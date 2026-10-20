/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Accounting
import EDSL.Logical64.SetHistory

namespace EDSL.Tests.Fixtures.AtomicSet64Grading
open X86 X86.Sequential OS.AddressSpace EDSL.Grading.AtomicSet64

/-- Client encoding, outside the trusted controller foundation. -/
def encode : List LogicalOp → List Byte
  | [] => [0xc3]
  | op :: rest => (LockedSet64.Instruction.logicalRdiRsi op).bytes ++ encode rest

@[simp] theorem encode_length (ops : List LogicalOp) : (encode ops).length = 4 * ops.length + 1 := by
  induction ops with
  | nil => rfl
  | cons op rest induction => simp [encode, LockedSet64.Instruction.bytes, induction]; omega

/-- Decode a complete current window inside the original selected extent. -/
theorem decode_window {descriptor shared cpu} (current : Current descriptor shared cpu)
    (instruction : LockedSet64.Instruction) (offset : Nat)
    (pc : cpu.rip = descriptor.code + BitVec.ofNat 64 offset)
    (bound : offset + instruction.length ≤ descriptor.bytes.length)
    (matching : ∀ index byte, instruction.bytes[index]? = some byte →
      descriptor.bytes[offset + index]? = some byte) :
    LockedSet64.decodeAt cpu = .ok instruction ∧ FetchWithin descriptor cpu := by
  have positive : 0 < instruction.length := by
    cases instruction <;> simp [LockedSet64.Instruction.length, LockedSet64.Instruction.bytes]
  have start : descriptor.code.toNat + offset < 2^64 := by
    have := current.code.1
    omega
  have code := current.code.window offset bound start matching
  have decoded := LockedSet64.decodeAt_of_code instruction (by rw [pc]; exact code)
  exact ⟨decoded, offset, instruction, pc, decoded, bound⟩

theorem decode_head {descriptor shared cpu ops offset} (current : Current descriptor shared cpu)
    (remaining : descriptor.bytes.drop offset = encode ops)
    (pc : cpu.rip = descriptor.code + BitVec.ofNat 64 offset)
    (offsetBound : offset ≤ descriptor.bytes.length) :
    LockedSet64.decodeAt cpu = .ok (match ops with | [] => .ret | op :: _ => .logicalRdiRsi op) ∧
      FetchWithin descriptor cpu := by
  have length := congrArg List.length remaining
  rw [List.length_drop, encode_length] at length
  cases ops with
  | nil =>
    apply decode_window current .ret offset pc (by change offset + 1 ≤ _; omega)
    intro index byte present
    rw [←List.getElem?_drop, remaining]
    exact present
  | cons op rest =>
    apply decode_window current (.logicalRdiRsi op) offset pc
      (by change offset + 4 ≤ _; simp only [List.length_cons] at length; omega)
    intro index byte present
    rw [←List.getElem?_drop, remaining]
    match index with
    | 0 | 1 | 2 | 3 => simpa [encode, LockedSet64.Instruction.bytes] using present
    | index + 4 => simp [LockedSet64.Instruction.bytes] at present

/-- Current authority derives the actual operation selected by decoding. -/
theorem advance {descriptor shared before} (op : LogicalOp)
    (current : Current descriptor shared before)
    (operand : before.registers .rdi = descriptor.target)
    (decoded : LockedSet64.decodeAt before = .ok (.logicalRdiRsi op)) (af : Bool) :
    ∃ evolved event after,
      OS.Atomics64.logicalUpdate op shared descriptor.input.actor descriptor.input.handle
        (before.registers .rsi) = .ok (evolved, event) ∧
      Step descriptor shared evolved before af ⟨.atomic64 event.logical after, [.rmw8 descriptor.target]⟩ ∧
      Current descriptor evolved after ∧
      LockedSet64.LogicalEffect op before af event.logical after ∧
      loadQWord before.memory descriptor.target = .ok event.logical.event.before ∧
      loadQWord after.memory descriptor.target = .ok event.logical.event.after ∧
      event.logical.event.after = op.eval event.logical.event.before (before.registers .rsi) := by
  obtain ⟨handle, cell, authorized, _, address⟩ := current.authority
  obtain ⟨changed, operation, actual⟩ := OS.Atomics64.logicalUpdate_step_enabled op shared
    descriptor.input.actor descriptor.input.handle (before.registers .rsi) handle cell before af
    current.valid authorized current.coupled (operand.trans address.symm) rfl decoded
  have actual' : LockedSet64.step af before = .ok ⟨.atomic64 changed.2.logical
      (LockedSet64.afterLogical before (toMemory changed.1.legacy.shared.resources.space)
        changed.2.logical.event.after af), [.rmw8 descriptor.target]⟩ := by
    simpa only [address] using actual
  have step : Step descriptor shared changed.1 before af _ := .atomic64 actual' operation
  obtain ⟨actualOp, actualDecode, effect, _⟩ := LockedSet64.step_atomic64_sound actual'
  have sameOp : actualOp = op := by
    have := Except.ok.inj (actualDecode.symm.trans decoded)
    cases this
    rfl
  subst actualOp
  have target : changed.2.logical.event.address = descriptor.target := effect.address.trans operand
  exact ⟨changed.1, changed.2, _, operation, step, step.current current, effect,
    by simpa only [target] using effect.transition.2.2.1,
    by simpa only [target] using effect.readback,
    (OS.Atomics64.logicalUpdate_sound _ _ _ _ _ _ operation).2.2.2.1⟩

theorem return_step {descriptor shared before} (current : Current descriptor shared before)
    (original : before.registers .rsp = descriptor.stack)
    (decoded : LockedSet64.decodeAt before = .ok .ret) (af : Bool) :
    Step descriptor shared shared before af
      ⟨.returned (OS.Atomics64.Routine.returned before descriptor.input.returnAddress),
        [.stack8 descriptor.stack]⟩ := by
  apply Step.ret (original := original)
  rw [LockedSet64.step_eq_execute af decoded]
  simpa only [OS.Atomics64.Routine.returned, original] using
    LockedSet64.execute_ret_context before descriptor.input.returnAddress af
      (by rw [original]; exact current.stack) current.returnCanonical

/-- All actual updates remain in the trace. The fold is derived behavior only;
client claims below separately prove the desired natural-bit membership. -/
theorem sequence {descriptor shared before} (ops : List LogicalOp) (offset : Nat)
    (current : Current descriptor shared before)
    (remaining : descriptor.bytes.drop offset = encode ops)
    (pc : before.rip = descriptor.code + BitVec.ofNat 64 offset)
    (offsetBound : offset ≤ descriptor.bytes.length)
    (operand : before.registers .rdi = descriptor.target)
    (stack : before.registers .rsp = descriptor.stack)
    (choices : Grading.AtomicSet64.Choices) :
    ∃ evolved result old,
      CoveredExecution descriptor choices shared before evolved result ∧
      loadQWord before.memory descriptor.target = .ok old ∧
      loadQWord result.state.memory descriptor.target =
        .ok (Logical64.applyUpdates old (ops.map (fun op => (op, before.registers .rsi)))) ∧
      result.instructions = ops.length + 1 ∧
      result.events.map LogicalEvent64.op = ops := by
  induction ops generalizing shared before offset choices with
  | nil =>
    have decoded := decode_head current remaining pc offsetBound
    have ret := return_step current stack decoded.1 (choices 0)
    obtain ⟨handle, cell, authorized, _, address⟩ := current.authority
    have allowed := (OS.Atomics64.authorize_ok _ _ _ _ authorized).2.2.2.1.writable
    have allowed' : canStoreQWord before.memory descriptor.target = true := by
      rw [current.coupled, ←address]
      exact allowed
    obtain ⟨old, read⟩ := loadQWord_of_canStoreQWord _ _ allowed'
    exact ⟨shared, _, old, .ret ret decoded.2, read, read, rfl, rfl⟩
  | cons op ops induction =>
    have decoded := decode_head current remaining pc offsetBound
    obtain ⟨middleShared, event, middle, operation, first, middleCurrent, effect,
      oldRead, middleRead, value⟩ := advance op current operand decoded.1 (choices 0)
    have nextRemaining : descriptor.bytes.drop (offset + 4) = encode ops := by
      rw [←List.drop_drop, remaining]
      simp [encode, LockedSet64.Instruction.bytes]
    have nextPC : middle.rip = descriptor.code + BitVec.ofNat 64 (offset + 4) := by
      rw [effect.rip, pc, BitVec.add_assoc]
      rw [BitVec.ofNat_add]
      rfl
    have nextBound : offset + 4 ≤ descriptor.bytes.length := by
      have length := congrArg List.length remaining
      simp [encode, LockedSet64.Instruction.bytes] at length
      omega
    obtain ⟨evolved, result, observed, covered, observedRead, finalRead, count, tags⟩ :=
      induction (offset + 4) middleCurrent nextRemaining nextPC nextBound
        ((congrFun effect.registers .rdi).trans operand)
        ((congrFun effect.registers .rsp).trans stack) (choices.drop 1)
    have chain : observed = event.logical.event.after := Except.ok.inj (observedRead.symm.trans middleRead)
    have mask := congrFun effect.registers .rsi
    rw [chain, value, mask] at finalRead
    have tag : event.logical.op = op := effect.op
    exact ⟨evolved, result.prepend 1 [event.logical] [.rmw8 descriptor.target],
      event.logical.event.before, .atomic64 first decoded.2 covered, oldRead, finalRead,
      by simp [LockedSet64.Result.prepend, count]; omega,
      by simp [LockedSet64.Result.prepend, tags, tag]⟩

/-- A client supplies a mathematical proof about all old/mask pairs. The
execution strategy itself accepts any actual operation list, including mixed. -/
theorem semantic_sequence (desired : Logical64.Operation) (ops : List LogicalOp)
    (mathematical : ∀ old mask, Logical64.MathematicalResult desired old mask
      (Logical64.applyUpdates old (ops.map (fun op => (op, mask))))) :
    SemanticClaim desired (encode ops) := by
  intro input shared initial pre choices
  have current : Current (frame (encode ops) input shared initial) shared initial := Current.of_pre pre
  obtain ⟨evolved, result, old, covered, oldRead, finalRead, _, _⟩ :=
    sequence ops 0 current (by rfl) (by simp [frame, Grading.AtomicLogical64.frame])
      (Nat.zero_le _) rfl rfl choices
  exact ⟨evolved, result, covered,
    Post.of_value covered current ⟨old, _, oldRead, finalRead, mathematical old (initial.registers .rsi)⟩⟩

/-- These client algebra lemmas inspect independent natural-bit membership.
They reduce no real event or covered transition. -/
theorem one_math (desired : Logical64.Operation) (old mask : Word) :
    Logical64.MathematicalResult desired old mask
      (Logical64.applyUpdates old [(desired.toLogicalOp, mask)]) :=
  Logical64.eval_mathematical desired old mask

theorem and_twice_math (old mask : Word) :
    Logical64.MathematicalResult .intersection old mask
      (Logical64.applyUpdates old [(.band, mask), (.band, mask)]) := by
  intro index
  change Logical64.HasBit ((old &&& mask) &&& mask) index ↔ _
  rw [Logical64.HasBit.and_iff, Logical64.HasBit.and_iff]
  exact ⟨fun left => left.1, fun left => ⟨left, left.2⟩⟩

theorem or_twice_math (old mask : Word) :
    Logical64.MathematicalResult .union old mask
      (Logical64.applyUpdates old [(.bor, mask), (.bor, mask)]) := by
  intro index
  change Logical64.HasBit ((old ||| mask) ||| mask) index ↔ _
  rw [Logical64.HasBit.or_iff, Logical64.HasBit.or_iff]
  exact ⟨fun left => left.elim id Or.inr, fun left => Or.inl left⟩

theorem xor_twice_bits (old mask : Word) (index : Fin 64) :
    Logical64.HasBit ((old ^^^ mask) ^^^ mask) index ↔ Logical64.HasBit old index := by
  rw [Logical64.HasBit.xor_iff, Logical64.HasBit.xor_iff]
  classical
  by_cases left : Logical64.HasBit old index <;> by_cases right : Logical64.HasBit mask index <;>
    simp [left, right]

theorem xor_thrice_math (old mask : Word) :
    Logical64.MathematicalResult .symmetricDifference old mask
      (Logical64.applyUpdates old [(.bxor, mask), (.bxor, mask), (.bxor, mask)]) := by
  intro index
  change Logical64.HasBit (((old ^^^ mask) ^^^ mask) ^^^ mask) index ↔ _
  rw [Logical64.HasBit.xor_iff, xor_twice_bits]

/-- Two real XORs cancel membership, then the real OR supplies union. The
execution retains all three operations and their current-before values. -/
theorem mixed_union_math (old mask : Word) :
    Logical64.MathematicalResult .union old mask
      (Logical64.applyUpdates old [(.bxor, mask), (.bxor, mask), (.bor, mask)]) := by
  intro index
  change Logical64.HasBit (((old ^^^ mask) ^^^ mask) ||| mask) index ↔ _
  rw [Logical64.HasBit.or_iff, xor_twice_bits]

def bytesAnd : List Byte := encode [.band]
def bytesOr : List Byte := encode [.bor]
def bytesXor : List Byte := encode [.bxor]
def bytesAndTwice : List Byte := encode [.band, .band]
def bytesOrTwice : List Byte := encode [.bor, .bor]
def bytesXorTwice : List Byte := encode [.bxor, .bxor]
def bytesXorThrice : List Byte := encode [.bxor, .bxor, .bxor]
def bytesMixedUnion : List Byte := encode [.bxor, .bxor, .bor]

theorem claim_one (desired : Logical64.Operation) : Claim desired (encode [desired.toLogicalOp]) :=
  ⟨semantic_sequence desired [desired.toLogicalOp] (one_math desired),
    nonvacuous_bytes desired _ (by simp) (by simp)⟩

theorem claimAnd : Claim .intersection bytesAnd := claim_one .intersection
theorem claimOr : Claim .union bytesOr := claim_one .union
theorem claimXor : Claim .symmetricDifference bytesXor := claim_one .symmetricDifference

theorem claimAndTwice : Claim .intersection bytesAndTwice :=
  ⟨semantic_sequence .intersection [.band, .band] and_twice_math,
    nonvacuous_bytes _ _ (by decide) (by decide)⟩

theorem claimOrTwice : Claim .union bytesOrTwice :=
  ⟨semantic_sequence .union [.bor, .bor] or_twice_math,
    nonvacuous_bytes _ _ (by decide) (by decide)⟩

theorem claimXorThrice : Claim .symmetricDifference bytesXorThrice :=
  ⟨semantic_sequence .symmetricDifference [.bxor, .bxor, .bxor] xor_thrice_math,
    nonvacuous_bytes _ _ (by decide) (by decide)⟩

theorem claimMixedUnion : Claim .union bytesMixedUnion :=
  ⟨semantic_sequence .union [.bxor, .bxor, .bor] mixed_union_math,
    nonvacuous_bytes _ _ (by decide) (by decide)⟩

end EDSL.Tests.Fixtures.AtomicSet64Grading
