/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.AtomicSet64Grading
import EDSL.Audit

namespace EDSL.Tests.AtomicSet64Grading
open X86 X86.Sequential OS.AddressSpace Grading.AtomicSet64
open EDSL.Tests.Fixtures.AtomicSet64Grading

/-- Unsupported bytes have useful resource admission for every desired task,
but the real decoder faults before any successful execution. -/
theorem unsupported_rejected (desired : Logical64.Operation) :
    Nonvacuous desired [0xff] ∧ ¬Claim desired [0xff] := by
  refine ⟨nonvacuous_bytes desired _ (by decide) (by decide), ?_⟩
  intro claim
  obtain ⟨input, shared, initial, pre, _⟩ := claim.2
  have opcode := pre.code.2 0 0xff (by rfl)
  simp only [BitVec.add_zero] at opcode
  have failed : LockedSet64.step false initial = .error .unsupportedEncoding := by
    simp [LockedSet64.step, LockedSet64.decodeAt, opcode]
  have fault := claim.no_fault_prefix pre
    (LockedSet64.run_fault (fuel := 0) (choices := fun _ => false) failed)
  cases fault

/-- RET alone really returns using the admitted caller loan. Its actual empty
RMW trace contradicts the independently necessary changed membership. -/
theorem ret_only_rejected (desired : Logical64.Operation) :
    Nonvacuous desired [0xc3] ∧ ¬Claim desired [0xc3] := by
  refine ⟨nonvacuous_bytes desired _ (by decide) (by decide), ?_⟩
  intro claim
  obtain ⟨input, shared, initial, pre, useful⟩ := claim.2
  have decoded := LockedSet64.decodeAt_of_code .ret pre.code
  have actual : LockedSet64.step false initial = .ok
      ⟨.returned (OS.Atomics64.Routine.returned initial input.returnAddress),
        [.stack8 (initial.registers .rsp)]⟩ := by
    rw [LockedSet64.step_eq_execute false decoded]
    exact LockedSet64.execute_ret_context initial input.returnAddress false
      pre.stack pre.returnCanonical
  obtain ⟨_, returned⟩ := claim.all_results pre
    (LockedSet64.Executes.ret (choices := fun _ => false) actual)
  exact returned.event_required useful rfl

/-- The largest selected span is usefully admitted without assuming decoding,
fuel or any successful future instruction. -/
theorem maximum_span_nonvacuous (desired : Logical64.Operation) (byte : Byte) :
    Nonvacuous desired (List.replicate 4096 byte) :=
  nonvacuous_bytes desired _ (by rw [List.length_replicate]; decide)
    (by rw [List.length_replicate]; exact Nat.le_refl _)

/-- Two real same-mask XOR operations restore all bits. The result identity is
independent bit membership, not a copied executor calculation. -/
theorem xor_twice_identity (old mask : Word) :
    Logical64.applyUpdates old [(.bxor, mask), (.bxor, mask)] = old := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index inside
  exact Bool.coe_iff_coe.mp
    (by simpa only [Logical64.applyUpdates, LogicalOp.eval, Logical64.HasBit, BitVec.testBit_toNat] using
      xor_twice_bits old mask ⟨index, inside⟩)

/-- A terminating two-XOR program cannot be offered as symmetric difference:
on a useful admitted input it restores entry RAM instead of changing the bit. -/
theorem double_xor_rejected :
    Nonvacuous .symmetricDifference bytesXorTwice ∧
      ¬Claim .symmetricDifference bytesXorTwice := by
  refine ⟨nonvacuous_bytes _ _ (by decide) (by decide), ?_⟩
  intro claim
  obtain ⟨input, shared, initial, pre, old, read, useful⟩ := claim.2
  have current : Current (frame bytesXorTwice input shared initial) shared initial := Current.of_pre pre
  obtain ⟨evolved, result, observed, covered, observedRead, finalRead, _, _⟩ :=
    sequence [.bxor, .bxor] 0 current (by simp [bytesXorTwice, frame, Grading.AtomicLogical64.frame]) (by simp [frame, Grading.AtomicLogical64.frame])
      (Nat.zero_le _) rfl rfl (fun _ => false)
  have observedEq : observed = old := Except.ok.inj (observedRead.symm.trans read)
  simp only [List.map_cons, List.map_nil] at finalRead
  rw [observedEq, xor_twice_identity] at finalRead
  obtain ⟨_, returned⟩ := claim.all_results pre covered.machine
  obtain ⟨entry, final, entryRead, outputRead, mathematical⟩ := returned.post.value
  have entryEq : entry = old := Except.ok.inj (entryRead.symm.trans read)
  have finalEq : final = old := Except.ok.inj (outputRead.symm.trans finalRead)
  subst entry
  exact useful.changes mathematical finalEq

/-- The mixed implementation has three actual tags, four retired instructions,
full current endpoint RAM and its independent all-word union postcondition.
None of its cancelling events is omitted or replaced by a single union event. -/
theorem mixed_actual (old mask : Word) (choices : Grading.AtomicSet64.Choices) :
    ∃ evolved result,
      LockedSet64.run choices 4 (EDSL.AtomicSet64.Domain.cpu bytesMixedUnion old mask) = .ok result ∧
      result.events.map LogicalEvent64.op = [.bxor, .bxor, .bor] ∧
      result.events.length = 3 ∧ result.instructions = 4 ∧
      Current (frame bytesMixedUnion EDSL.AtomicSet64.Domain.input
        (EDSL.AtomicSet64.Domain.World bytesMixedUnion old)
        (EDSL.AtomicSet64.Domain.cpu bytesMixedUnion old mask)) evolved result.state ∧
      loadQWord result.state.memory 65536 = .ok (old ||| mask) := by
  have pre := EDSL.AtomicSet64.Domain.admitted_bytes bytesMixedUnion (by decide) (by decide) old mask
  have current := Current.of_pre pre
  obtain ⟨evolved, result, observed, covered, observedRead, finalRead, count, tags⟩ :=
    sequence [.bxor, .bxor, .bor] 0 current (by simp [bytesMixedUnion, frame, Grading.AtomicLogical64.frame]) (by simp [frame, Grading.AtomicLogical64.frame])
      (Nat.zero_le _) rfl rfl choices
  have read := Grading.AtomicLogical64.Domain.old_read bytesMixedUnion (by decide) old mask
  have observedEq : observed = old := Except.ok.inj (observedRead.symm.trans read)
  have answer := Logical64.MathematicalResult.unique
    (mixed_union_math old mask) (Logical64.eval_mathematical .union old mask)
  have retired : result.instructions = 4 := count
  have length := congrArg List.length tags
  rw [List.length_map] at length
  refine ⟨evolved, result, LockedSet64.run_complete covered.machine (by rw [retired]; exact Nat.le_refl _),
    tags, length, retired, covered.current current, ?_⟩
  change loadQWord result.state.memory 65536 = .ok
    (Logical64.applyUpdates observed [(.bxor, mask), (.bxor, mask), (.bor, mask)]) at finalRead
  rw [observedEq, answer] at finalRead
  exact finalRead

/-- Every mixed event originates at its real current coupled CPU/OS prefix,
including the second XOR's current read. -/
theorem mixed_second_current (old mask : Word) (choices : Grading.AtomicSet64.Choices) :
    ∃ (evolved : Shared) (result : Grading.AtomicSet64.Result) (event : LogicalEvent64)
      (middle : Shared) (before after : X86.State) (accesses : List LockedSet64.Access),
      LockedSet64.run choices 4 (EDSL.AtomicSet64.Domain.cpu bytesMixedUnion old mask) = .ok result ∧
      result.events[1]? = some event ∧ event.op = .bxor ∧
      Current (frame bytesMixedUnion EDSL.AtomicSet64.Domain.input
        (EDSL.AtomicSet64.Domain.World bytesMixedUnion old)
        (EDSL.AtomicSet64.Domain.cpu bytesMixedUnion old mask)) middle before ∧
      LockedSet64.step (choices 1) before = .ok ⟨.atomic64 event after, accesses⟩ ∧
      loadQWord (toMemory middle.legacy.shared.resources.space) event.event.address = .ok event.event.before ∧
      result.state.memory = toMemory evolved.legacy.shared.resources.space := by
  have pre := EDSL.AtomicSet64.Domain.admitted_bytes bytesMixedUnion (by decide) (by decide) old mask
  have current := Current.of_pre pre
  obtain ⟨evolved, result, _, covered, _, _, count, tags⟩ :=
    sequence [.bxor, .bxor, .bor] 0 current (by simp [bytesMixedUnion, frame, Grading.AtomicLogical64.frame]) (by simp [frame, Grading.AtomicLogical64.frame])
      (Nat.zero_le _) rfl rfl choices
  have length : result.events.length = 3 := by
    have := congrArg List.length tags
    simpa only [List.length_map, List.length_cons, List.length_nil] using this
  let event := result.events[1]'(by omega)
  have present : result.events[1]? = some event :=
    List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩
  have actualTag : event.op = .bxor := by
    have := congrArg (fun list : List LogicalOp => list[1]?) tags
    have mapped : some event.op = some LogicalOp.bxor := by
      simpa only [List.getElem?_map, present, Option.map_some,
        List.getElem?_cons_succ, List.getElem?_cons_zero] using this
    exact Option.some.inj mapped
  obtain ⟨before, after, _, _, accesses, path, actual, _, op, _, effect⟩ :=
    covered.machine.event_origin present
  obtain ⟨middle, prefixCurrent, _⟩ := covered.prefix current path (by rw [count]; decide)
  exact ⟨evolved, result, event, middle, before, after, accesses,
    LockedSet64.run_complete covered.machine (by rw [count]; decide), present, actualTag,
    prefixCurrent, actual, by rw [←prefixCurrent.coupled]; exact effect.transition.2.2.1,
    (covered.current current).coupled⟩

/-- A physical decoder can see adjacent complete instruction bytes even when
the selected artifact cuts that instruction short. Covered execution rejects
the short selection separately from decoding or runner success. -/
theorem truncated_first (choices : Grading.AtomicSet64.Choices) :
    ∃ shared initial evolved result,
      EDSL.AtomicSet64.Pre bytesAnd EDSL.AtomicSet64.Domain.input shared initial ∧
      LockedSet64.run choices 2 initial = .ok result ∧
      ¬FetchWithin (frame [0xf0, 0x48, 0x21] EDSL.AtomicSet64.Domain.input shared initial) initial ∧
      ¬CoveredExecution (frame [0xf0, 0x48, 0x21] EDSL.AtomicSet64.Domain.input shared initial)
        choices shared initial evolved result := by
  let shared := EDSL.AtomicSet64.Domain.World bytesAnd 0x8000000000000000
  let initial := EDSL.AtomicSet64.Domain.cpu bytesAnd 0x8000000000000000 0
  have pre := EDSL.AtomicSet64.Domain.admitted_bytes bytesAnd (by decide) (by decide)
    0x8000000000000000 0
  obtain ⟨evolved, result, ran, _⟩ := claimAnd.run pre choices
  have retired := EDSL.AtomicSet64.exact2 .intersection pre (LockedSet64.run_sound ran)
  have decoded := (decode_head (Current.of_pre pre)
    (ops := [.band]) (offset := 0) (by simp [bytesAnd, frame, Grading.AtomicLogical64.frame]) (by simp [frame, Grading.AtomicLogical64.frame]) (Nat.zero_le _)).1
  have noFetch : ¬FetchWithin
      (frame [0xf0, 0x48, 0x21] EDSL.AtomicSet64.Domain.input shared initial) initial := by
    intro fetch
    obtain ⟨offset, _, bound⟩ := fetch.decoded decoded
    change offset + 4 ≤ 3 at bound
    omega
  exact ⟨shared, initial, evolved, result, pre, by rwa [retired] at ran,
    noFetch, fun impossible => noFetch impossible.fetchWithin⟩

/-- Whole-instruction coverage applies at later prefixes too. The actual
second XOR executes from adjacent bytes but its last byte lies outside a
seven-byte selected extent. -/
theorem truncated_second (choices : Grading.AtomicSet64.Choices) :
    ∃ shared initial evolved result before after label accesses,
      EDSL.AtomicSet64.Pre bytesMixedUnion EDSL.AtomicSet64.Domain.input shared initial ∧
      LockedSet64.run choices 4 initial = .ok result ∧
      Current (frame bytesMixedUnion EDSL.AtomicSet64.Domain.input shared initial) evolved result.state ∧
      LockedSet64.step (choices 1) before = .ok ⟨.atomic64 label after, accesses⟩ ∧
      before.rip = initial.rip + 4 ∧
      ¬FetchWithin (frame [0xf0, 0x48, 0x31, 0x37, 0xf0, 0x48, 0x31]
        EDSL.AtomicSet64.Domain.input shared initial) before := by
  let shared := EDSL.AtomicSet64.Domain.World bytesMixedUnion 0
  let initial := EDSL.AtomicSet64.Domain.cpu bytesMixedUnion 0 0x8000000000000000
  have pre := EDSL.AtomicSet64.Domain.admitted_bytes bytesMixedUnion (by decide) (by decide)
    0 0x8000000000000000
  have current := Current.of_pre pre
  obtain ⟨evolved, result, _, covered, _, _, count, tags⟩ :=
    sequence [.bxor, .bxor, .bor] 0 current (by simp [bytesMixedUnion, frame, Grading.AtomicLogical64.frame]) (by simp [frame, Grading.AtomicLogical64.frame])
      (Nat.zero_le _) rfl rfl choices
  have length : result.events.length = 3 := by
    have := congrArg List.length tags
    simpa only [List.length_map, List.length_cons, List.length_nil] using this
  let event := result.events[1]'(by omega)
  have present : result.events[1]? = some event :=
    List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩
  obtain ⟨before, after, _, _, accesses, path, actual, _, _⟩ :=
    covered.machine.event_origin present
  have pc : before.rip = initial.rip + 4 := by
    cases path with
    | atomic64 first tail =>
      cases tail
      exact (LockedSet64.step_atomic64_sound first).choose_spec.2.1.rip
  refine ⟨shared, initial, evolved, result, before, after, event, accesses,
    pre, LockedSet64.run_complete covered.machine (by rw [count]; decide),
    covered.current current, actual, pc, ?_⟩
  intro fetch
  obtain ⟨op, decoded, _, _⟩ := LockedSet64.step_atomic64_sound actual
  obtain ⟨offset, atOffset, bound⟩ := fetch.decoded decoded
  change offset + 4 ≤ 7 at bound
  have small : offset < 2^64 := by omega
  have total : 4096 + offset < 2^64 := by omega
  have natural := congrArg BitVec.toNat atOffset
  rw [pc] at natural
  change 4100 = (4096 + offset % 2^64) % 2^64 at natural
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total] at natural
  omega

end EDSL.Tests.AtomicSet64Grading

#audit_edsl
