/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Contract
import EDSL.Grading.AtomicLogical64.Domain

namespace EDSL.Grading.AtomicLogical64.Clients
open X86 OS.AddressSpace

/-- One actual OR followed by RET. -/
def bytes5 : List Byte := [0xf0, 0x48, 0x09, 0x37, 0xc3]

/-- Two actual ORs followed by RET. The second RMW remains observable. -/
def bytes9 : List Byte := [0xf0, 0x48, 0x09, 0x37, 0xf0, 0x48, 0x09, 0x37, 0xc3]

/-- Repeated union follows from independent natural-bit membership. No event
or execution is identified or discarded by this value-only theorem. -/
theorem union_twice {old mask middle final : Word}
    (first : Logical64.MathematicalResult .union old mask middle)
    (second : Logical64.MathematicalResult .union middle mask final) :
    Logical64.MathematicalResult .union old mask final := by
  intro index
  change Logical64.HasBit final index ↔ Logical64.HasBit old index ∨ Logical64.HasBit mask index
  rw [second index, first index]
  constructor
  · rintro ((initial | requested) | requested)
    · exact Or.inl initial
    · exact Or.inr requested
    · exact Or.inr requested
  · rintro (initial | requested)
    · exact Or.inl (Or.inl initial)
    · exact Or.inr requested

/-- ABI and nonarithmetic flags are consequences of actual instruction
semantics, independent of a fixture's assigned register or flag values. -/
theorem execution_frame {choices initial result}
    (actual : LockedLogical64.Executes choices initial result) :
    (∀ register, register ≠ .rsp → result.state.registers register = initial.registers register) ∧
      result.state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask := by
  induction actual with
  | ret actual =>
    have effect := (LockedLogical64.step_returned_sound actual).2.1
    exact ⟨effect.register_frame, congrArg (fun flags => flags &&& ~~~arithmeticFlagMask) effect.flags⟩
  | atomic64 actual _ induction =>
    have effect := (LockedLogical64.step_atomic64_sound actual).2.1
    exact ⟨fun register other => (induction.1 register other).trans (congrFun effect.registers register),
      induction.2.trans effect.nonarithmetic_flags⟩


/-- Decode a complete instruction selected from the frozen loaded extent. -/
theorem decode_window {descriptor shared cpu} (current : Current descriptor shared cpu)
    (instruction : LockedLogical64.Instruction) (offset : Nat)
    (pc : cpu.rip = descriptor.code + BitVec.ofNat 64 offset)
    (bound : offset + instruction.length ≤ descriptor.bytes.length)
    (matching : ∀ index byte, instruction.bytes[index]? = some byte →
      descriptor.bytes[offset + index]? = some byte) :
    LockedLogical64.decodeAt cpu = .ok instruction ∧ FetchWithin descriptor cpu := by
  have positive : 0 < instruction.length := by cases instruction <;> decide
  have start : descriptor.code.toNat + offset < 2^64 := by
    have := current.code.1
    omega
  have code := current.code.window offset bound start matching
  have decoded := LockedLogical64.decodeAt_of_code instruction (by rw [pc]; exact code)
  exact ⟨decoded, offset, instruction, pc, decoded, bound⟩

/-- Present current authority derives the real successful operation and its
machine step for every mask and AF choice. The successor remains current. -/
theorem advance_or {descriptor shared before} (current : Current descriptor shared before)
    (operand : before.registers .rdi = descriptor.target)
    (decoded : LockedLogical64.decodeAt before = .ok .orRdiRsi) (af : Bool) :
    ∃ evolved event after,
      OS.Atomics64.logicalDiscard shared descriptor.input.actor descriptor.input.handle
        (before.registers .rsi) = .ok (evolved, event) ∧
      Step descriptor shared evolved before af
        ⟨.atomic64 event.logical after, [.rmw8 descriptor.target]⟩ ∧
      Current descriptor evolved after ∧
      LockedLogical64.OrEffect before af event.logical after ∧
      loadQWord before.memory descriptor.target = .ok event.logical.event.before ∧
      loadQWord after.memory descriptor.target = .ok event.logical.event.after ∧
      Logical64.MathematicalResult .union event.logical.event.before (before.registers .rsi)
        event.logical.event.after := by
  obtain ⟨handle, cell, authorized, _, address⟩ := current.authority
  obtain ⟨changed, operation, actual⟩ := OS.Atomics64.logicalDiscard_step_enabled shared
    descriptor.input.actor descriptor.input.handle (before.registers .rsi) handle cell before af
    current.valid authorized current.coupled (operand.trans address.symm) rfl decoded
  have actual' : LockedLogical64.step af before = .ok ⟨.atomic64 changed.2.logical
      (LockedLogical64.afterOr before (toMemory changed.1.legacy.shared.resources.space)
        changed.2.logical.event.after af), [.rmw8 descriptor.target]⟩ := by
    simpa only [address] using actual
  have step : Step descriptor shared changed.1 before af _ := .atomic64 actual' operation
  have effect := (LockedLogical64.step_atomic64_sound actual').2.1
  have target : changed.2.logical.event.address = descriptor.target := effect.address.trans operand
  exact ⟨changed.1, changed.2, _, operation, step, step.current current, effect,
    by simpa only [target] using effect.transition.2.2.1,
    by simpa only [target] using effect.readback,
    OS.Atomics64.Routine.mathematical _ _ _ _ _ operation⟩

/-- RET uses the original current caller slot and leaves the current world
unchanged. Its actual encoding still requires separate complete coverage. -/
theorem return_step {descriptor shared before} (current : Current descriptor shared before)
    (original : before.registers .rsp = descriptor.stack)
    (decoded : LockedLogical64.decodeAt before = .ok .ret) (af : Bool) :
    Step descriptor shared shared before af
      ⟨.returned (OS.Atomics64.Routine.returned before descriptor.input.returnAddress),
        [.stack8 descriptor.stack]⟩ := by
  apply Step.ret (original := original)
  rw [LockedLogical64.step_eq_execute af decoded]
  simpa only [OS.Atomics64.Routine.returned, original] using
    LockedLogical64.execute_ret_context before descriptor.input.returnAddress af
      (by rw [original]; exact current.stack) current.returnCanonical

/-- Decode each exact window separately so its byte proof can be replayed as
a small client declaration, independently of the two-operation trace proof. -/
theorem decode9_first {descriptor shared cpu} (current : Current descriptor shared cpu)
    (bytes : descriptor.bytes = bytes9) (pc : cpu.rip = descriptor.code) :
    LockedLogical64.decodeAt cpu = .ok .orRdiRsi ∧ FetchWithin descriptor cpu := by
  apply decode_window current .orRdiRsi 0 (by simpa using pc)
  · rw [bytes]; decide
  · intro index byte present
    rw [bytes]
    match index with
    | 0 | 1 | 2 | 3 => simpa [bytes9, LockedLogical64.Instruction.bytes] using present
    | index + 4 => simp [LockedLogical64.Instruction.bytes] at present

theorem decode9_second {descriptor shared cpu} (current : Current descriptor shared cpu)
    (bytes : descriptor.bytes = bytes9) (pc : cpu.rip = descriptor.code + 4) :
    LockedLogical64.decodeAt cpu = .ok .orRdiRsi ∧ FetchWithin descriptor cpu := by
  apply decode_window current .orRdiRsi 4 pc
  · rw [bytes]; decide
  · intro index byte present
    rw [bytes]
    match index with
    | 0 | 1 | 2 | 3 => simpa [bytes9, LockedLogical64.Instruction.bytes] using present
    | index + 4 => simp [LockedLogical64.Instruction.bytes] at present

theorem decode9_return {descriptor shared cpu} (current : Current descriptor shared cpu)
    (bytes : descriptor.bytes = bytes9) (pc : cpu.rip = descriptor.code + 8) :
    LockedLogical64.decodeAt cpu = .ok .ret ∧ FetchWithin descriptor cpu := by
  apply decode_window current .ret 8 pc
  · rw [bytes]; decide
  · intro index byte present
    rw [bytes]
    cases index with
    | zero => simpa [bytes9, LockedLogical64.Instruction.bytes] using present
    | succ index => simp [LockedLogical64.Instruction.bytes] at present

/-- Both reads concern the same current RAM. Their equality supplies the
value chain; natural-bit membership then supplies union idempotence. -/
theorem current_union_chain {memory : Memory} {target old mask previous observed final : Word}
    (readback : loadQWord memory target = .ok previous)
    (currentRead : loadQWord memory target = .ok observed)
    (first : Logical64.MathematicalResult .union old mask previous)
    (second : Logical64.MathematicalResult .union observed mask final) :
    observed = previous ∧ Logical64.MathematicalResult .union old mask final := by
  have chain : observed = previous := Except.ok.inj (currentRead.symm.trans readback)
  exact ⟨chain, union_twice first (by rwa [chain] at second)⟩

theorem two_or_return_pc {initial middle final : X86.State} {af bf first second}
    (left : LockedLogical64.OrEffect initial af first middle)
    (right : LockedLogical64.OrEffect middle bf second final) :
    final.rip = initial.rip + 8 := by
  rw [right.rip, left.rip, BitVec.add_assoc]
  rfl

/-- The single-OR implementation has its actual two-instruction trace, in
addition to the task's count-free independent postcondition. -/
theorem witness5 {input shared initial}
    (pre : EDSL.AtomicLogical64.Pre bytes5 input shared initial) (choices : Choices) :
    ∃ evolved result event,
      CoveredExecution (frame bytes5 input shared initial) choices shared initial evolved result ∧
      Post (frame bytes5 input shared initial) shared initial evolved result.state ∧
      OS.Atomics64.logicalDiscard shared input.actor input.handle (initial.registers .rsi) =
        .ok (evolved, event) ∧
      result.instructions = 2 ∧ result.events = [event.logical] ∧
      result.accesses = [.rmw8 (initial.registers .rdi), .stack8 (initial.registers .rsp)] ∧
      loadQWord initial.memory (initial.registers .rdi) = .ok event.logical.event.before ∧
      loadQWord result.state.memory (initial.registers .rdi) = .ok event.logical.event.after ∧
      Logical64.MathematicalResult .union event.logical.event.before (initial.registers .rsi)
        event.logical.event.after := by
  let descriptor := frame bytes5 input shared initial
  have current : Current descriptor shared initial := Current.of_pre pre
  have decoded := LockedLogical64.decodeAt_of_code .orRdiRsi
    (OS.Atomics64.Routine.first_code pre.code)
  have firstFetch : FetchWithin descriptor initial :=
    ⟨0, .orRdiRsi, by simp [descriptor, frame], decoded, by change 4 ≤ 5; decide⟩
  obtain ⟨evolved, event, middle, operation, first, middleCurrent, effect, before, after, mathematical⟩ :=
    advance_or current rfl decoded (choices 0)
  have pc : middle.rip = descriptor.code + BitVec.ofNat 64 4 := effect.rip
  have ret := decode_window middleCurrent .ret 4 pc (by change 5 ≤ 5; decide) (by
    intro index byte present
    cases index with
    | zero => simpa [descriptor, frame, bytes5, LockedLogical64.Instruction.bytes] using present
    | succ index => simp [LockedLogical64.Instruction.bytes] at present)
  have returned := return_step middleCurrent (congrFun effect.registers .rsp) ret.1 ((choices.drop 1) 0)
  have covered : CoveredExecution descriptor choices shared initial evolved _ :=
    .atomic64 first firstFetch (.ret returned ret.2)
  have value : ∃ old result,
      loadQWord initial.memory descriptor.target = .ok old ∧
      loadQWord (OS.Atomics64.Routine.returned middle input.returnAddress).memory descriptor.target = .ok result ∧
      Logical64.MathematicalResult .union old (initial.registers .rsi) result :=
    ⟨event.logical.event.before, event.logical.event.after, before, after, mathematical⟩
  exact ⟨evolved, _, event, covered, Post.of_value covered current value, operation,
    rfl, rfl, rfl, before, after, mathematical⟩

/-- The second OR consumes the first operation's actual world and current RAM.
Both real events survive; only their final value is reduced by bit membership. -/
theorem witness9 {input shared initial}
    (pre : EDSL.AtomicLogical64.Pre bytes9 input shared initial) (choices : Choices) :
    ∃ middleShared evolved result first second,
      CoveredExecution (frame bytes9 input shared initial) choices shared initial evolved result ∧
      Post (frame bytes9 input shared initial) shared initial evolved result.state ∧
      OS.Atomics64.logicalDiscard shared input.actor input.handle (initial.registers .rsi) =
        .ok (middleShared, first) ∧
      OS.Atomics64.logicalDiscard middleShared input.actor input.handle (initial.registers .rsi) =
        .ok (evolved, second) ∧
      result.instructions = 3 ∧ result.events = [first.logical, second.logical] ∧
      result.accesses = [.rmw8 (initial.registers .rdi), .rmw8 (initial.registers .rdi),
        .stack8 (initial.registers .rsp)] ∧
      loadQWord initial.memory (initial.registers .rdi) = .ok first.logical.event.before ∧
      second.logical.event.before = first.logical.event.after ∧
      loadQWord result.state.memory (initial.registers .rdi) = .ok second.logical.event.after ∧
      Logical64.MathematicalResult .union first.logical.event.before (initial.registers .rsi)
        second.logical.event.after := by
  let descriptor := frame bytes9 input shared initial
  have current : Current descriptor shared initial := Current.of_pre pre
  have firstDecode := decode9_first current rfl rfl
  obtain ⟨middleShared, firstEvent, middle, firstOp, first, middleCurrent, firstEffect,
    before, firstRead, firstMath⟩ := advance_or current rfl firstDecode.1 (choices 0)
  have secondDecode := decode9_second middleCurrent rfl firstEffect.rip
  obtain ⟨evolved, secondEvent, last, secondOp, second, lastCurrent, secondEffect,
    secondRead, lastRead, secondMath⟩ := advance_or middleCurrent
      (congrFun firstEffect.registers .rdi) secondDecode.1 ((choices.drop 1) 0)
  have mask : middle.registers .rsi = initial.registers .rsi := congrFun firstEffect.registers .rsi
  have chainValue := current_union_chain firstRead secondRead firstMath
    (by rw [mask] at secondMath; exact secondMath)
  have ret := decode9_return lastCurrent rfl (two_or_return_pc firstEffect secondEffect)
  have stack : last.registers .rsp = descriptor.stack :=
    (congrFun secondEffect.registers .rsp).trans (congrFun firstEffect.registers .rsp)
  have returned := return_step lastCurrent stack ret.1 (((choices.drop 1).drop 1) 0)
  have covered : CoveredExecution descriptor choices shared initial evolved _ :=
    .atomic64 first firstDecode.2 (.atomic64 second secondDecode.2 (.ret returned ret.2))
  have value : ∃ old result,
      loadQWord initial.memory descriptor.target = .ok old ∧
      loadQWord (OS.Atomics64.Routine.returned last input.returnAddress).memory descriptor.target = .ok result ∧
      Logical64.MathematicalResult .union old (initial.registers .rsi) result :=
    ⟨firstEvent.logical.event.before, secondEvent.logical.event.after, before, lastRead, chainValue.2⟩
  exact ⟨middleShared, evolved, _, firstEvent, secondEvent, covered, Post.of_value covered current value,
    firstOp, by rw [mask] at secondOp; exact secondOp, rfl, rfl, rfl, before, chainValue.1, lastRead, chainValue.2⟩

theorem semantics5 : SemanticClaim bytes5 := by
  intro input shared initial pre choices
  obtain ⟨evolved, result, _, covered, post, _⟩ := witness5 pre choices
  exact ⟨evolved, result, covered, post⟩

theorem semantics9 : SemanticClaim bytes9 := by
  intro input shared initial pre choices
  obtain ⟨_, evolved, result, _, _, covered, post, _⟩ := witness9 pre choices
  exact ⟨evolved, result, covered, post⟩

/-- A useful admitted input is constructed by checked allocation, stores,
code installation, enrollment, handle issue and named read loans. -/
theorem nonvacuous {candidate : List Byte} (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) : Nonvacuous candidate := by
  obtain ⟨old, mask, shared, initial, pre, read, source, index, missing, requested⟩ :=
    Domain.useful_current candidate positive bound
  exact ⟨Domain.input, shared, initial, pre, old, read, index, missing, by rwa [source]⟩

theorem claim5 : Claim [0xf0, 0x48, 0x09, 0x37, 0xc3] :=
  ⟨semantics5, nonvacuous (by decide) (by decide)⟩

theorem claim9 : Claim [0xf0, 0x48, 0x09, 0x37, 0xf0, 0x48, 0x09, 0x37, 0xc3] :=
  ⟨semantics9, nonvacuous (by decide) (by decide)⟩

end EDSL.Grading.AtomicLogical64.Clients
