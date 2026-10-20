/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Machine
import EDSL.X86.Sequential.Return

namespace EDSL.X86.CallReturn

/-- Successful checked stores identify the actual complete replacement RAM,
readback, permissions, and every byte outside the eight-byte footprint. -/
theorem storeQWord_context {before after : Memory} {address value : Word}
    (stored : storeQWord before address value = .ok after) :
    canStoreQWord before address = true ∧
    after = writeQWordUnchecked before address value ∧
    readWord after address = .ok value ∧
    after.executable = before.executable ∧ after.writable = before.writable ∧
    ∀ query, 8 ≤ (query - address).toNat → after.read query = before.read query := by
  cases allowed : canStoreQWord before address with
  | false => simp [storeQWord, allowed] at stored
  | true =>
    have same : after = writeQWordUnchecked before address value := by
      simpa [storeQWord, allowed, eq_comm] using stored
    subst after
    exact ⟨rfl, rfl, readWord_of_loadQWord _ _ _ (qword_store_sound _ _ _ allowed).2,
      rfl, rfl, fun query outside => writeQWord_frame _ _ query _ outside⟩

theorem execute_call_context {before after : State} {displacement : BitVec 32} {af : Bool}
    {reads : List Read}
    (actual : execute before (.callRelative32 displacement) af = .ok ⟨.next after, reads⟩) :
    canonical (callTarget before displacement) = true ∧
    storeQWord before.memory (stackDestination before) (returnAddress before) = .ok after.memory ∧
    after.rip = callTarget before displacement ∧
    after.registers .rsp = stackDestination before ∧ after.flags = before.flags ∧ reads = [] ∧
    (∀ register, register ≠ .rsp → after.registers register = before.registers register) ∧
    readWord after.memory (stackDestination before) = .ok (returnAddress before) ∧
    after.memory.executable = before.memory.executable ∧
    after.memory.writable = before.memory.writable ∧
    ∀ query, 8 ≤ (query - stackDestination before).toNat →
      after.memory.read query = before.memory.read query := by
  obtain ⟨canon, memory, stored, same⟩ := execute_call_success_iff.mp actual
  cases same
  have facts := storeQWord_context stored
  exact ⟨canon, stored, rfl, by simp [callState, State.writeRegister], rfl, rfl,
    by intro r different; simp [callState, State.writeRegister, different],
    facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.1, facts.2.2.2.2.2⟩

theorem execute_push_context {before after : State} {source : Register} {prefixed af : Bool}
    {reads : List Read}
    (actual : execute before (.push64 source prefixed) af = .ok ⟨.next after, reads⟩) :
    storeQWord before.memory (stackDestination before) (before.registers source) = .ok after.memory ∧
    after.rip = before.rip + BitVec.ofNat 64 (stackLength prefixed) ∧
    after.registers .rsp = stackDestination before ∧ after.flags = before.flags ∧ reads = [] ∧
    (∀ register, register ≠ .rsp → after.registers register = before.registers register) ∧
    readWord after.memory (stackDestination before) = .ok (before.registers source) ∧
    after.memory.executable = before.memory.executable ∧
    after.memory.writable = before.memory.writable ∧
    ∀ query, 8 ≤ (query - stackDestination before).toNat →
      after.memory.read query = before.memory.read query := by
  obtain ⟨memory, stored, same⟩ := execute_push_success_iff.mp actual
  cases same
  have facts := storeQWord_context stored
  exact ⟨stored, rfl, by simp [pushState, State.writeRegister], rfl, rfl,
    by intro r different; simp [pushState, State.writeRegister, different],
    facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.1, facts.2.2.2.2.2⟩

theorem execute_pop_context {before after : State} {destination : Register} {prefixed af : Bool}
    {reads : List Read}
    (actual : execute before (.pop64 destination prefixed) af = .ok ⟨.next after, reads⟩) :
    readWord before.memory (before.registers .rsp) = .ok (after.registers destination) ∧
    after.rip = before.rip + BitVec.ofNat 64 (stackLength prefixed) ∧
    after.registers .rsp = (if destination = .rsp then after.registers destination else before.registers .rsp + 8) ∧
    after.flags = before.flags ∧ after.memory = before.memory ∧
    reads = [⟨.stack, before.registers .rsp, 8⟩] ∧
    ∀ register, register ≠ destination → register ≠ .rsp →
      after.registers register = before.registers register := by
  obtain ⟨value, loaded, same⟩ := execute_pop_success_iff.mp actual
  cases same
  refine ⟨?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simpa [popState, State.writeRegister] using loaded
  · by_cases equal : destination = .rsp
    · simp [popState, State.writeRegister, equal]
    · simp [popState, State.writeRegister, equal, Ne.symm equal]
  · intro r other notSP
    simp [popState, State.writeRegister, other, notSP]

theorem execute_lea_context {before after : State} {destination : Register} {address : Address}
    {displacement : Byte} {af : Bool} {reads : List Read}
    (actual : execute before (.leaDisp8 destination address displacement) af = .ok ⟨.next after, reads⟩) :
    after.registers destination = address.eval before + displacement.signExtend 64 ∧
    after.rip = before.rip + BitVec.ofNat 64 (Instruction.leaDisp8 destination address displacement).length ∧
    after.flags = before.flags ∧ after.memory = before.memory ∧ reads = [] ∧
    ∀ register, register ≠ destination → after.registers register = before.registers register := by
  have same : (⟨.next (leaState before destination address displacement), []⟩ : Observation) =
      ⟨.next after, reads⟩ := Except.ok.inj actual
  cases same
  exact ⟨by simp [leaState, State.writeRegister], rfl, rfl, rfl, rfl,
    by intro r other; simp [leaState, State.writeRegister, other]⟩

theorem execute_extension_next {before : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (extension : instruction.isExtension = true)
    (actual : execute before instruction af = .ok observation) :
    ∃ after, observation.result = .next after := by
  cases instruction with
  | sequential old => cases extension
  | callRelative32 d =>
    obtain ⟨_, memory, _, same⟩ := execute_call_success_iff.mp actual
    cases same
    exact ⟨_, rfl⟩
  | push64 source p =>
    obtain ⟨memory, _, same⟩ := execute_push_success_iff.mp actual
    cases same
    exact ⟨_, rfl⟩
  | pop64 destination p =>
    obtain ⟨value, _, same⟩ := execute_pop_success_iff.mp actual
    cases same
    exact ⟨_, rfl⟩
  | leaDisp8 destination a d =>
    cases actual
    exact ⟨_, rfl⟩

theorem execute_reads {before : State} {instruction : Instruction} {af : Bool} {observation : Observation}
    (actual : execute before instruction af = .ok observation) :
    observation.reads = instruction.operandReads before := by
  cases instruction with
  | sequential old => exact Sequential.execute_reads actual
  | callRelative32 d => obtain ⟨_, _, _, same⟩ := execute_call_success_iff.mp actual; cases same; rfl
  | push64 r p => obtain ⟨_, _, same⟩ := execute_push_success_iff.mp actual; cases same; rfl
  | pop64 r p => obtain ⟨_, _, same⟩ := execute_pop_success_iff.mp actual; cases same; rfl
  | leaDisp8 r a d => cases actual; rfl

theorem execute_reads_succeed {before : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (actual : execute before instruction af = .ok observation)
    {read : Read} (member : read ∈ observation.reads) : Sequential.OperandReadSucceeds before read := by
  cases instruction with
  | sequential old => exact Sequential.execute_reads_succeed actual read member
  | pop64 r p =>
    obtain ⟨value, loaded, same⟩ := execute_pop_success_iff.mp actual
    cases same
    simp only [List.mem_singleton] at member
    subst read
    exact ⟨rfl, value, loaded⟩
  | callRelative32 d | push64 r p | leaDisp8 r a d =>
    rw [execute_reads actual] at member
    cases member

theorem rawStep_read_origin {before : State} {af : Bool} {observation : Observation}
    (actual : rawStep af before = .ok observation) :
    ∃ instruction, decodeAt before = .ok instruction ∧
      execute before instruction af = .ok observation ∧
      observation.reads = instruction.operandReads before ∧
      ∀ read, read ∈ observation.reads → Sequential.OperandReadSucceeds before read := by
  obtain ⟨instruction, decoded, executed⟩ := rawStep_success_iff.mp actual
  exact ⟨instruction, decoded, executed, execute_reads executed, fun _ => execute_reads_succeed executed⟩

theorem execute_returned_only_ret {before after : State} {instruction : Instruction}
    {af : Bool} {reads : List Read}
    (actual : execute before instruction af = .ok ⟨.returned after, reads⟩) :
    instruction = .sequential (.legacy .ret) := by
  cases instruction with
  | sequential old => exact congrArg Instruction.sequential (Sequential.execute_returned_only_ret actual rfl)
  | callRelative32 _ | push64 _ _ | pop64 _ _ | leaDisp8 _ _ _ =>
    obtain ⟨_, impossible⟩ := execute_extension_next rfl actual
    cases impossible

/-- RET consumes actual current RAM, including tampered internal return words. -/
theorem execute_ret_success_iff {before after : State} {af : Bool} {reads : List Read} :
    execute before (.sequential (.legacy .ret)) af = .ok ⟨.returned after, reads⟩ ↔
    ∃ target, readWord before.memory (before.registers .rsp) = .ok target ∧
      canonical target = true ∧
      after = { before.writeRegister .rsp (before.registers .rsp + 8) with rip := target } ∧
      reads = [⟨.stack, before.registers .rsp, 8⟩] := by
  cases loaded : readWord before.memory (before.registers .rsp) with
  | error fault => simp [execute, Sequential.execute, X86.executeInstruction, executeRet, loaded]
  | ok target =>
    cases valid : canonical target <;>
      simp [execute, Sequential.execute, X86.executeInstruction, executeRet, loaded, valid,
        Sequential.Instruction.operandReads, Sequential.Observation.mk.injEq]
    all_goals simp only [eq_comm]

theorem rawStep_returned_iff {before after : State} {af : Bool} {reads : List Read} :
    rawStep af before = .ok ⟨.returned after, reads⟩ ↔
    decodeAt before = .ok (.sequential (.legacy .ret)) ∧
      execute before (.sequential (.legacy .ret)) af = .ok ⟨.returned after, reads⟩ := by
  constructor
  · intro actual
    obtain ⟨instruction, decoded, executed⟩ := rawStep_success_iff.mp actual
    have only := execute_returned_only_ret executed
    subst instruction
    exact ⟨decoded, executed⟩
  · rintro ⟨decoded, executed⟩
    rw [rawStep_eq_execute af decoded]
    exact executed

end EDSL.X86.CallReturn
