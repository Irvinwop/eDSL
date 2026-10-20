/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreLoad64.Contract
import EDSL.OS.Borrowing

set_option warningAsError true

namespace EDSL.StoreLoad64
open X86 X86.Sequential

/-- Exact full-RAM state after the store. -/
def stageOne (initial : State) : State :=
  { initial with
    memory := writeQWordUnchecked initial.memory (initial.registers .rdi) (initial.registers .rsi)
    rip := initial.rip + 3 }

/-- Exact state after the load, with RAX assigned the complete stored value. -/
def stageTwo (initial : State) : State :=
  { (stageOne initial).writeRegister .rax (initial.registers .rsi) with rip := initial.rip + 6 }

def finalState (initial : State) (target : Word) : State :=
  { (stageTwo initial).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

private theorem decode_from_code {memory base} (code : CodeAt memory base bytes)
    (offset : Nat) (inside : offset < bytes.length) {state instruction}
    (mem : state.memory = memory) (pc : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction :=
  decodeAt_transport (code_fetch_transport code (by decide) offset inside state mem pc) decoded

theorem stageOne_code {input initial} (pre : Pre bytes input initial) :
    CodeAt (stageOne initial).memory initial.rip bytes := by
  apply writeQWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

theorem first_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.storeMem64 (.base .rdi) .rsi) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

theorem second_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (stageOne initial) = .ok (.loadMem64 .rax (.base .rdi)) :=
  decode_from_code (stageOne_code pre) 3 (by decide) rfl rfl rfl

theorem ret_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (stageTwo initial) = .ok (.legacy .ret) :=
  decode_from_code (stageOne_code pre) 6 (by decide) rfl rfl rfl

theorem first_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (stageOne initial), []⟩ := by
  rw [step_eq_execute af (first_decoded pre)]
  have writable : canStoreQWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [Sequential.execute, Sequential.Instruction.operandReads, storeQWord, writable,
    stageOne, Address.eval, Sequential.Instruction.length]

theorem stageOne_value {input initial} (pre : Pre bytes input initial) :
    loadQWord (stageOne initial).memory input.address = .ok input.argument := by
  simpa only [stageOne, pre.pointer, pre.source] using
    qword_load_after_write initial.memory input.address input.argument pre.target_addressable

theorem second_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (stageOne initial) =
      .ok ⟨.next (stageTwo initial), [⟨.data, input.address, 8⟩]⟩ := by
  rw [step_eq_execute af (second_decoded pre)]
  have loaded : loadQWord (stageOne initial).memory ((Address.base .rdi).eval (stageOne initial)) =
      .ok (initial.registers .rsi) := by
    simpa only [Address.eval, stageOne, pre.pointer, pre.source] using stageOne_value pre
  rw [execute_loadMem64, loaded]
  simp [stageOne, stageTwo, State.writeRegister, Address.eval, Sequential.Instruction.length,
    BitVec.add_assoc, pre.pointer]

theorem stageTwo_stack {input initial} (pre : Pre bytes input initial) :
    readWord (stageTwo initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeQWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

theorem ret_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (stageTwo initial) =
      .ok ⟨.returned (finalState initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (stageTwo initial).memory ((stageTwo initial).registers .rsp) =
      .ok input.returnAddress := by
    simpa [stageTwo, stageOne, State.writeRegister] using stageTwo_stack pre
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [stageTwo, stageOne, State.writeRegister]

theorem final_post {input initial} (pre : Pre bytes input initial) :
    Post input initial (finalState initial input.returnAddress) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simpa [finalState, stageTwo, stageOne, State.writeRegister] using pre.source
  · simpa only [finalState, stageTwo, State.writeRegister] using stageOne_value pre
  · intro query outside
    exact writeQWord_frame initial.memory _ query _ (by simpa only [pre.pointer] using outside)
  · simp [finalState, stageTwo, stageOne, State.writeRegister]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same
      subst register
      simp [calleeSaved] at member
    have notRax : register ≠ .rax := by
      intro same
      subst register
      simp [calleeSaved] at member
    simp [finalState, stageTwo, stageOne, State.writeRegister, notStack, notRax]

/-- Actual three-instruction execution, including its ordered DATA8/STACK8
footprint, for every modeled AF stream. -/
theorem executions {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial input.returnAddress, 3,
        [⟨.data, input.address, 8⟩, ⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (first_step pre (choices 0))
    (Sequential.Executes.next (second_step pre ((choices.drop 1) 0))
      (Sequential.Executes.ret (ret_step pre (((choices.drop 1).drop 1) 0))))
  simpa only [Result.prepend, List.nil_append, List.cons_append] using execution

/-- Exact machine-code correctness follows from present inputs alone. -/
theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (ResultContract input initial) := by
  intro choices
  exact ⟨_, executions pre choices, final_post pre, rfl, rfl⟩

/-- Every instruction fetch stays inside the original admitted code span. -/
theorem fetch_at {input : Input} {initial before : State} {instruction : Sequential.Instruction}
    (pre : Pre bytes input initial)
    (offset : Nat) (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    OS.Borrowing.Subregion ⟨before.rip, instruction.length⟩ ⟨initial.rip, bytes.length⟩ := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 7 ≤ 2^64 at limit
  change offset + instruction.length ≤ 7 at span
  have small : offset < 2^64 := by omega
  have total : initial.rip.toNat + offset < 2^64 := by omega
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 7
  rw [pc, natural]
  omega

end EDSL.StoreLoad64
