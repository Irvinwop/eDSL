/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Execution

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential
open EDSL EDSL.X86

/-- Invert the entire legacy executor, including stores, locked RMWs and
syscalls. There is no read-only, policy or candidate-code premise. -/
private theorem legacy_returned_only_ret {initial final : State} {instruction : X86.Instruction}
    (actual : X86.executeInstruction initial instruction = .ok (.returned final)) :
    instruction = .ret := by
  cases instruction with
  | ret => rfl
  | leaEaxRdiDisp8 _ | leaEaxRaxDisp8 _ | movEaxEdi | movEaxEsi
  | cmpEaxZero | mov32 _ _ | syscall => cases actual
  | exchangeEaxRdi =>
    cases result : executeExchange initial <;>
      simp [X86.executeInstruction, result] at actual
  | fetchAddEaxRdi =>
    cases result : executeFetchAdd initial <;>
      simp [X86.executeInstruction, result] at actual
  | jrcxz displacement =>
    cases result : executeJrcxz initial displacement <;>
      simp [X86.executeInstruction, result] at actual
  | loopRcx displacement =>
    cases result : executeLoop initial displacement <;>
      simp [X86.executeInstruction, result] at actual
  | jnz displacement =>
    cases result : executeJnz initial displacement <;>
      simp [X86.executeInstruction, result] at actual
  | loadEaxRdi =>
    cases result : executeLoad initial <;>
      simp [X86.executeInstruction, result] at actual
  | loadEaxRsi =>
    cases result : executeLoadRsi initial <;>
      simp [X86.executeInstruction, result] at actual
  | storeEsiRdi =>
    cases result : executeStore initial <;>
      simp [X86.executeInstruction, result] at actual
  | storeEaxRsi =>
    cases result : executeStoreRsi initial <;>
      simp [X86.executeInstruction, result] at actual

/-- All extension instructions continue. Only actual legacy RET can return.
The statement covers the full sequential executor, without effect restrictions. -/
theorem execute_returned_only_ret {initial final : State}
    {instruction : Sequential.Instruction} {af : Bool} {observation : Observation}
    (actual : Sequential.execute initial instruction af = .ok observation)
    (returned : observation.result = .returned final) : instruction = .legacy .ret := by
  cases instruction with
  | legacy old =>
    cases result : X86.executeInstruction initial old with
    | error fault => simp [Sequential.execute, result] at actual
    | ok outcome =>
      simp only [Sequential.execute, result, ok_bind, pure_ok, Except.ok.injEq] at actual
      cases actual
      cases returned
      exact congrArg Sequential.Instruction.legacy (legacy_returned_only_ret result)
  | shiftRightImm32 _ _ _ _ | imulReg64 _ _ | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | addImm32 _ _ _ | inc32 _ _
  | negReg32 _ _ | bswapReg64 _ | shrOne64 _ | rolCL64 _
  | movzxMem8 _ _ _ | movzxReg8 _ _ _ | cmpReg8 _ _ _ | subReg32 _ _ _
  | xorSelf32 _ | movReg32 _ _ | movReg64 _ _ | setcc _ _ _ | movImm8 _ _ _ | movSignImm32 _ _ | cmovReg32 _ _ _ _ | cmovReg64 _ _ _ | lea64 _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _ | loadMem32 _ _ | storeMem32 _ _ | loadMem64 _ _ | storeMem64 _ _
  | test32 _ _ _ | cmp32 _ _ _ | cmpMemImm8 _ _ | cmpRegMem8 _ _ _ | cmpMemReg8 _ _ | cmpMemReg32 _ _ | endbr64IbtDisabled | nop _ | test64 _ _ | cmp64 _ _ | addMem32 _ _ | addMem64 _ _ | addImm64 _ _
  | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ =>
    obtain ⟨middle, next⟩ := execute_new_next rfl actual
    rw [returned] at next
    cases next

/-- Read-only is derived from the actual returned result; it is not assumed.
The existing CFG memory lemma is used only after this derivation. -/
theorem execute_returned_memory {initial final : State}
    {instruction : Sequential.Instruction} {af : Bool} {observation : Observation}
    (actual : Sequential.execute initial instruction af = .ok observation)
    (returned : observation.result = .returned final) : final.memory = initial.memory := by
  have onlyRet := execute_returned_only_ret actual returned
  have readOnly : CFG.readOnly instruction = true := by rw [onlyRet]; rfl
  exact CFG.execute_returned_memory readOnly actual returned

/-- Actual current executable RAM is decoded. No client-selected transition,
fixed fixture, checked CFG or raw-policy hypothesis occurs in this statement. -/
theorem step_returned_memory {initial final : State} {af : Bool} {reads : List Read}
    (actual : Sequential.step af initial = .ok ⟨.returned final, reads⟩) :
    final.memory = initial.memory := by
  cases decoded : Sequential.decodeAt initial with
  | error fault => simp [Sequential.step, decoded] at actual
  | ok instruction =>
    rw [step_eq_execute af decoded] at actual
    exact execute_returned_memory actual rfl

/-- A memory-changing actual returning execution costs at least two modeled
instructions. The atomic constructor is covered; its returning tail is positive.
Syscalls are boundaries and have no returning Executes constructor. -/
theorem Executes.memory_change_needs_two {choices : Choices} {initial : State} {result : Result}
    (execution : Sequential.Executes choices initial result)
    (changed : result.state.memory ≠ initial.memory) : 2 ≤ result.instructions := by
  cases execution with
  | ret actual => exact False.elim (changed (step_returned_memory actual))
  | next actual tail | atomic actual tail =>
    have positive := Engine.Executes.positive Sequential.step tail
    simp only [Result.prepend]
    omega

end EDSL.X86.Sequential
