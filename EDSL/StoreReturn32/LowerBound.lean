/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Accounting
import EDSL.X86.Sequential.Return

set_option warningAsError true

namespace EDSL.StoreReturn32
open X86 X86.Sequential

private theorem execute_returned_rax {initial final : State}
    {instruction : Sequential.Instruction} {af : Bool} {observation : Observation}
    (actual : Sequential.execute initial instruction af = .ok observation)
    (returned : observation.result = .returned final) :
    final.registers .rax = initial.registers .rax := by
  have onlyRet := execute_returned_only_ret actual returned
  rw [onlyRet] at actual
  cases loaded : readWord initial.memory (initial.registers .rsp) <;>
    simp [Sequential.execute, X86.executeInstruction, executeRet, loaded] at actual
  split at actual
  · cases actual
    cases returned
    simp [State.writeRegister]
  · cases actual

private theorem step_returned_rax {initial final : State} {af : Bool} {reads : List Read}
    (actual : Sequential.step af initial = .ok ⟨.returned final, reads⟩) :
    final.registers .rax = initial.registers .rax := by
  cases decoded : Sequential.decodeAt initial with
  | error fault => simp [Sequential.step, decoded] at actual
  | ok instruction =>
    rw [step_eq_execute af decoded] at actual
    exact execute_returned_rax actual rfl

/-- Every useful admitted execution that must change RAX takes at least three
modeled sequential instructions, including RET. The unchanged registered raw
policy excludes atomics; this is not a physical x86, cycle or source optimum. -/
theorem minimum_modeled_instructions {candidateBytes : List Byte}
    {input : Grading.Write32.Input} {choices : Choices} {initial : State} {result : Result}
    (pre : Grading.Write32.Pre candidateBytes input initial)
    (useful : Grading.Write32.Useful input)
    (needed : initial.registers .rax ≠ input.address)
    (policy : Grading.Write32.RawPolicy candidateBytes input initial)
    (execution : Sequential.Executes choices initial result)
    (post : StoreReturn32.Post input initial result.state) : 3 ≤ result.instructions := by
  have changed := Grading.Write32.useful_requires_memory_change pre useful post.toPost
  have raxChanged : result.state.registers .rax ≠ initial.registers .rax := by
    intro same
    exact needed (same.symm.trans post.pointer)
  obtain ⟨_, lifted, _⟩ := Grading.Trace.policy_return policy execution
  cases lifted with
  | ret _ actual _ _ =>
    exact False.elim (changed (step_returned_memory actual))
  | next decoded actual _ effect tail =>
    cases tail with
    | ret _ actualRet _ _ =>
      rw [step_eq_execute _ decoded] at actual
      have memory := step_returned_memory actualRet
      have rax := step_returned_rax actualRet
      rcases effect.2 with readOnly | ⟨value, store⟩
      · exact False.elim (changed (memory.trans (CFG.execute_next_memory readOnly actual rfl)))
      · have registers := (execute_storeIntent_frame store actual rfl).1
        exact False.elim (raxChanged (rax.trans (congrFun registers .rax)))
    | next _ _ _ _ tail =>
      have positive := Sequential.Executes.positive tail.erase
      simp only [Result.prepend]
      omega

/-- The registered claim supplies the postcondition and unchanged raw policy
for the same actual execution and AF stream supplied by the caller. -/
theorem claim_minimum {candidateBytes : List Byte} {input : Grading.Write32.Input}
    {choices : Choices} {initial : State} {result : Result}
    (claim : Grading.Claim .storeReturn32 candidateBytes)
    (pre : Grading.Write32.Pre candidateBytes input initial)
    (useful : Grading.Write32.Useful input)
    (needed : initial.registers .rax ≠ input.address)
    (execution : Sequential.Executes choices initial result) : 3 ≤ result.instructions := by
  have semantics := claim.1.machine input initial pre
  have post : StoreReturn32.Post input initial result.state :=
    Sequential.AllExecutions.project semantics.1 ⟨choices, execution⟩
  exact minimum_modeled_instructions pre useful needed semantics.2 execution post

end EDSL.StoreReturn32
