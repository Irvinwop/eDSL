/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.ClosedForm.Tail

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.ClosedForm
open X86 OS

/-- Every admitted full64 input/count, arbitrary current resources and old
DATA, and every AF stream have this actual covered returning execution.
Exact cost is a separate conclusion: GCC 4/6 and Clang 5/7 for zero/nonzero.
The root ordinary-RAM, AC/CET-disabled and no-asynchronous-interference
environmental contract applies unchanged. No native observation is asserted. -/
theorem covered {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result, CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state ∧ result.instructions = cost profile resource.count := by
  obtain ⟨middle, history, inv⟩ := front pre choices
  obtain ⟨evolved, result, execution, output, instructions⟩ :=
    tail (profile := profile) pre.code (history.current pre.current) inv (choices.drop (frontCost profile))
  let complete := result.prepend (frontCost profile) []
  have execution : CoveredExecution resource.descriptor choices resource.shared initial evolved complete :=
    history.then_execution execution
  have memory := execution.memory_frame pre.current
  refine ⟨evolved, complete, execution, ?_, ?_⟩
  · refine ⟨?_, output.stored, memory.1, memory.2.1, memory.2.2, output.returned, ?_,
      output.frame.preserved, output.frame.flags⟩
    · change (result.state.registers .rax).toNat = resultNat resource.value resource.count
      rw [output.value]
      exact resultNat_add _ _
    · change result.state.registers .rsp = initial.registers .rsp + 8
      rw [pre.stack]
      exact output.stack
  · change frontCost profile + result.instructions = cost profile resource.count
    rw [instructions]
    rfl

/-- The unchanged independent root semantic claim, without cost, positive
count, CALL, DATA-read, future-run or code-graph premises in admission. -/
theorem semantic_claim (profile : Profile) : SemanticClaim (program profile) := by
  intro resource initial pre choices
  obtain ⟨evolved, result, execution, post, _⟩ := covered pre choices
  exact ⟨evolved, result, execution, post⟩

/-- Useful nonvacuity is obtained from actual checked allocation for generic
bounded code, independently of this program's execution proof. -/
theorem claim (profile : Profile) : EDSL.CallMemoryLoop64.Claim (program profile) :=
  ⟨semantic_claim profile, domain_nonvacuous _ (positive profile) (bounded profile)⟩

/-- The actual evaluator succeeds at the exact proved cost. Returned bundles
the same covered execution, current stack/DATA capabilities, mixed history,
allocation/loan/permission preservation and independent root Post. -/
theorem evaluated {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result, CallReturn.run choices (cost profile resource.count) initial = .ok result ∧
      Returned resource initial choices evolved result ∧ result.instructions = cost profile resource.count := by
  obtain ⟨evolved, result, execution, post, instructions⟩ := covered pre choices
  have actual := execution.run (Nat.le_of_eq instructions)
  refine ⟨evolved, result, ?_, Returned.of_covered pre execution post, instructions⟩
  simpa only [CallReturn.run, pre.stack] using actual

/-- Every successful actual evaluator result, at arbitrary fuel, has the
same independent contract, current resources and exact instruction cost. -/
theorem actual {profile resource initial choices fuel result}
    (pre : ResourcePre (program profile) resource initial)
    (run : CallReturn.run choices fuel initial = .ok result) :
    ∃ evolved, Returned resource initial choices evolved result ∧
      result.instructions = cost profile resource.count := by
  obtain ⟨evolved, expected, execution, post, instructions⟩ := covered pre choices
  have machine : CallReturn.Executes choices initial expected := by
    simpa only [CallReturn.Executes, pre.stack] using execution.machine
  have same := CallReturn.ExecutesFrom.fixed_choices_unique machine (CallReturn.run_sound run)
  subst expected
  exact ⟨evolved, Returned.of_covered pre execution post, instructions⟩

end EDSL.CallMemoryLoop64.ClosedForm
