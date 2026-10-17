/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC.Prologue
import tests.fixtures.CallMemoryLoop64.GCC.Loop
import EDSL.CallMemoryLoop64.Admission

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

/-- Complete separately compiled GCC text: all full64 counts, arbitrary current
resources and admitted CPU states, and every AF stream. The exact model cost
is a consequence of actual execution, separate from the independent contract.
The underlying profile is ordinary sequential RAM with AC/CET disabled and no
asynchronous interference, as specified by the root contract. -/
theorem covered {resource : Resources} {initial : State}
    (pre : ResourcePre (Compiler.program .gccSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result, CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = 12 + 10 * resource.count.toNat := by
  obtain ⟨middleWorld, middle, history, middleCurrent, middleInv⟩ := prologue pre choices
  obtain ⟨evolved, result, execution, output, cost⟩ :=
    loop pre.code pre.stackCapacity middleCurrent middleInv (choices.drop 5)
  let complete := result.prepend 5 []
  have covered : CoveredExecution resource.descriptor choices resource.shared initial evolved complete :=
    history.then_execution execution
  have memory := covered.memory_frame pre.current
  refine ⟨evolved, complete, covered, ?_, ?_⟩
  · refine ⟨?_, output.stored, memory.1, memory.2.1, memory.2.2, output.returned, ?_,
      output.preserved, output.flags⟩
    · change (result.state.registers .rax).toNat = resultNat resource.value resource.count
      rw [output.value]
      exact resultNat_add _ _
    · change result.state.registers .rsp = initial.registers .rsp + 8
      rw [pre.stack]
      exact output.stack
  · simp only [complete, Sequential.Result.prepend]
    omega

/-- Universal correctness has no future execution, cost, CALL, read order or
positive-count premise. All fetches and both current capabilities belong to
this same constructed covered mixed execution. -/
theorem semantic_claim : SemanticClaim (Compiler.program .gccSeparate) := by
  intro resource initial pre choices
  obtain ⟨evolved, result, execution, post, _⟩ := covered pre choices
  exact ⟨evolved, result, execution, post⟩

/-- Public compiler-backed claim, including checked-allocation nonvacuity. -/
theorem claim : EDSL.CallMemoryLoop64.Claim (Compiler.program .gccSeparate) :=
  ⟨semantic_claim, domain_nonvacuous _ (by decide) (by decide)⟩

/-- Useful evaluator/cost theorem with the actual frozen original slot,
current endpoint, mixed preservation and independent output contract. Counts
up to 2^64-1 are handled by proof, without evaluating that many iterations. -/
theorem evaluated {resource : Resources} {initial : State}
    (pre : ResourcePre (Compiler.program .gccSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.runFrom resource.descriptor.frame.top choices (12 + 10 * resource.count.toNat) initial = .ok result ∧
      Returned resource initial choices evolved result ∧
      result.instructions = 12 + 10 * resource.count.toNat := by
  obtain ⟨evolved, result, execution, post, cost⟩ := covered pre choices
  exact ⟨evolved, result, execution.run (Nat.le_of_eq cost), Returned.of_covered pre execution post, cost⟩

/-- Every successful actual evaluator result at any fuel has the same exact
cost and contract; uniqueness identifies it with the universally built run. -/
theorem actual {resource : Resources} {initial : State} {choices : CallReturn.Choices}
    {fuel : Nat} {result : CallReturn.Result}
    (pre : ResourcePre (Compiler.program .gccSeparate) resource initial)
    (run : CallReturn.run choices fuel initial = .ok result) :
    ∃ evolved, Returned resource initial choices evolved result ∧
      result.instructions = 12 + 10 * resource.count.toNat := by
  obtain ⟨evolved, expected, execution, post, cost⟩ := covered pre choices
  have machine : CallReturn.Executes choices initial expected := by
    simpa only [CallReturn.Executes, pre.stack] using execution.machine
  have same := CallReturn.ExecutesFrom.fixed_choices_unique machine (CallReturn.run_sound run)
  subst expected
  exact ⟨evolved, Returned.of_covered pre execution post, cost⟩

end EDSL.CallMemoryLoop64.GCC
