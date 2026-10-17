/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64.Inline
import EDSL.CallMemory64.Accounting
import EDSL.Audit

set_option warningAsError true

namespace EDSL.CallMemory64.Inline
open X86

/-- The actual three-instruction candidate attains the independent lower
bound against every accepted candidate on admitted useful inputs. Counts are
for the accepted mixed model, without a claim about all raw ISA code or cycles. -/
theorem optimal_for_useful_inputs {resource initial}
    (pre : ResourcePre program resource initial) (choices : CallReturn.Choices) :
    (∃ evolved result, CallReturn.run choices 3 initial = .ok result ∧
      Returned resource initial choices evolved result ∧ result.instructions = 3) ∧
    ∀ candidate, Claim candidate →
      ∀ other otherInitial otherChoices otherResult,
        ResourcePre candidate other otherInitial → Useful other otherInitial →
        CallReturn.Executes otherChoices otherInitial otherResult →
        3 ≤ otherResult.instructions := by
  refine ⟨exact_three pre choices, ?_⟩
  intro candidate accepted other otherInitial otherChoices otherResult admitted useful actual
  exact minimum_modeled_instructions accepted admitted useful actual

/-- The same actual evaluator theorem specializes to arbitrary full-width
inputs and old target contents, register seeds, flags and AF streams in the
independently allocated resource domain. -/
theorem domain_evaluated (input old : Word) (registers : Register → Word)
    (flags : Word) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices 3 (Domain.initial program input old registers flags) = .ok result ∧
      Returned (Domain.resource program input old)
        (Domain.initial program input old registers flags) choices evolved result ∧
      result.instructions = 3 :=
  exact_three (Domain.resource_pre program (by decide) (by decide) input old registers flags) choices

end EDSL.CallMemory64.Inline

#print axioms EDSL.OS.CallMemory64.CPU.Step.rax_or_memory
#print axioms EDSL.OS.CallMemory64.CPU.Step.returned_preserves
#print axioms EDSL.OS.CallMemory64.CPU.Execution.changed_rax_memory_needs_three
#print axioms EDSL.CallMemory64.minimum_modeled_instructions
#print axioms EDSL.CallMemory64.minimum_run
#print axioms EDSL.CallMemory64.Inline.claim
#print axioms EDSL.CallMemory64.Inline.exact_three
#print axioms EDSL.CallMemory64.Inline.optimal_for_useful_inputs
#print axioms EDSL.CallMemory64.Inline.domain_evaluated
#audit_edsl
