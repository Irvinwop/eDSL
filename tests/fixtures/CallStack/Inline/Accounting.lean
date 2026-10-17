/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.Inline
import EDSL.Grading.CallStack.Accounting
import EDSL.Audit

set_option warningAsError true

namespace EDSL.CallStack.Inline
open X86

/-- The inlined candidate attains the instruction lower bound against every
accepted candidate on inputs requiring a changed RAX. Counts refer to the
modeled ISA, with no assertion about cycles or all-x86 instruction sets. -/
theorem optimal_for_useful_inputs {resource initial}
    (pre : ResourcePre program resource initial) (choices : CallReturn.Choices) :
    CallReturn.run choices 2 initial = .ok (result resource initial) ∧
      ∀ candidate, Grading.CallStack.Claim candidate →
        ∀ other otherInitial otherChoices otherResult,
          ResourcePre candidate other otherInitial → Grading.CallStack.Useful other otherInitial →
          CallReturn.Executes otherChoices otherInitial otherResult →
          (result resource initial).instructions ≤ otherResult.instructions := by
  refine ⟨exact_two pre choices, ?_⟩
  intro candidate accepted other otherInitial otherChoices otherResult admitted useful actual
  exact Grading.CallStack.minimum_modeled_instructions accepted admitted useful actual

end EDSL.CallStack.Inline

#print axioms EDSL.X86.CallReturn.ExecutesFrom.changed_rax_needs_two
#print axioms EDSL.Grading.CallStack.minimum_modeled_instructions
#print axioms EDSL.CallStack.Inline.claim
#print axioms EDSL.CallStack.Inline.exact_two
#print axioms EDSL.CallStack.Inline.optimal_for_useful_inputs
#audit_edsl
