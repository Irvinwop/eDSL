/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.Logical64.Raw

set_option warningAsError true

namespace EDSL.Logical64.Client
open X86 X86.Sequential Grading

def taskID : Operation → TaskID
  | .intersection => .intersection64
  | .union => .union64
  | .symmetricDifference => .symmetricDifference64

theorem registered_task (operation : Operation) :
    registered (taskID operation) = ofReadOnly (readOnlyTask operation) := by
  cases operation <;> rfl

/-- All-AF raw correctness and current-prefix policies establish the same
independent task for every literal program in this client family. -/
theorem semantic_claim (operation : Operation) :
    SemanticClaim (registered (taskID operation)) (bytes operation) := by
  rw [registered_task]
  exact (old_semanticClaim_iff _ _).mpr (readOnly_semantic_claim operation)

theorem useful_domain (operation : Operation) :
    Nonvacuous (registered (taskID operation)) (bytes operation) :=
  domain_nonvacuous (taskID operation) (bytes operation)
    (by cases operation <;> decide) (by cases operation <;> decide)

/-- This proof stays outside the trusted grader imports. A serialized proof
packet is checked against the registry's independently selected task and bytes. -/
theorem claim (operation : Operation) : Grading.Claim (taskID operation) (bytes operation) :=
  ⟨semantic_claim operation,useful_domain operation⟩

theorem intersection : Grading.Claim .intersection64 (bytes .intersection) := claim .intersection
theorem union : Grading.Claim .union64 (bytes .union) := claim .union
theorem symmetricDifference : Grading.Claim .symmetricDifference64 (bytes .symmetricDifference) :=
  claim .symmetricDifference

end EDSL.Logical64.Client
