/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.Comparison64.Raw

set_option warningAsError true

namespace EDSL.Comparison64.Client
open X86 X86.Sequential Grading

def taskID : Operation → TaskID
  | .unsignedMaximum => .maximum64
  | .unsignedMinimum => .minimum64
  | .signedMaximum => .signedMaximum64

theorem registered_task (operation : Operation) :
    registered (taskID operation) = ofReadOnly (readOnlyTask operation) := by
  cases operation <;> rfl

/-- The same raw execution and prefix policy restore current OS code/slot
authority. Mathematical correctness remains independent of accounting. -/
theorem semantic_claim (variant : Variant) (operation : Operation) :
    SemanticClaim (registered (taskID operation)) (bytes variant operation) := by
  rw [registered_task]
  apply (old_semanticClaim_iff _ _).mpr
  apply readOnly_semantics_of_raw
  intro input initial pre
  refine ⟨?_,raw_policy pre⟩
  intro choices
  obtain ⟨result,actual,post,_,_⟩ := raw_semantics pre choices
  exact ⟨result,actual,post⟩

theorem useful_domain (variant : Variant) (operation : Operation) :
    Nonvacuous (registered (taskID operation)) (bytes variant operation) :=
  domain_nonvacuous (taskID operation) (bytes variant operation)
    (by cases variant <;> cases operation <;> decide)
    (by cases variant <;> cases operation <;> decide)

/-- Separate clients export checked claims for each complete compiler window;
the trusted registration does not import these implementations. -/
theorem claim (variant : Variant) (operation : Operation) :
    Grading.Claim (taskID operation) (bytes variant operation) :=
  ⟨semantic_claim variant operation,useful_domain variant operation⟩

theorem gccMaximum : Grading.Claim .maximum64 (bytes .gcc .unsignedMaximum) := claim .gcc .unsignedMaximum
theorem gccMinimum : Grading.Claim .minimum64 (bytes .gcc .unsignedMinimum) := claim .gcc .unsignedMinimum
theorem gccSignedMaximum : Grading.Claim .signedMaximum64 (bytes .gcc .signedMaximum) := claim .gcc .signedMaximum
theorem clangMaximum : Grading.Claim .maximum64 (bytes .clang .unsignedMaximum) := claim .clang .unsignedMaximum
theorem clangMinimum : Grading.Claim .minimum64 (bytes .clang .unsignedMinimum) := claim .clang .unsignedMinimum
theorem clangSignedMaximum : Grading.Claim .signedMaximum64 (bytes .clang .signedMaximum) := claim .clang .signedMaximum

end EDSL.Comparison64.Client
