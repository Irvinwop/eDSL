/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Contract
import tests.fixtures.CallStack.Correctness

set_option warningAsError true

namespace EDSL.CallStack.Client
open Compiler

/-- Every current OS-admitted state and every choice stream has a covered
returning execution satisfying the fixed, independent postcondition. -/
theorem semantic_claim (profile : Profile) :
    Grading.CallStack.SemanticClaim (program profile) := by
  intro resource initial pre choices
  exact Compiler.covered profile pre choices

/-- Nonvacuity comes from the generic resource domain for any bounded code
window. It does not depend on these programs decoding or executing. -/
theorem useful_domain (profile : Profile) :
    Grading.CallStack.Nonvacuous (program profile) :=
  Grading.CallStack.domain_nonvacuous (program profile)
    (by cases profile <;> decide) (by cases profile <;> decide)

/-- Client proofs bind each original whole text and selected entry to the
closed resource-first grading contract. Counts and read order remain separate. -/
theorem claim (profile : Profile) : Grading.CallStack.Claim (program profile) :=
  ⟨semantic_claim profile, useful_domain profile⟩

/-- The closed export roots depend on their concrete execution proof, keeping
the other profiles' execution proofs out of each independently checked packet. -/
theorem gccSame : Grading.CallStack.Claim (program .gccSame) := by
  refine ⟨?_, Grading.CallStack.domain_nonvacuous _ (by decide) (by decide)⟩
  intro resource initial pre choices
  obtain ⟨evolved, result, actual, post, _, _⟩ := gccSame_covered_checked pre choices
  exact ⟨evolved, result, actual, post⟩

theorem gccSeparate : Grading.CallStack.Claim (program .gccSeparate) := by
  refine ⟨?_, Grading.CallStack.domain_nonvacuous _ (by decide) (by decide)⟩
  intro resource initial pre choices
  obtain ⟨evolved, result, actual, _, _, post⟩ := Padded.gcc_covered pre choices
  exact ⟨evolved, result, actual, post⟩

theorem clangSame : Grading.CallStack.Claim (program .clangSame) := by
  refine ⟨?_, Grading.CallStack.domain_nonvacuous _ (by decide) (by decide)⟩
  intro resource initial pre choices
  obtain ⟨evolved, result, actual, _, _, post⟩ := Padded.clang_covered (Or.inl rfl) pre choices
  exact ⟨evolved, result, actual, post⟩

theorem clangSeparate : Grading.CallStack.Claim (program .clangSeparate) := by
  refine ⟨?_, Grading.CallStack.domain_nonvacuous _ (by decide) (by decide)⟩
  intro resource initial pre choices
  obtain ⟨evolved, result, actual, _, _, post⟩ := Padded.clang_covered (Or.inr rfl) pre choices
  exact ⟨evolved, result, actual, post⟩

end EDSL.CallStack.Client
