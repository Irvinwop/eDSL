/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64.Correctness
import EDSL.CallMemory64.Admission

set_option warningAsError true

namespace EDSL.CallMemory64.Client
open Compiler

/-- Client proof of the independent task contract, universally over present
resources, full-width inputs, other registers, flags and AF choice streams. -/
theorem semantic_claim (profile : Profile) : SemanticClaim (program profile) := by
  cases profile with
  | gccSeparate => exact gcc_semantic
  | clangSeparate => exact clang_semantic

/-- Nonvacuity uses the independent actual-allocation domain, with both
caller-visible outputs requiring a change. No compiler behavior is admitted. -/
theorem useful_domain (profile : Profile) : Nonvacuous (program profile) :=
  domain_nonvacuous _ (by cases profile <;> decide) (by cases profile <;> decide)

theorem claim (profile : Profile) : Claim (program profile) :=
  ⟨semantic_claim profile, useful_domain profile⟩

theorem gccSeparate : Claim (program .gccSeparate) :=
  ⟨gcc_semantic, domain_nonvacuous _ (by decide) (by decide)⟩

theorem clangSeparate : Claim (program .clangSeparate) :=
  ⟨clang_semantic, domain_nonvacuous _ (by decide) (by decide)⟩

/-- Universal compiler correctness specializes to the reachable domain with
arbitrary old target contents, all input words, register seeds and flags. The
actual endpoint still retains both owner resources and their mixed history. -/
theorem domain_evaluated (profile : Profile) (input old : X86.Word)
    (registers : X86.Register → X86.Word) (flags : X86.Word)
    (choices : X86.CallReturn.Choices) :
    ∃ evolved result,
      X86.CallReturn.runFrom (Domain.descriptor (program profile).bytes).frame.top choices 8
        (Domain.initial (program profile) input old registers flags) = .ok result ∧
      Returned (Domain.resource (program profile) input old)
        (Domain.initial (program profile) input old registers flags) choices evolved result ∧
      result.instructions = 8 ∧ result.reads = reads (Domain.resource (program profile) input old) := by
  have pre := Domain.resource_pre (program profile) (by cases profile <;> decide)
    (by cases profile <;> decide) input old registers flags
  obtain ⟨evolved, result, actual, covered, _, _, post, cost, trace⟩ := evaluated profile pre choices
  exact ⟨evolved, result, actual, Returned.of_covered pre covered post, cost, trace⟩

end EDSL.CallMemory64.Client
