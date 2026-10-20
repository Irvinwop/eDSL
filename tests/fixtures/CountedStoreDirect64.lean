/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.CountedStoreDirect64.Policy

set_option warningAsError true

namespace EDSL.CountedStoreDirect64
open EDSL X86 X86.Sequential Grading CountedStore64

theorem useful_domain (variant : Variant) :
    Nonvacuous (registered .countedStore64) (bytes variant) :=
  domain_nonvacuous .countedStore64 (bytes variant)
    (by cases variant <;> decide) (by cases variant <;> decide)

/-- Both independent compiler clients prove the unchanged registered task.
Their arithmetic has constant instruction counts; acceptance remains a
mathematical result and present-world resource contract without a shape gate. -/
theorem claim (variant : Variant) : Grading.Claim .countedStore64 (bytes variant) :=
  ⟨⟨fun _ _ pre => ⟨fun choices => by
      obtain ⟨result,actual,post,_,_⟩ := raw_semantics pre choices
      exact ⟨result,actual,post⟩,raw_policy pre⟩,
    fun _ _ pre => ⟨fun choices => by
      obtain ⟨result,actual,post,returned,_,_⟩ := (resource_semantics pre).1 choices
      exact ⟨result,actual,post,returned⟩,(resource_semantics pre).2⟩⟩,
    useful_domain variant⟩

theorem gccClaim : Grading.Claim .countedStore64 (bytes .gcc) := claim .gcc
theorem clangClaim : Grading.Claim .countedStore64 (bytes .clang) := claim .clang

end EDSL.CountedStoreDirect64
