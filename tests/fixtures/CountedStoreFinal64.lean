/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.CountedStoreFinal64.Accounting

set_option warningAsError true

namespace EDSL.CountedStoreFinal64
open EDSL X86 X86.Sequential Grading CountedStore64

/-- Admission remains independent of the loop and is useful for this byte list. -/
theorem useful_domain : Nonvacuous (registered .countedStore64) bytes :=
  domain_nonvacuous .countedStore64 bytes (by decide) (by decide)

/-- This client is outside the grader's trusted import snapshot. Its loop
retains the old target until a single final positive-count store, while proving
the same registered mathematical result and current OS authority contract. -/
theorem claim : Grading.Claim .countedStore64 bytes :=
  ⟨⟨fun _ _ pre => ⟨fun choices => by
      obtain ⟨result, actual, post, _⟩ := raw_semantics pre choices
      exact ⟨result, actual, post⟩, raw_policy pre⟩,
    fun _ _ pre => ⟨fun choices => by
      obtain ⟨result, actual, post, returned, _⟩ := (resource_semantics pre).1 choices
      exact ⟨result, actual, post, returned⟩, (resource_semantics pre).2⟩⟩,
    useful_domain⟩

end EDSL.CountedStoreFinal64
