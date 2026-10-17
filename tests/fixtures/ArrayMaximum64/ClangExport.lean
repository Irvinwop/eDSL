/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.ArrayMaximum64.Clang

set_option warningAsError true

namespace EDSL.ArrayMaximum64.Client
open Grading

/-- The exact complete Clang18 function satisfies the same registered task
as GCC, including empty inputs and current OS code/input/caller-slot loans. -/
theorem clang : Grading.Claim .arrayMaximum64 Clang.bytes := by
  refine ⟨(old_semanticClaim_iff _ _).mpr ?_,
    domain_nonvacuous .arrayMaximum64 Clang.bytes (by decide) (by decide)⟩
  exact Clang.readOnly_semantic_claim

end EDSL.ArrayMaximum64.Client
