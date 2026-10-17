/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.ArrayMaximum64.GCC

set_option warningAsError true

namespace EDSL.ArrayMaximum64.Client
open Grading

/-- The exact complete GCC13 function satisfies the independently registered
array maximum task. Exact cost and operand order remain separate theorems. -/
theorem gcc : Grading.Claim .arrayMaximum64 GCC.bytes := by
  refine ⟨(old_semanticClaim_iff _ _).mpr ?_,
    domain_nonvacuous .arrayMaximum64 GCC.bytes (by decide) (by decide)⟩
  exact readOnly_semantics_of_raw (fun _ _ _ pre => ⟨GCC.raw_semantics pre,GCC.raw_policy pre⟩)

end EDSL.ArrayMaximum64.Client
