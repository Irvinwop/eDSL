/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import tests.fixtures.ArraySum64.GCC

set_option warningAsError true

namespace EDSL.ArraySum64.Client
open Grading

/-- The complete compiler function satisfies the independently registered
natural sum modulo 2^64 with current OS resources. Accounting is separate. -/
theorem gcc : Grading.Claim .arraySum64 GCC.bytes := by
  refine ⟨(old_semanticClaim_iff _ _).mpr GCC.semantics,
    domain_nonvacuous .arraySum64 GCC.bytes (by decide) (by decide)⟩

end EDSL.ArraySum64.Client
