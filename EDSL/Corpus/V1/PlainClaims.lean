/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.PlainInputs
import EDSL.OS.PlainCallClaim64

/-!
Universal independent plain64 claims for the checked unchanged compiler windows.
One shared catalog proof serves both operations and arbitrary admitted current
resources. Useful whole-loaded-file populations and execution certificates are
separate gates; these claims alone do not award compiler-corpus credit.
-/

set_option autoImplicit false

namespace EDSL.Corpus.V1.PlainClaims
open Grading.ConcurrentTask.Plain64

abbrev Compiler := PlainInputs.Compiler

theorem cohort (compiler : Compiler) : Claim (PlainInputs.catalog compiler) :=
  OS.PlainCallClaim64.claim (PlainInputs.staticShapes compiler)

/-- Homogeneous load or store cohorts reuse the entire mixed-catalog contract. -/
theorem named (compiler : Compiler) (kind : Kind) : Claim [PlainInputs.site compiler kind] :=
  (cohort compiler).mono (by
    intro selected member
    have same : selected = PlainInputs.site compiler kind := List.mem_singleton.mp member
    subst selected
    cases kind <;> simp [PlainInputs.catalog])

end EDSL.Corpus.V1.PlainClaims

#audit_edsl
