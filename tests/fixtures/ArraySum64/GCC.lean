/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.GCC.Policy
import EDSL.ArraySum64.Resources

set_option warningAsError true

namespace EDSL.ArraySum64.GCC

/-- Complete GCC13 text satisfies the independent sum contract for every
admitted machine/current-resource input and AF stream, including empty and
wrapping sums. Exact instruction/read accounting is a separate claim. -/
theorem semantics : Grading.ReadOnlySemanticClaim readOnlyTask bytes :=
  readOnly_semantics_of_raw (fun _ _ _ pre => ⟨raw_semantics pre,raw_policy pre⟩)

end EDSL.ArraySum64.GCC
