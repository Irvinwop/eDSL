/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArrayMaximum64.Domain
import tests.fixtures.ArrayMaximum64.Clang.Correctness
import tests.fixtures.ArrayMaximum64.Clang.Policy

set_option warningAsError true

namespace EDSL.ArrayMaximum64.Clang

/-- The public resource adapter consumes the actual raw proof and prefix
policy. Its current loans authorize every operand and survive the actual RET.
No instruction count or operand-read order enters this semantic claim. -/
theorem readOnly_semantic_claim : Grading.ReadOnlySemanticClaim readOnlyTask bytes :=
  readOnly_semantics_of_raw (fun _ _ _ pre => ⟨raw_semantics pre,raw_policy pre⟩)

/-- Independent current-resource and machine witnesses, with a nonzero full64
mathematical maximum. Admission itself continues to include empty inputs. -/
theorem useful_domain : Grading.ReadOnlyNonvacuous readOnlyTask bytes :=
  Domain.nonvacuous bytes (by decide) (by decide)

end EDSL.ArrayMaximum64.Clang
