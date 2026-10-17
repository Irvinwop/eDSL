/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArraySum64.Domain
import tests.fixtures.ArraySum64.Clang.Correctness
import tests.fixtures.ArraySum64.Clang.Policy

set_option warningAsError true

namespace EDSL.ArraySum64.Clang

/-- The independent full64 modular sum, finite all-AF termination, original
caller RET and complete machine frame, with current loans at every actual
prefix and return. The checked adapter consumes both raw correctness and
prefix-sensitive read policy; admission assumes no future execution. -/
theorem semantics : Grading.ReadOnlySemanticClaim readOnlyTask bytes :=
  readOnly_semantics_of_raw (fun _ _ _ pre => ⟨raw_semantics pre,raw_policy pre⟩)

/-- Independent current machine/resource inputs have a positive modular sum.
This witness does not restrict universal admission, which includes empty,
zero and wrapping inputs. -/
theorem useful_domain : Grading.ReadOnlyNonvacuous readOnlyTask bytes :=
  Domain.nonvacuous bytes (by decide) (by decide)

end EDSL.ArraySum64.Clang
