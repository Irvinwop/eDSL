/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.ClosedForm
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallMemoryLoop64.ClosedForm.static_sites
#print axioms EDSL.CallMemoryLoop64.ClosedForm.static_decode
#print axioms EDSL.CallMemoryLoop64.ClosedForm.fetchWithin
#print axioms EDSL.CallMemoryLoop64.ClosedForm.target_predecessor
#print axioms EDSL.CallMemoryLoop64.ClosedForm.covered
#print axioms EDSL.CallMemoryLoop64.ClosedForm.semantic_claim
#print axioms EDSL.CallMemoryLoop64.ClosedForm.claim
#print axioms EDSL.CallMemoryLoop64.ClosedForm.evaluated
#print axioms EDSL.CallMemoryLoop64.ClosedForm.actual
#audit_edsl
