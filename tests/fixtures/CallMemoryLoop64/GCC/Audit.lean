/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallMemoryLoop64.GCC.push_next
#print axioms EDSL.CallMemoryLoop64.GCC.call_next
#print axioms EDSL.CallMemoryLoop64.GCC.store_next
#print axioms EDSL.CallMemoryLoop64.GCC.inner_ret_next
#print axioms EDSL.CallMemoryLoop64.GCC.Saved.private_store
#print axioms EDSL.CallMemoryLoop64.GCC.Saved.data_store
#print axioms EDSL.CallMemoryLoop64.GCC.prologue
#print axioms EDSL.CallMemoryLoop64.GCC.body
#print axioms EDSL.CallMemoryLoop64.GCC.target_predecessor
#print axioms EDSL.CallMemoryLoop64.GCC.exit
#print axioms EDSL.CallMemoryLoop64.GCC.loop
#print axioms EDSL.CallMemoryLoop64.GCC.covered
#print axioms EDSL.CallMemoryLoop64.GCC.semantic_claim
#print axioms EDSL.CallMemoryLoop64.GCC.claim
#print axioms EDSL.CallMemoryLoop64.GCC.evaluated
#print axioms EDSL.CallMemoryLoop64.GCC.actual
#audit_edsl
