/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC
import tests.fixtures.CallMemoryLoop64.Clang
import EDSL.OS.CallMemory64.Cutpoints
import EDSL.OS.CallMemory64.Private
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallMemoryLoop64.GCC.claim
#print axioms EDSL.CallMemoryLoop64.Clang.claim
#print axioms EDSL.CallMemoryLoop64.domain_nonvacuous
#print axioms EDSL.CallMemoryLoop64.Compiler.static_decode
#print axioms EDSL.CallMemoryLoop64.Compiler.fetchWithin
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.execution
#print axioms EDSL.OS.CallMemory64.Cutpoints.Certificate.after_history
#print axioms EDSL.OS.CallMemory64.History.preserves_private
#print axioms EDSL.CallStack.CapacityDomain.allocated
#print axioms EDSL.CallMemory64.CapacityDomain.resource_pre
#audit_edsl
