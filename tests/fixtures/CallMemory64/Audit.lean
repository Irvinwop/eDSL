/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64.Covered
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallMemory64.Compiler.prefix_covered
#print axioms EDSL.CallMemory64.Compiler.gcc_covered
#print axioms EDSL.CallMemory64.Compiler.gcc_semantic
#print axioms EDSL.CallMemory64.Compiler.gcc_evaluated
#print axioms EDSL.CallMemory64.Compiler.clang_covered
#print axioms EDSL.CallMemory64.Compiler.clang_semantic
#print axioms EDSL.CallMemory64.Compiler.evaluated
#print axioms EDSL.CallMemory64.Client.gccSeparate
#print axioms EDSL.CallMemory64.Client.clangSeparate
#print axioms EDSL.CallMemory64.Client.domain_evaluated
#audit_edsl
