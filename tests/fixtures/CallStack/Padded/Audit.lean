/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.Padded
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallStack.Compiler.Padded.prefix_checked
#print axioms EDSL.CallStack.Compiler.Padded.gcc_correct
#print axioms EDSL.CallStack.Compiler.Padded.clang_correct
#audit_edsl
