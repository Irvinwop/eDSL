/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.Correctness
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallStack.ResourcePre.machine
#print axioms EDSL.CallStack.memory_frame
#print axioms EDSL.CallStack.Compiler.GCCSame.correct
#print axioms EDSL.CallStack.Compiler.Padded.gcc_correct
#print axioms EDSL.CallStack.Compiler.Padded.clang_correct
#print axioms EDSL.CallStack.Compiler.checked
#print axioms EDSL.CallStack.Compiler.evaluated
#audit_edsl
