/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.Clang
import EDSL.Audit

set_option warningAsError true

#check EDSL.ArraySum64.Clang.bytes
#check EDSL.ArraySum64.Clang.graph
#check EDSL.ArraySum64.Clang.valid
#check EDSL.ArraySum64.Clang.semantics
#check EDSL.ArraySum64.Clang.instructionCount
#check EDSL.ArraySum64.Clang.raw_exact
#check EDSL.ArraySum64.Clang.raw_semantics
#check EDSL.ArraySum64.Clang.raw_policy
#check EDSL.ArraySum64.Clang.raw_accounting
#check EDSL.ArraySum64.Clang.execution_accounting
#check EDSL.ArraySum64.Clang.useful_domain

#print axioms EDSL.ArraySum64.Clang.valid
#print axioms EDSL.ArraySum64.Clang.raw_exact
#print axioms EDSL.ArraySum64.Clang.raw_semantics
#print axioms EDSL.ArraySum64.Clang.raw_policy
#print axioms EDSL.ArraySum64.Clang.raw_accounting
#print axioms EDSL.ArraySum64.Clang.execution_accounting
#print axioms EDSL.ArraySum64.Clang.semantics
#print axioms EDSL.ArraySum64.Clang.useful_domain
#audit_edsl
