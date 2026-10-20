/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.GCC
import EDSL.Audit

set_option warningAsError true

#check EDSL.ArraySum64.GCC.bytes
#check EDSL.ArraySum64.GCC.graph
#check EDSL.ArraySum64.GCC.valid
#check EDSL.ArraySum64.GCC.semantics
#check EDSL.ArraySum64.GCC.cost
#check EDSL.ArraySum64.GCC.executions
#check EDSL.ArraySum64.GCC.raw_semantics
#check EDSL.ArraySum64.GCC.raw_policy
#check EDSL.ArraySum64.GCC.execution_exact
#check EDSL.ArraySum64.GCC.raw_accounting

#print axioms EDSL.ArraySum64.GCC.valid
#print axioms EDSL.ArraySum64.GCC.initialized_header
#print axioms EDSL.ArraySum64.GCC.next_header
#print axioms EDSL.ArraySum64.GCC.empty_post
#print axioms EDSL.ArraySum64.GCC.suffix_execution
#print axioms EDSL.ArraySum64.GCC.executions
#print axioms EDSL.ArraySum64.GCC.raw_semantics
#print axioms EDSL.ArraySum64.GCC.Prefix.advance
#print axioms EDSL.ArraySum64.GCC.Prefix.reachable
#print axioms EDSL.ArraySum64.GCC.raw_policy
#print axioms EDSL.ArraySum64.GCC.execution_exact
#print axioms EDSL.ArraySum64.GCC.raw_accounting
#print axioms EDSL.ArraySum64.GCC.semantics

#audit_edsl
