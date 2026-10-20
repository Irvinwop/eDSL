/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ShiftOne
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.Sum32.Artifact
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.X86.Sequential.decodeAt_shrOne64
#print axioms EDSL.X86.Sequential.execute_shrOne64_context
#print axioms EDSL.X86.Sequential.execute_shrOne64_flags
#print axioms EDSL.X86.Sequential.execute_shrOne64_choices
#print axioms EDSL.X86.Sequential.shrOneFlags64_observed_witness
#print axioms EDSL.X86.Sequential.shrOneFlags64_admits_both
#print axioms EDSL.X86.Sequential.shrOneFlags64_choice_injective
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.X86.Sequential.CFG.execute_next_target
#print axioms EDSL.X86.Sequential.execute_new_flags
#print axioms EDSL.X86.CallReturn.execute_liftSequential
#print axioms EDSL.X86.CallReturn.decodeAt_transport

#audit_edsl
