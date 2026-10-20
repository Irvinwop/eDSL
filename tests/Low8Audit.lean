/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.SequentialLow8
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.X86.Sequential.replaceLow8_eq_append
#print axioms EDSL.X86.Sequential.replaceLow8_widths
#print axioms EDSL.X86.Sequential.replaceLow8_bits
#print axioms EDSL.X86.Sequential.execute_setcc_context
#print axioms EDSL.X86.Sequential.execute_movImm8_context
#print axioms EDSL.X86.Sequential.execute_setcc_result
#print axioms EDSL.OS.CallResources.current_setcc_step
#print axioms EDSL.OS.CallResources.current_movImm8_step
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.X86.Sequential.CFG.execute_next_target
#print axioms EDSL.X86.Sequential.execute_new_flags
#print axioms EDSL.X86.Sequential.execute_returned_only_ret
#print axioms EDSL.X86.CallReturn.execute_liftSequential
#print axioms EDSL.X86.CallReturn.decodeAt_transport
#print axioms EDSL.X86.VCGen.sound
#print axioms EDSL.Tests.SequentialLow8.generated_vc_runs

#audit_edsl
