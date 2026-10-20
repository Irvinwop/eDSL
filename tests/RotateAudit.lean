/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Rotate
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.X86.Sequential.Unary
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.VCGen.Frame
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.X86.Sequential.decodeAt_rolCL64
#print axioms EDSL.X86.Sequential.decodeREXWAt_rolCL64_badREX
#print axioms EDSL.X86.Sequential.decodeAt_rolCL64_rejects
#print axioms EDSL.X86.Sequential.decodeAt_rolCL64_modrm_fault
#print axioms EDSL.X86.Sequential.execute_rolCL64_context
#print axioms EDSL.X86.Sequential.execute_rolCL64_zero
#print axioms EDSL.X86.Sequential.execute_rolCL64_flags
#print axioms EDSL.X86.Sequential.execute_rolCL64_choices
#print axioms EDSL.X86.Sequential.rolFlags64_observed_witness
#print axioms EDSL.X86.Sequential.rolFlags64_admissible_iff
#print axioms EDSL.X86.Sequential.rolFlags64_choice_injective
#print axioms EDSL.X86.Sequential.execute_choice_independent
#print axioms EDSL.X86.Sequential.execute_choice_context
#print axioms EDSL.X86.Sequential.execute_choice_observed_witness
#print axioms EDSL.X86.Sequential.execute_choice_admissible_iff
#print axioms EDSL.X86.Sequential.current_rolCL64_step
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.X86.Sequential.CFG.execute_next_target
#print axioms EDSL.X86.Sequential.execute_new_flags
#print axioms EDSL.X86.Sequential.step_returned_memory
#print axioms EDSL.X86.CallReturn.execute_liftSequential
#print axioms EDSL.X86.CallReturn.liftSequential_choiceFlag
#print axioms EDSL.X86.CallReturn.execute_choice_independent
#print axioms EDSL.X86.CallReturn.decodeAt_transport
#print axioms EDSL.X86.VCGen.decidableWP
#print axioms EDSL.X86.VCGen.certify_sound_frame
#print axioms EDSL.X86.VCGen.pureCall_semantics_of_generated

#audit_edsl
