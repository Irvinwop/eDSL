/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ParityISA
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.Sum32.Artifact
import EDSL.X86.VCGen.Core
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.X86.Sequential.execute_logicalReg32_context
#print axioms EDSL.X86.Sequential.execute_logicalImm32_context
#print axioms EDSL.X86.Sequential.execute_cmpImm64_context
#print axioms EDSL.X86.Sequential.logicalFlags32_observed_witness
#print axioms EDSL.X86.Sequential.logicalFlags32_admissible_iff
#print axioms EDSL.X86.Sequential.logicalFlags32_choices
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.X86.Sequential.CFG.execute_next_target
#print axioms EDSL.X86.Sequential.execute_new_flags
#print axioms EDSL.X86.Sequential.execute_returned_only_ret
#print axioms EDSL.X86.CallReturn.execute_liftSequential
#print axioms EDSL.X86.CallReturn.decodeAt_transport
#print axioms EDSL.X86.VCGen.sound

#audit_edsl
