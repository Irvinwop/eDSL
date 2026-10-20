/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.SequentialByteComparePadding
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.X86.Sequential.execute_cmpRegMem8_success_iff
#print axioms EDSL.X86.Sequential.execute_cmpRegMem8_contract
#print axioms EDSL.X86.Sequential.execute_cmpRegMem8_observed
#print axioms EDSL.X86.Sequential.execute_nop_context
#print axioms EDSL.X86.Sequential.NopEncoding.decode_bytes
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.X86.Sequential.code_fetch_transport_of_bound
#print axioms EDSL.X86.Sequential.CFG.Valid.address_no_wrap
#print axioms EDSL.X86.CallReturn.decodeAt_transport
#print axioms EDSL.X86.CallReturn.execute_cmpRegMem8
#print axioms EDSL.X86.VCGen.wp_cmpRegMem8_iff
#print axioms EDSL.BufferCall.Current.cmpRegMem8_step
#print axioms EDSL.PureCall.cmpRegMem8_not_rawRead
#print axioms EDSL.Tests.SequentialByteComparePadding.original_whole_windows
#print axioms EDSL.Tests.SequentialByteComparePadding.clang_checked
#print axioms EDSL.Tests.SequentialByteComparePadding.generated_vc_runs

#audit_edsl
