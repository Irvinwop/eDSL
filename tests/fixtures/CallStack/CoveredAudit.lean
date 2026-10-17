/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.Covered
import EDSL.Audit

set_option warningAsError true

namespace EDSL.CallStack.Compiler.CoveredAudit
open X86 OS

/-- The first opcode byte of the real five-byte CALL is insufficient even
when all actual executable bytes remain in memory. -/
theorem clipped_call {frame : StackFrame.Descriptor} {before : State}
    (code : CodeAt before.memory frame.call.code (bytes .gccSame))
    (pc : before.rip = frame.call.code + 5)
    (extent : frame.call.bytes.length = 9) : ¬FetchWithin frame before := by
  have decoded := decode code .call rfl pc
  intro covered
  have bound := (FetchWithin.atOffset_iff (by omega : frame.call.bytes.length ≤ 2^64)
    (by decide : 5 < 2^64) pc decoded).mp covered
  change 5 + 5 ≤ frame.call.bytes.length at bound
  omega

/-- Stopping the selected extent at the first RET omits the separate-TU
helper's actual internal RET. Its presence in RAM cannot authorize that fetch. -/
theorem first_ret_truncation {frame : StackFrame.Descriptor} {before : State}
    (code : CodeAt before.memory frame.call.code (bytes .gccSeparate))
    (pc : before.rip = frame.call.code + 15)
    (extent : frame.call.bytes.length = 11) : ¬FetchWithin frame before := by
  have decoded := decode code .innerRet rfl pc
  intro covered
  have bound := (FetchWithin.atOffset_iff (by omega : frame.call.bytes.length ≤ 2^64)
    (by decide : 15 < 2^64) pc decoded).mp covered
  change 15 + 1 ≤ frame.call.bytes.length at bound
  omega

/-- The original caller RET also needs its own byte in the whole extent. -/
theorem omitted_original_ret {frame : StackFrame.Descriptor} {before : State}
    (code : CodeAt before.memory frame.call.code (bytes .gccSame))
    (pc : before.rip = frame.call.code + 13)
    (extent : frame.call.bytes.length = 13) : ¬FetchWithin frame before := by
  have decoded := decode code .ret rfl pc
  intro covered
  have bound := (FetchWithin.atOffset_iff (by omega : frame.call.bytes.length ≤ 2^64)
    (by decide : 13 < 2^64) pc decoded).mp covered
  change 13 + 1 ≤ frame.call.bytes.length at bound
  omega

#check @GCCSame.correct
#check @Padded.prefix_checked
#check @Padded.gcc_correct
#check @Padded.clang_correct
#check @covered
#check @covered_checked
#check @checked
#check @evaluated
#check @Client.semantic_claim
#check @Client.useful_domain
#check @Client.claim
#check @Client.gccSame
#check @Client.gccSeparate
#check @Client.clangSame
#check @Client.clangSeparate
#check @Certificates.fetchWithin_of_code
#check @gccSame_covered_checked
#print axioms Certificates.fetchWithin_of_code
#print axioms clipped_call
#print axioms first_ret_truncation
#print axioms omitted_original_ret
#print axioms EDSL.CallStack.Compiler.covered
#print axioms EDSL.CallStack.Compiler.evaluated
#print axioms Client.semantic_claim
#print axioms Client.useful_domain
#print axioms Client.gccSame
#print axioms Client.gccSeparate
#print axioms Client.clangSame
#print axioms Client.clangSeparate
#audit_edsl

end EDSL.CallStack.Compiler.CoveredAudit
