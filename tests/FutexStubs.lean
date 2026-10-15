/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexCertificate
import EDSL.Examples.Suspend
import EDSL.Audit

namespace EDSL.Tests.FutexStubs
open X86 Examples.FutexStubs

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def initial (profile : Profile) : State :=
  { OS.MachineThreads.contextState Examples.Suspend.callerContext
      (Examples.Suspend.memory profile.bytes []) with
    registers := fun register =>
      if register = .rdx then 0x89abcdef
      else if register = .r10 ∨ register = .r8 ∨ register = .r9 then 0
      else Examples.Suspend.callerContext.registers register }

def requestView (invocation : Invocation) :
    Nat × Word × BitVec 32 × List Word × Word × Word × Word :=
  (invocation.instructions, invocation.request.user.registers .rax,
    invocation.request.number,
    [.first, .second, .third, .fourth, .fifth, .sixth].map invocation.request.argument,
    invocation.request.user.rip, invocation.request.continuation, invocation.request.user.flags)

-- Execute independently assembled opcodes. High initial RAX/RSI values expose
-- missing zero extension; all six arguments and both boundary PCs are checked.
example : (runToSyscall 3 (initial .wait)).map requestView =
    .ok (3, 202, 202, [65536, 128, 0x89abcdef, 0, 0, 0], 4106, 4108, 0x8d7) := by rfl
example : (runToSyscall 4 (initial .wakeOne)).map requestView =
    .ok (4, 202, 202, [65536, 129, 1, 0, 0, 0], 4111, 4113, 0x8d7) := by rfl

def current (profile : Profile) : Memory :=
  writeDWordUnchecked (initial profile).memory 65536 0x11223344

def completionView (execution : Execution) :
    Nat × Word × Word × Word × Word × Word × Word × Option (BitVec 32) :=
  (execution.instructions, execution.state.registers .rax, execution.state.registers .rsp,
    execution.state.rip, execution.state.flags, execution.state.registers .rcx,
    execution.state.registers .r11, (loadDWord execution.state.memory 65536).toOption)

-- Full raw errno bits and arbitrary post-kernel flags/RCX/R11 survive actual
-- RET. Returning through historical request RAM would lose the peer's update.
example : (run 1 (resumeAt (request .wait (initial .wait)) (current .wait)
      0xfffffffffffffff5 0xabcdef0123456789 0xfedcba9876543210 0x8877665544332211)).map completionView =
    .ok (1, 0xfffffffffffffff5, 32776, 12288, 0xabcdef0123456789,
      0xfedcba9876543210, 0x8877665544332211, some 0x11223344) := by rfl
example : (run 1 (resumeAt (request .wakeOne (initial .wakeOne)) (current .wakeOne)
      0xffffffffffffffea 0xabcdef0123456789 0xfedcba9876543210 0x8877665544332211)).map completionView =
    .ok (1, 0xffffffffffffffea, 32776, 12288, 0xabcdef0123456789,
      0xfedcba9876543210, 0x8877665544332211, some 0x11223344) := by rfl

-- Byte admission is strict about syscall, operation, wake count and RET;
-- changing these cannot inherit the independently selected function contract.
example : FutexCertificate.accepts .wait
    [0xb8, 203, 0, 0, 0, 0xbe, 128, 0, 0, 0, 0x0f, 0x05, 0xc3] = false := by decide
example : FutexCertificate.accepts .wait
    [0xb8, 202, 0, 0, 0, 0xbe, 0, 0, 0, 0, 0x0f, 0x05, 0xc3] = false := by decide
example : FutexCertificate.accepts .wakeOne
    [0xb8, 202, 0, 0, 0, 0xbe, 129, 0, 0, 0, 0xba, 2, 0, 0, 0, 0x0f, 0x05, 0xc3] = false := by decide
example : FutexCertificate.accepts .wait
    [0xb8, 202, 0, 0, 0, 0xbe, 128, 0, 0, 0, 0x0f, 0x05, 0x90] = false := by decide

-- Current instruction permissions remain architectural: entry-time code
-- evidence cannot justify RET after its executable permission disappears.
def noRet : Memory :=
  { current .wait with executable := fun address =>
      if address = 4108 then false else (current .wait).executable address }

example : run 1 (resumeAt (request .wait (initial .wait)) noRet 0 0 0 0) =
    .error (.inaccessibleInstruction 4108) := by rfl

end EDSL.Tests.FutexStubs

#audit_edsl
