/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Process.Certificate
import EDSL.Examples.Compiler.Increment
import EDSL.Audit

namespace EDSL.Tests.Process
open X86 Examples.Compiler

def codeMemory (bytes : List Byte) : Memory where
  read address := if 4096 ≤ address.toNat then bytes[address.toNat - 4096]? else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)

def startup (registers : Register → Word) (flags : Word) : State :=
  ⟨registers, 4096, flags, codeMemory Exit42.bytes⟩

theorem exit_code : CodeAt (codeMemory Exit42.bytes) 4096 Exit42.bytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte atOffset
  match offset with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 =>
    simp [Exit42.bytes] at atOffset
    subst byte
    rfl
  | n + 12 => simp [Exit42.bytes] at atOffset

/-- Nonvacuity for every initial register/flags choice, with no stack mapping. -/
theorem all_startup_values_reach_exit (registers : Register → Word) (flags : Word) :
    Invokes (startup registers flags) (Exit42.request (startup registers flags)) 3 :=
  (Exit42.reaches_request (startup registers flags) exit_code).1

def entry : State := startup (fun register =>
  if register = .rsp then 0x800000000000 else 0xfeedface00000000) 0x202

-- The stack is unmapped and its register is noncanonical: these bytes do not
-- use it. Check the number, full argument, continuation and exact user cost.
example : (runToSyscall 3 entry).toOption.map (fun result =>
    (result.request.number, result.request.argument .first, result.request.continuation, result.instructions)) =
    some (60, 42, 4108, 3) := by decide

example : runToSyscall 2 entry = .error .exhaustedFuel := by rfl
example : run 3 entry = .error .syscallBoundary := by rfl
example : runToSyscall 2 (Increment.witnessEntry 0) = .error .unexpectedReturn := by rfl

-- A generic immediate with bit 31 set must zero-extend, even though the exit42
-- fixture uses small positive immediates and cannot expose this width defect.
def largeImmediate : State := { entry with memory := codeMemory [0xb8, 0xff, 0xff, 0xff, 0xff, 0x0f, 0x05] }

example : (runToSyscall 2 largeImmediate).toOption.map
    (fun result => result.request.user.registers .rax) = some 0x00000000ffffffff := by decide

-- Linux ABI oracle: fourth argument is R10, not RCX; dispatch/exit status use
-- their specified low bits rather than accidental whole-register equality.
def abiRequest : SyscallRequest :=
  ⟨{ entry with registers := fun register =>
    if register = .rax then 0xdeadbeef0000003c
    else if register = .rdi then 0xffff00000000012a
    else if register = .rcx then 0x3333
    else if register = .r10 then 0x4444 else 0 }, 0⟩

example : abiRequest.argument .fourth = 0x4444 := by rfl
example : abiRequest.number = 60 := by rfl
example : OS.LinuxExit.status abiRequest = 42 := by rfl

end EDSL.Tests.Process

#audit_edsl
