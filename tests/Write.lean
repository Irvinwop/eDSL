/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Process.WriteExit
import EDSL.Audit

namespace EDSL.Tests.Write
open X86 Examples.Compiler

def memory : Memory where
  read address := if 0x400000 ≤ address.toNat then
    WriteExit.bytes[address.toNat - 0x400000]? else none
  executable address := decide (0x400000 ≤ address.toNat ∧ address.toNat < 0x400025)

def startup : State := ⟨fun _ => 0xaaaaaaaaaaaaaaaa, 0x400000, 0x202, memory⟩

-- Decode a real entry through its first syscall. Independent ABI expectations
-- catch swapped RSI/RDX destinations, wrong immediates and continuation length.
example : (runToSyscall 5 startup).toOption.map (fun result =>
    (result.request.number, result.request.argument .first,
     result.request.argument .second, result.request.argument .third,
     result.request.continuation, result.instructions)) =
    some (1, 1, 0x400022, 3, 0x400016, 5) := by decide

def returned (outcome : OS.LinuxWrite.Outcome) : State :=
  resume (WriteExit.request startup) (OS.LinuxWrite.rawResult outcome)
    0xdeadbeef 0xbadbadbad 0xfaded

-- Partial success and a negative raw error must both reach exit42. In
-- particular the write result must not accidentally select the next syscall.
example : (runToSyscall 3 (returned (.accepted 1))).toOption.map (fun result =>
    (result.request.number, result.request.argument .first, result.instructions)) =
    some (60, 42, 3) := by decide

example : (runToSyscall 3 (returned (.failed OS.LinuxWrite.eintr))).toOption.map
    (fun result => (result.request.number, result.request.argument .first)) =
    some (60, 42) := by decide

-- A short transfer reports precisely the accepted prefix, not the remainder
-- or the whole requested buffer. Oversized return counts must be inadmissible.
example : OS.LinuxWrite.emitted WriteExit.payload (.accepted 1) = [0x4f] := by decide
example : ¬ OS.LinuxWrite.Permitted WriteExit.payload (.accepted 4) := by decide
example : OS.LinuxWrite.emitted WriteExit.payload (.failed OS.LinuxWrite.eagain) = [] := by rfl
example : (OS.LinuxWrite.rawResult (.failed OS.LinuxWrite.eagain)).toInt = -11 := by decide

-- Reading the passed buffer exercises actual memory addressing and fails
-- when permissions/bytes are absent, independently of syscall result choice.
example : readDataByte memory 0x400022 = .ok 0x4f := by rfl
example : readDataByte memory 0x400025 = .error (.inaccessibleData 0x400025) := by rfl

end EDSL.Tests.Write

#audit_edsl
