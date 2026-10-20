/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.RuntimeInvariant
import EDSL.Audit

namespace EDSL.Tests.FutexAdmission
open X86 OS OS.AddressSpace

/-- Only the actual request instruction is installed here. No fabricated saved
request or service record supplies the admission evidence. -/
def code : AddressSpace.Space where
  cells address := if address = 4096 then some ⟨0x0f, readExecute⟩
    else if address = 4097 then some ⟨0x05, readExecute⟩ else none

def seed : Atomics.State := Atomics.empty (Borrowing.empty (Ownership.empty code))

def context (address : Word) : Threads.Context where
  registers register := if register = .rax then 202 else if register = .rsi then 128
    else if register = .rdi then address else 0
  rip := 4096
  flags := 0

def observedError (attempt : Except OS.Futex.Physical.Fault α) : Option OS.Futex.Physical.Fault :=
  match attempt with | .error fault => some fault | .ok _ => none

def attempt (address : Word) (permissions : Permissions) (interval : OS.Futex.Resources.UserInterval) :
    Except Atomics.Fault (Option OS.Futex.Physical.Fault) := do
  let (mapped, ticket) ← Atomics.mutate seed (.allocate 7 ⟨address, 4⟩ permissions)
  let some ticket := ticket | throw .missingHandle
  let (reserved, keeper) ← Atomics.issue mapped 7 ticket 90 address
  let registration : OS.Futex.Resources.Registration := ⟨7, ticket, 90, address, keeper⟩
  let profile : OS.Futex.Physical.Profile := ⟨⟨0, 90, interval⟩, fun _ => none, fun _ => none⟩
  let state := OS.Futex.Runtime.initial reserved (some registration) [⟨context address, false, []⟩]
  return observedError (OS.Futex.Physical.issue profile state 0)

-- A canonical upper-half word is valid for the machine/resource model, yet
-- cannot enter the configured Linux lower-userspace service profile.
example : attempt 0xffff800000000000 readWrite ⟨4096, 2^47⟩ =
    .ok (some (.service .unsupportedAddress)) := by rfl

-- Full four-byte containment matters; checking only the first byte would
-- admit this aligned word straddling the explicitly supplied interval end.
example : attempt 65536 readWrite ⟨4096, 65538⟩ =
    .ok (some (.service .unsupportedAddress)) := by rfl

-- Executable writable storage has valid ordinary machine write permission,
-- but the fixed futex profile excludes it at actual syscall capture.
example : attempt 65536 ⟨true, true, true⟩ ⟨4096, 2^47⟩ =
    .ok (some (.service .unsupportedAddress)) := by rfl

-- These same actual bytes enter with ordinary aligned non-executable storage.
example : attempt 65536 readWrite ⟨4096, 2^47⟩ = .ok none := by rfl

end EDSL.Tests.FutexAdmission

#audit_edsl
