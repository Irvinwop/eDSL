/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AddressSpace
import EDSL.Audit

namespace EDSL.Tests.AddressSpace
open X86 OS.AddressSpace

def data : Region := ⟨65536, 4⟩
def neighbor : Region := ⟨65540, 1⟩

/-- Entire lifecycle through checked operations; no unchecked state construction. -/
def lifecycle : Except Fault (Option Byte × Option Byte × Option Byte × Option Byte) := do
  let mapped ← map empty data readWrite
  let mapped ← map mapped neighbor readWrite
  let filled ← writeByte mapped 65536 0x3d
  let filled ← writeByte filled 65539 0x92
  let filled ← writeByte filled 65540 0xb7
  let readProtected ← protect filled data readOnly
  let hidden ← protect readProtected data inaccessible
  let restored ← protect hidden data readOnly
  let removed ← unmap restored data
  let remapped ← map removed data readWrite
  return ((toMemory readProtected).read 65536, (toMemory restored).read 65539,
    (toMemory remapped).read 65536, (toMemory remapped).read 65540)

-- Read/write protection changes preserve hidden data; fresh remapping is zeroed;
-- an immediately adjacent mapping retains its independent value.
example : lifecycle = .ok (some 0x3d, some 0x92, some 0, some 0xb7) := by rfl

def deniedWrite : Except Fault Space := do
  let mapped ← map empty data readWrite
  let readProtected ← protect mapped data readOnly
  writeByte readProtected 65539 0x7b

example : deniedWrite = .error .denied := by rfl

-- Machine operations must observe revoked OS permissions, including fetch.
def revoked : Except Fault (Except X86.Error Byte × Except X86.Error X86.Memory) := do
  let mapped ← map empty data readExecute
  let hidden ← protect mapped data inaccessible
  return (fetchByte (toMemory hidden) 65536, storeDWord (toMemory hidden) 65536 0x11223344)

example : (revoked.map fun result => result.1) = .ok (.error (.inaccessibleInstruction 65536)) := by rfl
example : (revoked.map fun result => result.2) = .ok (.error (.writeDenied 65536)) := by rfl

def overlapRejected : Except Fault Space := do
  let mapped ← map empty data readWrite
  map mapped ⟨65539, 2⟩ readWrite

example : overlapRejected = .error .overlap := by rfl

def protectHole : Except Fault Space := do
  let mapped ← map empty ⟨65536, 3⟩ readWrite
  protect mapped data readOnly

example : protectHole = .error .notMapped := by rfl

def unmapHole : Except Fault Space := do
  let mapped ← map empty ⟨65536, 3⟩ readWrite
  unmap mapped data

example : unmapHole = .error .notMapped := by rfl

-- Empty, wrapping and canonical-gap-spanning requests are invalid.
example : map empty ⟨65536, 0⟩ readWrite = .error .invalidRegion := by rfl
example : map empty ⟨0xffffffffffffffff, 2⟩ readWrite = .error .invalidRegion := by rfl
example : map empty ⟨0x7fffffffffff, 2⟩ readWrite = .error .invalidRegion := by rfl

-- The projection cannot implement execute-only memory, so it must reject it.
example : map empty data ⟨false, false, true⟩ = .error .unsupportedPermissions := by rfl

end EDSL.Tests.AddressSpace

#audit_edsl
