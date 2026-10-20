/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Compiler.MemoryWitness
import EDSL.Audit

namespace EDSL.Tests.Memory
open X86 Examples.Compiler.MemoryOps

/-- Independent little-endian byte layout, with read permission but no writes. -/
def readOnly : X86.Memory where
  read address :=
    match address.toNat with
    | 65536 => some 0x44
    | 65537 => some 0x33
    | 65538 => some 0x22
    | 65539 => some 0x11
    | _ => none
  executable := fun _ => false

example : loadDWord readOnly 65536 = .ok 0x11223344 := by rfl

def observeStoredByte (initial : State) (address : Word) : Except Error (Option Byte) := do
  let completed ← run 2 initial
  return completed.state.memory.read address

-- Full instruction execution, high RSI bits ignored, and independently defined
-- byte-order expectations catch wrong width, endian order and source register.
example : observeStoredByte (storeEntry 0xa5a5a5a5 0xfeedface89abcdef) 65536 = .ok (some 0xef) := by rfl
example : observeStoredByte (storeEntry 0xa5a5a5a5 0xfeedface89abcdef) 65537 = .ok (some 0xcd) := by rfl
example : observeStoredByte (storeEntry 0xa5a5a5a5 0xfeedface89abcdef) 65538 = .ok (some 0xab) := by rfl
example : observeStoredByte (storeEntry 0xa5a5a5a5 0xfeedface89abcdef) 65539 = .ok (some 0x89) := by rfl

def denied : State :=
  let entry := storeEntry 0xa5a5a5a5 0x11223344
  { entry with memory := { entry.memory with writable := fun _ => false } }

example : run 2 denied = .error (.writeDenied 65536) := by rfl

def lastByteDenied : State :=
  let entry := storeEntry 0xa5a5a5a5 0x11223344
  { entry with memory := { entry.memory with writable := fun address => decide (address ≠ 65539) } }

example : run 2 lastByteDenied = .error (.writeDenied 65536) := by rfl

/-- Write permission alone does not authorize creating an unmapped byte. -/
def lastByteUnmapped : State :=
  let entry := storeEntry 0xa5a5a5a5 0x11223344
  { entry with memory := { entry.memory with
      read := fun address => if address = 65539 then none else entry.memory.read address } }

example : run 2 lastByteUnmapped = .error (.writeDenied 65536) := by rfl

def fullMemory : X86.Memory where
  read := fun _ => some 0xa5
  executable := fun _ => false
  writable := fun _ => true

example : loadDWord fullMemory 0xffffffffffffffff =
    .error (.inaccessibleData 0xffffffffffffffff) := by rfl

example : loadDWord fullMemory 0x7ffffffffffe =
    .error (.inaccessibleData 0x800000000000) := by rfl

end EDSL.Tests.Memory

#audit_edsl
