/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordStore
import EDSL.Examples.Compiler.MemoryWitness
import EDSL.Audit

namespace EDSL.Tests.WordStore
open X86 OS.AddressSpace Examples.Compiler.MemoryOps

/-- The actual store binary, a return stack, writable data and two guard cells. -/
def space (oldValue : BitVec 32) : Space where
  cells address :=
    if address = 65535 ∨ address = 65540 then some ⟨0xa5, readWrite⟩ else
    ((dataMemory 0x89 0x37 oldValue).read address).map fun byte =>
      ⟨byte, ⟨true, (dataMemory 0x89 0x37 oldValue).writable address,
        (dataMemory 0x89 0x37 oldValue).executable address⟩⟩

theorem code (oldValue : BitVec 32) : CodeAt (toMemory (space oldValue)) 4096 storeBytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte atOffset
  match offset with
  | 0 | 1 | 2 =>
    simp [storeBytes] at atOffset
    subst byte
    rfl
  | n + 3 => simp [storeBytes] at atOffset

def updated (oldValue : BitVec 32) (value : Word) : Space :=
  writeWordCells (space oldValue) 65536 (value.setWidth 32)

def entry (oldValue : BitVec 32) (value : Word) : State :=
  { storeEntry oldValue value with memory := toMemory (space oldValue) }

/-- All old data and 64-bit arguments admit the cross-layer store contract. -/
theorem every_store_updates_cells (oldValue : BitVec 32) (value : Word) :
    Executes (entry oldValue value)
      (storeFinalWithSpace (entry oldValue value) (updated oldValue value) 8192) 2 := by
  apply (store32_updates_space (space oldValue) (updated oldValue value)
    (storeEntry oldValue value) 8192 ?_ (code oldValue)
    data_code_disjoint data_stack_disjoint ?_ (by decide)).1
  · change storeWord (space oldValue) 65536 (value.setWidth 32) = .ok (updated oldValue value)
    apply storeWord_success
    simp [canStoreDWord, dwordAddressable, dwordWritable, toMemory, space,
      dataMemory, writeDWordUnchecked, storedDWordByte, baseMemory, canonical]
  · change readWord (toMemory (space oldValue)) 32768 = .ok 8192
    simp [readWord, readStackByte, toMemory, space, dataMemory,
      writeDWordUnchecked, storedDWordByte, baseMemory, canonical]

/-- Observe the OS state only after a checked store and permission lifecycle. -/
def lifecycle : Except Fault (Except X86.Error (BitVec 32) × Option Byte × Option Byte) := do
  let stored ← storeWord (space 0xa5a5a5a5) 65536 0x89abcdef
  let hidden ← protect stored ⟨65536, 4⟩ inaccessible
  let restored ← protect hidden ⟨65536, 4⟩ readOnly
  return (loadDWord (toMemory restored) 65536,
    (toMemory restored).read 65535, (toMemory restored).read 65540)

-- Catches stale cell contents, byte-order mistakes and changes to neighboring cells.
example : lifecycle = .ok (.ok 0x89abcdef, some 0xa5, some 0xa5) := by rfl

-- High source-register bits do not enter the 32-bit OS update.
example : (run 2 (entry 0xa5a5a5a5 0xfeedface89abcdef)).map
    (fun result => result.state.memory.read 65539) = .ok (some 0x89) := by rfl

-- Updating a mapped but inaccessible cell or any denied byte must fail preflight.
example : storeWord (protectUnchecked (space 0) ⟨65539, 1⟩ readOnly) 65536 0x11223344 =
    .error .denied := by rfl

example : storeWord (protectUnchecked (space 0) ⟨65539, 1⟩ inaccessible) 65536 0x11223344 =
    .error .denied := by rfl

-- Unmapped and wrapped operands are rejected before any cell update is returned.
example : storeWord (unmapUnchecked (space 0) ⟨65539, 1⟩) 65536 0x11223344 =
    .error .denied := by rfl

example : storeWord (space 0) 0xffffffffffffffff 0x11223344 = .error .denied := by rfl

end EDSL.Tests.WordStore

#audit_edsl
