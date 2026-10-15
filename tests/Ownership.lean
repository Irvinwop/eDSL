/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.History
import EDSL.Examples.Compiler.MemoryWitness
import EDSL.Audit

namespace EDSL.Tests.Ownership
open X86 OS.AddressSpace

def failureIs {α : Type} (operation : Except OS.Ownership.Fault α) (expected : OS.Ownership.Fault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

-- Reusing the same address must not restore the old lifetime's authority;
-- the fresh ticket must work and its machine readback must have the new bytes.
def addressReuse : Except OS.Ownership.Fault (Bool × Bool × Except X86.Error (BitVec 32)) := do
  let (first, stale) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 4⟩ readWrite
  let released ← OS.Ownership.release first 7 stale
  let (second, fresh) ← OS.Ownership.allocate released 7 ⟨65536, 4⟩ readWrite
  let stored ← OS.Ownership.storeWord second 7 fresh 65536 0x89abcdef
  return (failureIs (OS.Ownership.storeWord second 7 stale 65536 0x11223344) .missingAllocation,
    failureIs (OS.Ownership.protect second 7 stale readOnly) .missingAllocation,
    loadDWord (toMemory stored.space) 65536)

example : addressReuse = .ok (true, true, .ok 0x89abcdef) := by rfl

def transferBack : Except OS.Ownership.Fault (Bool × Bool × Except X86.Error (BitVec 32)) := do
  let (first, original) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 4⟩ readWrite
  let (other, handed) ← OS.Ownership.transfer first 7 original 8
  let (back, current) ← OS.Ownership.transfer other 8 handed 7
  let stored ← OS.Ownership.storeWord back 7 current 65536 0x11223344
  return (failureIs (OS.Ownership.storeWord back 7 original 65536 0) .staleEpoch,
    failureIs (OS.Ownership.release back 7 handed) .staleEpoch,
    loadDWord (toMemory stored.space) 65536)

example : transferBack = .ok (true, true, .ok 0x11223344) := by rfl

def selfTransfer : Except OS.Ownership.Fault Bool := do
  let (first, original) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 4⟩ readWrite
  let (second, _) ← OS.Ownership.transfer first 7 original 7
  return failureIs (OS.Ownership.release second 7 original) .staleEpoch

example : selfTransfer = .ok true := by rfl

-- Both regions are writable and share the same owner. The boundary must still
-- reject a four-byte operand crossing from the first resource into the second.
def adjacent : Except OS.Ownership.Fault (Bool × Bool × Option Byte × Except X86.Error (BitVec 32)) := do
  let (left, a) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 8⟩ readWrite
  let (both, _) ← OS.Ownership.allocate left 7 ⟨65544, 4⟩ readWrite
  let stored ← OS.Ownership.storeWord both 7 a 65540 0x89abcdef
  return (canStoreDWord (toMemory both.space) 65542,
    failureIs (OS.Ownership.storeWord both 7 a 65542 0x11223344) .outsideAllocation,
    (toMemory stored.space).read 65544, loadDWord (toMemory stored.space) 65540)

example : adjacent = .ok (true, true, some 0, .ok 0x89abcdef) := by rfl

def hiddenAdoption : Except OS.Ownership.Fault (Bool × Bool × Except X86.Error (BitVec 32)) := do
  let space ← (OS.AddressSpace.map OS.AddressSpace.empty ⟨65536, 4⟩ readWrite).mapError OS.Ownership.Fault.addressSpace
  let populated ← (OS.AddressSpace.storeWord space 65536 0x11223344).mapError OS.Ownership.Fault.addressSpace
  let hidden ← (OS.AddressSpace.protect populated ⟨65536, 4⟩ inaccessible).mapError OS.Ownership.Fault.addressSpace
  let (owned, ticket) ← OS.Ownership.adopt (OS.Ownership.empty hidden) 7 ⟨65536, 4⟩
  let readable ← OS.Ownership.protect owned 7 ticket readOnly
  return (failureIs (OS.Ownership.storeWord owned 7 ticket 65536 0) (.addressSpace .denied),
    failureIs (OS.Ownership.storeWord readable 7 ticket 65536 0) (.addressSpace .denied),
    loadDWord (toMemory readable.space) 65536)

example : hiddenAdoption = .ok (true, true, .ok 0x11223344) := by rfl

def adoptionOverlap : Except OS.Ownership.Fault (Bool × Bool × Bool) := do
  let backing ← (OS.AddressSpace.map OS.AddressSpace.empty ⟨65536, 16⟩ readWrite).mapError OS.Ownership.Fault.addressSpace
  let (first, _) ← OS.Ownership.adopt (OS.Ownership.empty backing) 7 ⟨65536, 4⟩
  let (second, _) ← OS.Ownership.adopt first 8 ⟨65544, 4⟩
  return (failureIs (OS.Ownership.adopt second 9 ⟨65543, 2⟩) .claimedRegion,
    failureIs (OS.Ownership.adopt second 9 ⟨65539, 2⟩) .claimedRegion,
    failureIs (OS.Ownership.adopt second 9 ⟨65548, 5⟩) (.addressSpace .notMapped))

example : adoptionOverlap = .ok (true, true, true) := by rfl

def ownerMismatch : Except OS.Ownership.Fault (Bool × Bool) := do
  let (owned, ticket) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 4⟩ readWrite
  return (failureIs (OS.Ownership.storeWord owned 8 ticket 65536 0) .wrongOwner,
    failureIs (OS.Ownership.protect owned 7 ticket ⟨false, true, false⟩) (.addressSpace .unsupportedPermissions))

example : ownerMismatch = .ok (true, true) := by rfl

-- Actual store bytes with arbitrary prior data and a 64-bit source argument.
-- Adoption leaves caller code/stack bytes intact; owned execution must update
-- the same OS cells as the machine store, for every old/new value.
open Examples.Compiler.MemoryOps

def caller (old : BitVec 32) : Space where
  cells address := ((dataMemory 0x89 0x37 old).read address).map fun byte =>
    ⟨byte, ⟨true, (dataMemory 0x89 0x37 old).writable address,
      (dataMemory 0x89 0x37 old).executable address⟩⟩

def owned (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (caller old)) (caller old) 7 ⟨65536, 4⟩

theorem adopted (old : BitVec 32) :
    OS.Ownership.adopt (OS.Ownership.empty (caller old)) 7 ⟨65536, 4⟩ = .ok (owned old, ⟨0, 0⟩) := by
  apply OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) ?_ (by rfl)
  change allMapped (caller old) ⟨65536, 4⟩ = true
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨offset, bound, same⟩ := List.mem_map.mp member
  have small : offset < 4 := List.mem_range.mp bound
  subst address
  match offset with
  | 0 | 1 | 2 | 3 => rfl
  | offset + 4 => omega

theorem owned_valid (old : BitVec 32) : OS.Ownership.WellFormed (owned old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) (adopted old)).1

theorem caller_code (old : BitVec 32) : CodeAt (toMemory (caller old)) 4096 storeBytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  match offset with
  | 0 | 1 | 2 =>
    simp [storeBytes] at present
    subst byte
    rfl
  | offset + 3 => simp [storeBytes] at present

def stored (old : BitVec 32) (value : Word) : OS.Ownership.World :=
  { owned old with space := writeWordCells (caller old) 65536 (value.setWidth 32) }

theorem owned_store (old : BitVec 32) (value : Word) :
    OS.Ownership.storeWord (owned old) 7 ⟨0, 0⟩ 65536 (value.setWidth 32) = .ok (stored old value) := by
  have permitted : canStoreDWord (toMemory (caller old)) 65536 = true := by
    simp [canStoreDWord, dwordAddressable, dwordWritable, toMemory, caller,
      dataMemory, writeDWordUnchecked, storedDWordByte, baseMemory, canonical]
  have authority : OS.Ownership.authorize (owned old) 7 ⟨0, 0⟩ = .ok ⟨7, 0, ⟨65536, 4⟩⟩ := by rfl
  have rawStore := OS.AddressSpace.storeWord_success (caller old) 65536 (value.setWidth 32) permitted
  simp only [BitVec.ofNat_eq_ofNat] at rawStore
  simp only [OS.Ownership.storeWord, authority, ok_bind]
  change (do
    if !OS.Ownership.containsWord ⟨7, 0, ⟨65536, 4⟩⟩ 65536 then throw OS.Ownership.Fault.outsideAllocation
    let space ← (OS.AddressSpace.storeWord (caller old) 65536 (value.setWidth 32)).mapError OS.Ownership.Fault.addressSpace
    pure { owned old with space := space }) = .ok (stored old value)
  simp [OS.Ownership.containsWord, rawStore, Except.mapError, stored]

def binaryEntry (old : BitVec 32) (value : Word) : State :=
  { storeEntry old value with memory := toMemory (caller old) }

theorem all_values_owned_binary (old : BitVec 32) (value : Word) :
    OS.Ownership.WellFormed (stored old value) ∧
    Executes (binaryEntry old value)
      (storeFinalWithSpace (binaryEntry old value) (stored old value).space 8192) 2 := by
  refine ⟨(OS.Ownership.storeWord_wellFormed _ _ _ _ _ _ (owned_valid old) (owned_store old value)).1, ?_⟩
  apply (OS.Ownership.owned_store32_correct (owned old) 7 ⟨0, 0⟩ (stored old value)
    (storeEntry old value) 8192 (owned_store old value) (caller_code old)
    data_code_disjoint data_stack_disjoint ?_ (by decide)).1
  change readWord (toMemory (caller old)) 32768 = .ok 8192
  simp [readWord, readStackByte, toMemory, caller,
    dataMemory, writeDWordUnchecked, storedDWordByte, baseMemory, canonical]

end EDSL.Tests.Ownership

#audit_edsl
