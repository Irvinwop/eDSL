/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Composition.Core

namespace EDSL.OS.AddressSpace
open X86

def wordRegion (address : Word) : Region := ⟨address, 4⟩

/-- Natural-address cell update, retaining mappedness and permissions.
The four bytes encode the low-to-high slices of the mathematical word. -/
def writeWordCells (space : Space) (address : Word) (value : BitVec 32) : Space where
  cells query :=
    if (wordRegion address).Contains query then
      (space.cells query).map fun cell =>
        { cell with byte := value.extractLsb' ((query.toNat - address.toNat) * 8) 8 }
    else space.cells query

/-- Preflight the complete machine operand before updating the OS space.
This is a sequential ordinary-RAM contract, with no concurrent atomicity claim. -/
def storeWord (space : Space) (address : Word) (value : BitVec 32) : Except Fault Space :=
  if canStoreDWord (toMemory space) address then .ok (writeWordCells space address value)
  else .error .denied

theorem word_contains_iff (address query : Word)
    (noWrap : address.toNat + 3 < 2^64) :
    (wordRegion address).Contains query ↔ (query - address).toNat < 4 := by
  constructor
  · intro inside
    have lower : address ≤ query := inside.1
    rw [BitVec.toNat_sub_of_le lower]
    have upper := inside.2
    change query.toNat < address.toNat + 4 at upper
    omega
  · intro offset
    have bound : address.toNat + (query - address).toNat < 2^64 := by omega
    have equality : address + (query - address) = query := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have sum := congrArg BitVec.toNat equality
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt bound] at sum
    change address.toNat ≤ query.toNat ∧ query.toNat < address.toNat + 4
    constructor <;> omega

theorem word_offset (address query : Word) (inside : (wordRegion address).Contains query) :
    (query - address).toNat = query.toNat - address.toNat :=
  BitVec.toNat_sub_of_le inside.1

theorem query_of_offset (address query : Word) (offset : Nat)
    (equal : (query - address).toNat = offset) :
    query = address + BitVec.ofNat 64 offset := by
  have difference : query - address = BitVec.ofNat 64 offset := by
    rw [← equal]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (query - address).isLt]
  calc
    query = query - address + address := (BitVec.sub_add_cancel query address).symm
    _ = address + BitVec.ofNat 64 offset := by rw [difference, BitVec.add_comm]

theorem store_readable (space : Space) (address query : Word)
    (allowed : canStoreDWord (toMemory space) address = true)
    (inside : (query - address).toNat < 4) :
    ∃ byte, (toMemory space).read query = some byte := by
  have writable := (Bool.and_eq_true_iff.mp allowed).2
  have mapped := (Bool.and_eq_true_iff.mp writable).2
  rcases (Bool.and_eq_true_iff.mp mapped) with ⟨firstThree, last⟩
  rcases (Bool.and_eq_true_iff.mp firstThree) with ⟨firstTwo, third⟩
  rcases (Bool.and_eq_true_iff.mp firstTwo) with ⟨first, second⟩
  have cases : (query - address).toNat = 0 ∨ (query - address).toNat = 1 ∨
    (query - address).toNat = 2 ∨ (query - address).toNat = 3 := by omega
  rcases cases with h | h | h | h
  all_goals rw [query_of_offset address query _ h]
  · simpa using Option.isSome_iff_exists.mp first
  · exact Option.isSome_iff_exists.mp second
  · exact Option.isSome_iff_exists.mp third
  · exact Option.isSome_iff_exists.mp last

theorem writeWord_frame (space : Space) (address query : Word) (value : BitVec 32)
    (outside : ¬ (wordRegion address).Contains query) :
    (writeWordCells space address value).cells query = space.cells query := by
  simp [writeWordCells, outside]

/-- Permissions and mapping identity survive the cell update even before the
readability premise used by the projection theorem. -/
theorem writeWord_permissions (space : Space) (address query : Word) (value : BitVec 32) :
    ((writeWordCells space address value).cells query).map Cell.permissions =
      (space.cells query).map Cell.permissions := by
  simp only [writeWordCells]
  split
  · cases space.cells query <;> rfl
  · rfl

private theorem memory_ext {left right : X86.Memory}
    (reads : left.read = right.read) (executes : left.executable = right.executable)
    (writes : left.writable = right.writable) : left = right := by
  cases left
  cases right
  cases reads
  cases executes
  cases writes
  rfl

/-- Commuting projection: an allowed machine word store has exactly the bytes
and permissions obtained by updating the OS cells through natural addresses. -/
theorem writeWord_projects (space : Space) (address : Word) (value : BitVec 32)
    (allowed : canStoreDWord (toMemory space) address = true) :
    toMemory (writeWordCells space address value) =
      X86.writeDWordUnchecked (toMemory space) address value := by
  have valid := (Bool.and_eq_true_iff.mp allowed).1
  have noWrap : address.toNat + 3 < 2^64 := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp valid).1
  apply memory_ext
  · funext query
    by_cases inside : (wordRegion address).Contains query
    · have offset := (word_contains_iff address query noWrap).mp inside
      obtain ⟨byte, readable⟩ := store_readable space address query allowed offset
      have lower := inside.1
      have difference := word_offset address query inside
      have cases : (query - address).toNat = 0 ∨ (query - address).toNat = 1 ∨
        (query - address).toNat = 2 ∨ (query - address).toNat = 3 := by omega
      cases cellAt : space.cells query with
      | none => simp [toMemory, cellAt] at readable
      | some cell =>
        have permission : cell.permissions.readable = true := by
          cases h : cell.permissions.readable <;> simp [toMemory, cellAt, h] at readable ⊢
        rcases cases with h | h | h | h <;>
          simp [toMemory, writeWordCells, inside, cellAt, permission,
            X86.writeDWordUnchecked, storedDWordByte, h, ← difference]
    · have outside : 4 ≤ (query - address).toNat := by
        have notInside : ¬ (query - address).toNat < 4 :=
          fun small => inside ((word_contains_iff address query noWrap).mpr small)
        omega
      have unchanged := writeDWord_frame (toMemory space) address query value outside
      rw [unchanged]
      simp [toMemory, writeWordCells, inside]
  · funext query
    by_cases inside : (wordRegion address).Contains query <;>
      cases cellAt : space.cells query <;>
      simp [toMemory, writeWordCells, X86.writeDWordUnchecked, inside, cellAt]
  · funext query
    by_cases inside : (wordRegion address).Contains query <;>
      cases cellAt : space.cells query <;>
      simp [toMemory, writeWordCells, X86.writeDWordUnchecked, inside, cellAt]

theorem storeWord_ok (space result : Space) (address : Word) (value : BitVec 32)
    (success : storeWord space address value = .ok result) :
    result = writeWordCells space address value ∧
      canStoreDWord (toMemory space) address = true := by
  unfold storeWord at success
  split at success <;> simp_all

theorem storeWord_success (space : Space) (address : Word) (value : BitVec 32)
    (allowed : canStoreDWord (toMemory space) address = true) :
    storeWord space address value = .ok (writeWordCells space address value) := by
  simp [storeWord, allowed]

/-- The same successful store is observed by both models, and readback yields
its mathematical value. No mapped cell or permission is created by the write. -/
theorem storeWord_sound (space result : Space) (address : Word) (value : BitVec 32)
    (success : storeWord space address value = .ok result) :
    X86.storeDWord (toMemory space) address value = .ok (toMemory result) ∧
    loadDWord (toMemory result) address = .ok value ∧
    (∀ query, (result.cells query).map Cell.permissions =
      (space.cells query).map Cell.permissions) ∧
    (∀ query, ¬ (wordRegion address).Contains query → result.cells query = space.cells query) := by
  obtain ⟨resultEq, allowed⟩ := storeWord_ok space result address value success
  subst result
  have projects := writeWord_projects space address value allowed
  refine ⟨?_, ?_, (fun query => writeWord_permissions space address query value), ?_⟩
  · rw [projects]
    exact (X86.store_sound (toMemory space) address value allowed).1
  · rw [projects]
    exact (X86.store_sound (toMemory space) address value allowed).2
  · intro query outside
    exact writeWord_frame space address query value outside

/-- This final state retains the updated OS resource representation. -/
def storeFinalWithSpace (initial : State) (result : Space) (returnAddress : Word) : State :=
  { initial with
    registers := fun register =>
      if register = .rsp then initial.registers .rsp + 8 else initial.registers register
    rip := returnAddress
    memory := toMemory result }


end EDSL.OS.AddressSpace
