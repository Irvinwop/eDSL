/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AddressSpace
import EDSL.X86.Memory64

namespace EDSL.OS.AddressSpace
open X86

def qwordRegion (address : Word) : Region := ⟨address, 8⟩

/-- Natural-address cell update, retaining mappedness and permissions.
The eight bytes encode the low-to-high slices of the mathematical word. -/
def writeQWordCells (space : Space) (address : Word) (value : Word) : Space where
  cells query :=
    if (qwordRegion address).Contains query then
      (space.cells query).map fun cell =>
        { cell with byte := value.extractLsb' ((query.toNat - address.toNat) * 8) 8 }
    else space.cells query

/-- Preflight the complete machine operand before updating the OS space.
This is a sequential ordinary-RAM contract, with no concurrent atomicity claim. -/
def storeQWord (space : Space) (address : Word) (value : Word) : Except Fault Space :=
  if canStoreQWord (toMemory space) address then .ok (writeQWordCells space address value)
  else .error .denied

theorem qword_contains_iff (address query : Word)
    (noWrap : address.toNat + 7 < 2^64) :
    (qwordRegion address).Contains query ↔ (query - address).toNat < 8 := by
  constructor
  · intro inside
    have lower : address ≤ query := inside.1
    rw [BitVec.toNat_sub_of_le lower]
    have upper := inside.2
    change query.toNat < address.toNat + 8 at upper
    omega
  · intro offset
    have bound : address.toNat + (query - address).toNat < 2^64 := by omega
    have equality : address + (query - address) = query := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have sum := congrArg BitVec.toNat equality
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt bound] at sum
    change address.toNat ≤ query.toNat ∧ query.toNat < address.toNat + 8
    constructor <;> omega

theorem qword_offset (address query : Word) (inside : (qwordRegion address).Contains query) :
    (query - address).toNat = query.toNat - address.toNat :=
  BitVec.toNat_sub_of_le inside.1

theorem qword_query_of_offset (address query : Word) (offset : Nat)
    (equal : (query - address).toNat = offset) :
    query = address + BitVec.ofNat 64 offset := by
  have difference : query - address = BitVec.ofNat 64 offset := by
    rw [← equal]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (query - address).isLt]
  calc
    query = query - address + address := (BitVec.sub_add_cancel query address).symm
    _ = address + BitVec.ofNat 64 offset := by rw [difference, BitVec.add_comm]

theorem qword_store_readable (space : Space) (address query : Word)
    (allowed : canStoreQWord (toMemory space) address = true)
    (inside : (query - address).toNat < 8) :
    ∃ byte, (toMemory space).read query = some byte := by
  have writable := (Bool.and_eq_true_iff.mp allowed).2
  have mapped := (Bool.and_eq_true_iff.mp writable).2
  simp only [Bool.and_eq_true] at mapped
  rcases mapped with ⟨⟨⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩
  have cases : (query - address).toNat = 0 ∨ (query - address).toNat = 1 ∨
    (query - address).toNat = 2 ∨ (query - address).toNat = 3 ∨
    (query - address).toNat = 4 ∨ (query - address).toNat = 5 ∨
    (query - address).toNat = 6 ∨ (query - address).toNat = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h
  all_goals rw [qword_query_of_offset address query _ h]
  · simpa using Option.isSome_iff_exists.mp b0
  · exact Option.isSome_iff_exists.mp b1
  · exact Option.isSome_iff_exists.mp b2
  · exact Option.isSome_iff_exists.mp b3
  · exact Option.isSome_iff_exists.mp b4
  · exact Option.isSome_iff_exists.mp b5
  · exact Option.isSome_iff_exists.mp b6
  · exact Option.isSome_iff_exists.mp b7

theorem writeQWord_frame (space : Space) (address query : Word) (value : Word)
    (outside : ¬ (qwordRegion address).Contains query) :
    (writeQWordCells space address value).cells query = space.cells query := by
  simp [writeQWordCells, outside]

/-- Permissions and mapping identity survive the cell update even before the
readability premise used by the projection theorem. -/
theorem writeQWord_permissions (space : Space) (address query : Word) (value : Word) :
    ((writeQWordCells space address value).cells query).map Cell.permissions =
      (space.cells query).map Cell.permissions := by
  simp only [writeQWordCells]
  split
  · cases space.cells query <;> rfl
  · rfl

theorem writeQWord_mapped (space : Space) (address query value : Word) :
    ((writeQWordCells space address value).cells query).isSome = (space.cells query).isSome := by
  simp only [writeQWordCells]
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
theorem writeQWord_projects (space : Space) (address : Word) (value : Word)
    (allowed : canStoreQWord (toMemory space) address = true) :
    toMemory (writeQWordCells space address value) =
      X86.writeQWordUnchecked (toMemory space) address value := by
  have valid := (Bool.and_eq_true_iff.mp allowed).1
  have noWrap : address.toNat + 7 < 2^64 := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp valid).1
  apply memory_ext
  · funext query
    by_cases inside : (qwordRegion address).Contains query
    · have offset := (qword_contains_iff address query noWrap).mp inside
      obtain ⟨byte, readable⟩ := qword_store_readable space address query allowed offset
      have lower := inside.1
      have difference := qword_offset address query inside
      have cases : (query - address).toNat = 0 ∨ (query - address).toNat = 1 ∨
        (query - address).toNat = 2 ∨ (query - address).toNat = 3 ∨
        (query - address).toNat = 4 ∨ (query - address).toNat = 5 ∨
        (query - address).toNat = 6 ∨ (query - address).toNat = 7 := by omega
      cases cellAt : space.cells query with
      | none => simp [toMemory, cellAt] at readable
      | some cell =>
        have permission : cell.permissions.readable = true := by
          cases h : cell.permissions.readable <;> simp [toMemory, cellAt, h] at readable ⊢
        rcases cases with h | h | h | h | h | h | h | h <;>
          simp [toMemory, writeQWordCells, inside, cellAt, permission,
            X86.writeQWordUnchecked, storedQWordByte, h, ← difference]
    · have outside : 8 ≤ (query - address).toNat := by
        have notInside : ¬ (query - address).toNat < 8 :=
          fun small => inside ((qword_contains_iff address query noWrap).mpr small)
        omega
      have unchanged := X86.writeQWord_frame (toMemory space) address query value outside
      rw [unchanged]
      simp [toMemory, writeQWordCells, inside]
  · funext query
    by_cases inside : (qwordRegion address).Contains query <;>
      cases cellAt : space.cells query <;>
      simp [toMemory, writeQWordCells, X86.writeQWordUnchecked, inside, cellAt]
  · funext query
    by_cases inside : (qwordRegion address).Contains query <;>
      cases cellAt : space.cells query <;>
      simp [toMemory, writeQWordCells, X86.writeQWordUnchecked, inside, cellAt]

theorem storeQWord_ok (space result : Space) (address : Word) (value : Word)
    (success : storeQWord space address value = .ok result) :
    result = writeQWordCells space address value ∧
      canStoreQWord (toMemory space) address = true := by
  unfold storeQWord at success
  split at success <;> simp_all

theorem storeQWord_success (space : Space) (address : Word) (value : Word)
    (allowed : canStoreQWord (toMemory space) address = true) :
    storeQWord space address value = .ok (writeQWordCells space address value) := by
  simp [storeQWord, allowed]

/-- The same successful store is observed by both models, and readback yields
its mathematical value. No mapped cell or permission is created by the write. -/
theorem storeQWord_sound (space result : Space) (address : Word) (value : Word)
    (success : storeQWord space address value = .ok result) :
    X86.storeQWord (toMemory space) address value = .ok (toMemory result) ∧
    loadQWord (toMemory result) address = .ok value ∧
    (∀ query, (result.cells query).map Cell.permissions =
      (space.cells query).map Cell.permissions) ∧
    (∀ query, ¬ (qwordRegion address).Contains query → result.cells query = space.cells query) := by
  obtain ⟨resultEq, allowed⟩ := storeQWord_ok space result address value success
  subst result
  have projects := writeQWord_projects space address value allowed
  refine ⟨?_, ?_, (fun query => writeQWord_permissions space address query value), ?_⟩
  · rw [projects]
    exact (X86.qword_store_sound (toMemory space) address value allowed).1
  · rw [projects]
    exact (X86.qword_store_sound (toMemory space) address value allowed).2
  · intro query outside
    exact writeQWord_frame space address query value outside

end EDSL.OS.AddressSpace
