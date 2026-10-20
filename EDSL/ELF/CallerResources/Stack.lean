/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.CallerResources

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.ELF.CallerResources.Stack
open X86 OS OS.AddressSpace

def region (stack : Word) : Region := ⟨stack, 8⟩

/-- Exactly the abstract return slot, with read-only little-endian bytes.
This declares current modeled cells, not native authority or allocated pages.
Invalid intervals do not acquire validity through this construction. -/
def prior (stack returnAddress : Word) : Space where
  cells address := if (region stack).Contains address then
    some ⟨returnAddress.extractLsb' ((address.toNat - stack.toNat) * 8) 8, readOnly⟩
    else none

def caller (codeOwner callerOwner worker : Nat) (stack returnAddress : Word) : Caller :=
  ⟨prior stack returnAddress, codeOwner, callerOwner, worker, stack, returnAddress⟩

theorem cells_inside (stack returnAddress address : Word)
    (inside : (region stack).Contains address) :
    (prior stack returnAddress).cells address =
      some ⟨returnAddress.extractLsb' ((address.toNat - stack.toNat) * 8) 8, readOnly⟩ := by
  simp only [prior, ite_eq_left inside]

theorem cells_outside (stack returnAddress address : Word)
    (outside : ¬(region stack).Contains address) :
    (prior stack returnAddress).cells address = none := by
  simp only [prior, ite_eq_right outside]

private theorem offset_inside (stack : Word) (valid : (region stack).valid = true)
    (offset : Nat) (bound : offset < 8) :
    (region stack).Contains (stack + BitVec.ofNat 64 offset) :=
  Ownership.addresses_inside _ valid _
    (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)

theorem read_byte (stack returnAddress : Word) (valid : (region stack).valid = true)
    (offset : Nat) (bound : offset < 8) :
    (toMemory (prior stack returnAddress)).read (stack + BitVec.ofNat 64 offset) =
      some (returnAddress.extractLsb' (offset * 8) 8) := by
  have extent : stack.toNat + 8 ≤ 2^64 := (of_decide_eq_true valid).2.1
  have small : offset < 2^64 := by omega
  have total : stack.toNat + offset < 2^64 := by omega
  simp only [toMemory, cells_inside _ _ _ (offset_inside stack valid offset bound),
    readOnly, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt total, Nat.add_sub_cancel_left]
  rfl

theorem read_stack_byte (stack returnAddress : Word)
    (valid : (region stack).valid = true) (offset : Nat) (bound : offset < 8) :
    readStackByte (toMemory (prior stack returnAddress)) (stack + BitVec.ofNat 64 offset) =
      .ok (returnAddress.extractLsb' (offset * 8) 8) := by
  have canon := valid_contains_canonical _ valid _ (offset_inside stack valid offset bound)
  simp only [readStackByte, canon, ↓reduceIte, read_byte stack returnAddress valid offset bound]

/-- Complete RET read for every input word, without an execution/result premise. -/
theorem read_word (stack returnAddress : Word) (valid : (region stack).valid = true) :
    readWord (toMemory (prior stack returnAddress)) stack = .ok returnAddress := by
  have extent : stack.toNat + 8 ≤ 2^64 := (of_decide_eq_true valid).2.1
  have noWrap : ¬stack.toNat + 7 ≥ 2^64 := by omega
  have b0 := read_stack_byte stack returnAddress valid 0 (by decide)
  have b1 := read_stack_byte stack returnAddress valid 1 (by decide)
  have b2 := read_stack_byte stack returnAddress valid 2 (by decide)
  have b3 := read_stack_byte stack returnAddress valid 3 (by decide)
  have b4 := read_stack_byte stack returnAddress valid 4 (by decide)
  have b5 := read_stack_byte stack returnAddress valid 5 (by decide)
  have b6 := read_stack_byte stack returnAddress valid 6 (by decide)
  have b7 := read_stack_byte stack returnAddress valid 7 (by decide)
  simp only [BitVec.add_zero] at b0
  simp only [readWord, ite_eq_right noWrap, BitVec.ofNat_eq_ofNat,
    b0, b1, b2, b3, b4, b5, b6, b7, ok_bind, pure_ok]
  exact congrArg Except.ok (qword_join_extracts returnAddress)

theorem readable (stack returnAddress : Word) (valid : (region stack).valid = true) :
    Borrowing.allReadable (prior stack returnAddress) (region stack) = true := by
  apply CallResources.Domain.allReadable_of_cells _ _ valid
  intro address inside
  exact ⟨_, cells_inside stack returnAddress address inside, rfl⟩

/-- All environmental side conditions remain explicit. No native ownership or
authentication follows from the proof-level IDs. -/
theorem facts (codeOwner callerOwner worker : Nat) (stack returnAddress : Word)
    (valid : (region stack).valid = true) (returnCanonical : canonical returnAddress = true)
    (stackBound : stack.toNat + 8 < 2^64) (postStackCanonical : canonical (stack + 8) = true) :
    (caller codeOwner callerOwner worker stack returnAddress).Facts :=
  ⟨valid, readable stack returnAddress valid, read_word stack returnAddress valid,
    returnCanonical, stackBound, postStackCanonical⟩

theorem allUnmapped_of_disjoint (stack returnAddress : Word) (pages : Region)
    (valid : pages.valid = true) (separate : Ownership.Disjoint pages (region stack)) :
    allUnmapped (prior stack returnAddress) pages = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside pages valid address member
  have outside := Ownership.disjoint_outside (Ownership.disjoint_symm separate) inside
  simp only [cells_outside stack returnAddress address outside, Option.isNone_none]

/-- A sufficient interval check for the existing rounded-page freshness check.
It checks no page bytes and makes no ELF-validity or allocation claim. -/
def check (image : ELF.Image) (stack : Word) : Bool :=
  (region stack).valid && image.segments.all fun segment =>
    segment.pageRegion.valid && decide (Ownership.Disjoint segment.pageRegion (region stack))

/-- Success proves the original freshness predicate, with no fallback. Function
separation is still an explicit premise of `CallerResources.initial_facts`. -/
theorem check_sound (image : ELF.Image) (stack returnAddress : Word)
    (checked : check image stack = true) : ELF.fresh image (prior stack returnAddress) = true := by
  have segments := (Bool.and_eq_true_iff.mp checked).2
  apply List.all_eq_true.mpr
  intro segment member
  have parts := Bool.and_eq_true_iff.mp (List.all_eq_true.mp segments segment member)
  exact allUnmapped_of_disjoint stack returnAddress segment.pageRegion parts.1
    (of_decide_eq_true parts.2)

/-- Useful witness defaults, imposing no restriction on other current callers. -/
def standard : Caller := caller 101 202 303 0x700008 0x654321

theorem standard_facts : standard.Facts :=
  facts 101 202 303 0x700008 0x654321 (by decide) (by decide) (by decide) (by decide)

end EDSL.ELF.CallerResources.Stack
