/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.History

set_option warningAsError true

namespace EDSL.OS.CallMemory64
open X86 AddressSpace

/-- A wholly contained private operand inherits the current frame's valid
natural interval, including the canonical-address and nonwrapping bounds. -/
theorem Contract.private_valid {descriptor : Descriptor} {shared : Shared}
    {location : Word} (contract : Contract descriptor shared)
    (slot : StackFrame.Slot descriptor.frame location) :
    (qwordRegion location).valid = true := by
  have valid := of_decide_eq_true contract.stack.region_valid
  have fits : descriptor.frame.region.base.toNat ≤ location.toNat ∧
      location.toNat + 8 ≤
        descriptor.frame.region.base.toNat + descriptor.frame.region.length := slot
  apply decide_eq_true
  change 0 < 8 ∧ location.toNat + 8 ≤ 2^64 ∧
    (location.toNat + 8 ≤ 2^47 ∨ 2^64 - 2^47 ≤ location.toNat)
  omega

private theorem qword_byte_inside {location : Word}
    (valid : (qwordRegion location).valid = true) (offset : Nat) (bound : offset < 8) :
    (qwordRegion location).Contains (location + BitVec.ofNat 64 offset) :=
  Ownership.addresses_inside _ valid _
    (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)

/-- Exact cell identity, including all permissions, on the entire private
allocation after a DATA store. Separation comes from the current capabilities. -/
theorem data_preserves_private_cells {descriptor : Descriptor} {before after : Shared}
    {value : Word} (contract : Contract descriptor before)
    (effect : Borrowing.StoreEffect64 before after descriptor.target value)
    (query : Word) (inside : descriptor.frame.region.Contains query) :
    after.resources.space.cells query = before.resources.space.cells query :=
  effect.outside query (fun data => contract.target_outside_private data inside)

/-- A checked store's exact effect retains a protected word only when its whole
operand is disjoint. Different starting addresses alone do not suffice. -/
theorem store64_preserves_disjoint_cells {before after : Shared} {address value location : Word}
    (effect : Borrowing.StoreEffect64 before after address value)
    (separate : Ownership.Disjoint (qwordRegion address) (qwordRegion location))
    (query : Word) (inside : (qwordRegion location).Contains query) :
    after.resources.space.cells query = before.resources.space.cells query :=
  effect.outside query (Ownership.disjoint_outside separate inside)

private theorem private_read_congr {descriptor : Descriptor} {before after : Shared}
    {initial final : X86.State} {location : Word}
    (first : Current descriptor before initial) (last : Current descriptor after final)
    (slot : StackFrame.Slot descriptor.frame location)
    (cells : ∀ query, (qwordRegion location).Contains query →
      after.resources.space.cells query = before.resources.space.cells query) :
    readWord final.memory location = readWord initial.memory location := by
  rw [first.coupled, last.coupled]
  apply readWord_congr
  apply AddressSpace.agrees_read
  intro offset bound
  exact cells _ (qword_byte_inside (first.contract.private_valid slot) offset bound)

/-- Public DATA/private framing at the actual coupled endpoints. The saved
contents may be arbitrary full64 values; no immutable private-stack premise is used. -/
theorem data_preserves_private {descriptor : Descriptor} {before after : Shared}
    {initial final : X86.State} {value location : Word}
    (first : Current descriptor before initial) (last : Current descriptor after final)
    (effect : Borrowing.StoreEffect64 before after descriptor.target value)
    (slot : StackFrame.Slot descriptor.frame location) :
    readWord final.memory location = readWord initial.memory location :=
  private_read_congr first last slot (fun query inside =>
    data_preserves_private_cells first.contract effect query (Borrowing.subregion_inside slot inside))

/-- In particular, another private-slot store preserves the current saved word
when their entire eight-byte operands are disjoint. -/
theorem store64_preserves_private {descriptor : Descriptor} {before after : Shared}
    {initial final : X86.State} {address value location : Word}
    (first : Current descriptor before initial) (last : Current descriptor after final)
    (effect : Borrowing.StoreEffect64 before after address value)
    (slot : StackFrame.Slot descriptor.frame location)
    (separate : Ownership.Disjoint (qwordRegion address) (qwordRegion location)) :
    readWord final.memory location = readWord initial.memory location :=
  private_read_congr first last slot (store64_preserves_disjoint_cells effect separate)

/-- DATA writes automatically miss private slots by current allocation
separation. A private write must explicitly exclude the protected whole word. -/
inductive Write.Excludes {descriptor : Descriptor} (location : Word) :
    {before after : Shared} → Write descriptor before after → Prop where
  | data {before after value}
      (success : Borrowing.mutate before
        (.store64 descriptor.owner descriptor.ticket descriptor.target value) = .ok (after, none)) :
      Write.Excludes location (.data success)
  | privateSlot {before after address value} (slot : StackFrame.Slot descriptor.frame address)
      (success : Borrowing.mutate before
        (.store64 descriptor.owner descriptor.frame.ticket address value) = .ok (after, none))
      (separate : Ownership.Disjoint (qwordRegion address) (qwordRegion location)) :
      Write.Excludes location (.privateSlot slot success)

/-- Per-slot exclusion throughout an explicit checked mixed write history.
There is no length bound; different saved slots may use different exclusions. -/
inductive History.Excludes {descriptor : Descriptor} (location : Word) :
    {before after : Shared} → History descriptor before after → Prop where
  | refl {shared} : History.Excludes location (.refl (shared := shared))
  | next {before middle after} {first : Write descriptor before middle}
      {tail : History descriptor middle after}
      (head : first.Excludes location) (rest : tail.Excludes location) :
      History.Excludes location (.next first tail)

theorem History.excludes_trans {descriptor : Descriptor} {a b c : Shared} {location : Word}
    (first : History descriptor a b) (last : History descriptor b c)
    (left : first.Excludes location) (right : last.Excludes location) :
    (first.trans last).Excludes location := by
  induction left with
  | refl => exact right
  | next head _ ih => exact .next head (ih last right)

theorem Write.preserves_private_cells {descriptor : Descriptor} {before after : Shared}
    {location : Word} (write : Write descriptor before after)
    (contract : Contract descriptor before) (slot : StackFrame.Slot descriptor.frame location)
    (excludes : write.Excludes location) (query : Word)
    (inside : (qwordRegion location).Contains query) :
    after.resources.space.cells query = before.resources.space.cells query := by
  cases excludes with
  | data success =>
    exact data_preserves_private_cells contract (Borrowing.store64_effect success) query
      (Borrowing.subregion_inside slot inside)
  | privateSlot _ success separate =>
    exact store64_preserves_disjoint_cells (Borrowing.store64_effect success) separate query inside

/-- Exact cells and contents of a protected private qword survive any finite
checked mixed history that excludes overlapping private writes. Capabilities
remain current at every step by the existing history transport. -/
theorem History.preserves_private_cells {descriptor : Descriptor} {before after : Shared}
    {location : Word} (history : History descriptor before after)
    (contract : Contract descriptor before) (slot : StackFrame.Slot descriptor.frame location)
    (excludes : history.Excludes location) (query : Word)
    (inside : (qwordRegion location).Contains query) :
    after.resources.space.cells query = before.resources.space.cells query := by
  induction excludes with
  | refl => rfl
  | @next _ _ _ first _ head _ ih =>
    exact (ih (first.contract contract)).trans
      (first.preserves_private_cells contract slot head query inside)

theorem History.preserves_private {descriptor : Descriptor} {before after : Shared}
    {initial final : X86.State} {location : Word}
    (history : History descriptor before after)
    (first : Current descriptor before initial) (last : Current descriptor after final)
    (slot : StackFrame.Slot descriptor.frame location) (excludes : history.Excludes location) :
    readWord final.memory location = readWord initial.memory location :=
  private_read_congr first last slot (history.preserves_private_cells first.contract slot excludes)

end EDSL.OS.CallMemory64
