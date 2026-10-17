/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.Model

set_option warningAsError true

namespace EDSL.OS.CallMemory64
open X86 AddressSpace

/-- Exactly the two owned write regions. These OS events are checked mutations,
not a claim that a CPU executed a matching instruction. -/
inductive Write (descriptor : Descriptor) : Shared → Shared → Prop where
  | privateSlot {before after address value} (slot : StackFrame.Slot descriptor.frame address)
      (success : Borrowing.mutate before
        (.store64 descriptor.owner descriptor.frame.ticket address value) = .ok (after, none)) :
      Write descriptor before after
  | data {before after value}
      (success : Borrowing.mutate before
        (.store64 descriptor.owner descriptor.ticket descriptor.target value) = .ok (after, none)) :
      Write descriptor before after

inductive History (descriptor : Descriptor) : Shared → Shared → Prop where
  | refl {shared} : History descriptor shared shared
  | next {before middle after} (first : Write descriptor before middle)
      (tail : History descriptor middle after) : History descriptor before after

/-- A union RAM frame, with exact allocation, loan and permission metadata.
Private return-address bytes may change independently of the DATA operand. -/
structure Preservation (descriptor : Descriptor) (before after : Shared) : Prop where
  history : Borrowing.History before after
  allocations : after.resources.allocations = before.resources.allocations
  frontier : after.resources.frontier = before.resources.frontier
  loans : after.loans = before.loans
  nextLoan : after.nextLoan = before.nextLoan
  permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
    (before.resources.space.cells query).map Cell.permissions
  outside : ∀ query, ¬descriptor.frame.region.Contains query →
    ¬(qwordRegion descriptor.target).Contains query →
    after.resources.space.cells query = before.resources.space.cells query

theorem Preservation.refl (descriptor : Descriptor) (shared : Shared) :
    Preservation descriptor shared shared :=
  ⟨.refl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

private theorem borrowing_trans {a b c : Shared}
    (first : Borrowing.History a b) (last : Borrowing.History b c) : Borrowing.History a c := by
  induction first with
  | refl => exact last
  | next step _ ih => exact .next step (ih last)

theorem Preservation.trans {descriptor : Descriptor} {a b c : Shared}
    (first : Preservation descriptor a b) (last : Preservation descriptor b c) :
    Preservation descriptor a c :=
  ⟨borrowing_trans first.history last.history,
    last.allocations.trans first.allocations, last.frontier.trans first.frontier,
    last.loans.trans first.loans, last.nextLoan.trans first.nextLoan,
    fun query => (last.permissions query).trans (first.permissions query),
    fun query stack data => (last.outside query stack data).trans (first.outside query stack data)⟩

theorem Write.preserves {descriptor : Descriptor} {before after : Shared}
    (write : Write descriptor before after) : Preservation descriptor before after := by
  cases write with
  | privateSlot slot success =>
    have effect := Borrowing.store64_effect success
    exact ⟨.next (.mutate success) .refl, effect.allocations, effect.frontier,
      effect.loans, effect.nextLoan, effect.permissions,
      fun query outside _ => effect.outside query
        (fun inside => outside (Borrowing.subregion_inside slot inside))⟩
  | data success =>
    have effect := Borrowing.store64_effect success
    exact ⟨.next (.mutate success) .refl, effect.allocations, effect.frontier,
      effect.loans, effect.nextLoan, effect.permissions,
      fun query _ outside => effect.outside query outside⟩

theorem History.preserves {descriptor : Descriptor} {before after : Shared}
    (history : History descriptor before after) : Preservation descriptor before after := by
  induction history with
  | refl => exact .refl _ _
  | next first _ ih => exact first.preserves.trans ih

theorem History.borrowing {descriptor : Descriptor} {before after : Shared}
    (history : History descriptor before after) : Borrowing.History before after :=
  history.preserves.history

theorem History.trans {descriptor : Descriptor} {a b c : Shared}
    (first : History descriptor a b) (last : History descriptor b c) : History descriptor a c := by
  induction first with
  | refl => exact last
  | next step _ ih => exact .next step (ih last)

theorem Preservation.contract {descriptor : Descriptor} {before after : Shared}
    (preservation : Preservation descriptor before after) (contract : Contract descriptor before) :
    Contract descriptor after :=
  contract.transport preservation.history preservation.allocations preservation.permissions
    preservation.loans

theorem Write.contract {descriptor : Descriptor} {before after : Shared}
    (write : Write descriptor before after) (contract : Contract descriptor before) :
    Contract descriptor after := write.preserves.contract contract

theorem History.contract {descriptor : Descriptor} {before after : Shared}
    (history : History descriptor before after) (contract : Contract descriptor before) :
    Contract descriptor after := history.preserves.contract contract

theorem History.current {descriptor : Descriptor} {before after : Shared} {machine : X86.State}
    (history : History descriptor before after) (contract : Contract descriptor before)
    (coupled : machine.memory = toMemory after.resources.space) : Current descriptor after machine :=
  ⟨history.contract contract, coupled⟩

theorem Preservation.loan_contents {descriptor : Descriptor} {before after : Shared}
    (preservation : Preservation descriptor before after) (valid : Borrowing.WellFormed before)
    {identifier : Nat} {loan : Borrowing.Loan} (live : before.loans identifier = some loan) :
    ∀ query, loan.region.Contains query →
      after.resources.space.cells query = before.resources.space.cells query :=
  (preservation.history.loan_stable valid identifier (valid.2 _ _ live).1 loan
    ((congrFun preservation.loans identifier).trans live)).2

/-- Real private stores retain both capabilities, including the DATA allocation. -/
theorem contract_private_store64 {descriptor : Descriptor} {before after : Shared}
    {address value : Word} (contract : Contract descriptor before)
    (slot : StackFrame.Slot descriptor.frame address)
    (success : Borrowing.mutate before
      (.store64 descriptor.owner descriptor.frame.ticket address value) = .ok (after, none)) :
    Contract descriptor after := (Write.privateSlot slot success).contract contract

/-- Real DATA stores retain both capabilities, including the private stack. -/
theorem contract_data_store64 {descriptor : Descriptor} {before after : Shared}
    {value : Word} (contract : Contract descriptor before)
    (success : Borrowing.mutate before
      (.store64 descriptor.owner descriptor.ticket descriptor.target value) = .ok (after, none)) :
    Contract descriptor after := (Write.data success).contract contract

/-- A current store obtains its evolved world from the checked OS mutation. The
returned view is recoupled to that same complete memory, not a prior snapshot. -/
theorem Current.data_store64 {descriptor : Descriptor} {shared : Shared} {machine : X86.State}
    (current : Current descriptor shared machine) (value : Word) :
    ∃ evolved, Borrowing.mutate shared
        (.store64 descriptor.owner descriptor.ticket descriptor.target value) = .ok (evolved, none) ∧
      Current descriptor evolved (StackFrame.recouple machine evolved) ∧
      Write descriptor shared evolved ∧
      Borrowing.StoreEffect64 shared evolved descriptor.target value ∧
      Borrowing.loadOwnedWord64 evolved descriptor.owner descriptor.ticket descriptor.target = .ok value ∧
      readWord (StackFrame.recouple machine evolved).memory descriptor.target = .ok value := by
  obtain ⟨evolved, success⟩ := current.contract.data_store64_enabled value
  exact ⟨evolved, success, ⟨contract_data_store64 current.contract success, rfl⟩,
    .data success, Borrowing.store64_effect success,
    Borrowing.store64_owned_readback success, Borrowing.store64_readWord success⟩

/-- Private owner stores are enabled from the present stack capability and keep
the separately owned DATA capability current in the same evolved world. -/
theorem Current.private_store64 {descriptor : Descriptor} {shared : Shared}
    {machine : X86.State} {address : Word} (current : Current descriptor shared machine)
    (slot : StackFrame.Slot descriptor.frame address) (value : Word) :
    ∃ evolved, Borrowing.mutate shared
        (.store64 descriptor.owner descriptor.frame.ticket address value) = .ok (evolved, none) ∧
      Current descriptor evolved (StackFrame.recouple machine evolved) ∧
      Write descriptor shared evolved ∧
      Borrowing.StoreEffect64 shared evolved address value ∧
      Borrowing.loadOwnedWord64 evolved descriptor.owner descriptor.frame.ticket address = .ok value ∧
      readWord (StackFrame.recouple machine evolved).memory address = .ok value := by
  obtain ⟨evolved, success⟩ := current.contract.private_store64_enabled slot value
  exact ⟨evolved, success, ⟨contract_private_store64 current.contract slot success, rfl⟩,
    .privateSlot slot success, Borrowing.store64_effect success,
    Borrowing.store64_owned_readback success, Borrowing.store64_readWord success⟩

/-- A private store cannot alter the independently owned target read. -/
theorem private_store64_preserves_data {descriptor : Descriptor} {before after : Shared}
    {address value observed : Word} (contract : Contract descriptor before)
    (slot : StackFrame.Slot descriptor.frame address)
    (success : Borrowing.mutate before
      (.store64 descriptor.owner descriptor.frame.ticket address value) = .ok (after, none))
    (read : Borrowing.loadOwnedWord64 before descriptor.owner descriptor.ticket descriptor.target =
      .ok observed) :
    Borrowing.loadOwnedWord64 after descriptor.owner descriptor.ticket descriptor.target =
      .ok observed := by
  have effect := Borrowing.store64_effect success
  obtain ⟨allocation, authorized, fits, loaded⟩ := Borrowing.loadOwnedWord64_ok _ _ _ _ _ read
  apply Borrowing.loadOwnedWord64_success _ _ _ _ _ allocation ?_ fits ?_
  · simpa only [Ownership.authorize, effect.allocations] using authorized
  · apply (loadQWord_congr _ _ _ ?_).trans loaded
    apply AddressSpace.agrees_read
    intro offset bound
    have inside : (qwordRegion descriptor.target).Contains
        (descriptor.target + BitVec.ofNat 64 offset) :=
      Ownership.addresses_inside _ contract.target_valid _
        (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)
    exact effect.outside _ (fun operand =>
      contract.target_outside_private inside (Borrowing.subregion_inside slot operand))

end EDSL.OS.CallMemory64
