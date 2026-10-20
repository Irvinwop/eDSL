/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame.Store

set_option warningAsError true

namespace EDSL.OS.StackFrame
open X86 AddressSpace

/-- One actual checked private store. Its entire operand must fit the frame.
These are OS transitions; no CPU CALL or PUSH trace is asserted. -/
inductive PrivateWrite (frame : Descriptor) : Shared → Shared → Prop where
  | store64 {before after address value} (slot : Slot frame address)
      (success : Borrowing.mutate before (.store64 frame.owner frame.ticket address value) =
        .ok (after, none)) : PrivateWrite frame before after

inductive PrivateHistory (frame : Descriptor) : Shared → Shared → Prop where
  | refl {shared} : PrivateHistory frame shared shared
  | next {before middle after} (first : PrivateWrite frame before middle)
      (tail : PrivateHistory frame middle after) : PrivateHistory frame before after

/-- Whole-frame boundary, every permission and all allocation/loan metadata.
Inside-frame bytes may differ, including return addresses left behind after pop. -/
structure Preservation (frame : Descriptor) (before after : Shared) : Prop where
  history : Borrowing.History before after
  allocations : after.resources.allocations = before.resources.allocations
  frontier : after.resources.frontier = before.resources.frontier
  loans : after.loans = before.loans
  nextLoan : after.nextLoan = before.nextLoan
  permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
    (before.resources.space.cells query).map Cell.permissions
  outside : ∀ query, ¬frame.region.Contains query →
    after.resources.space.cells query = before.resources.space.cells query

theorem Preservation.refl (frame : Descriptor) (shared : Shared) : Preservation frame shared shared :=
  ⟨.refl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

private theorem history_trans {a b c : Shared}
    (first : Borrowing.History a b) (last : Borrowing.History b c) : Borrowing.History a c := by
  induction first with
  | refl => exact last
  | next step _ ih => exact .next step (ih last)

theorem Preservation.trans {frame : Descriptor} {a b c : Shared}
    (first : Preservation frame a b) (last : Preservation frame b c) : Preservation frame a c :=
  ⟨history_trans first.history last.history,
    last.allocations.trans first.allocations, last.frontier.trans first.frontier,
    last.loans.trans first.loans, last.nextLoan.trans first.nextLoan,
    fun query => (last.permissions query).trans (first.permissions query),
    fun query outside => (last.outside query outside).trans (first.outside query outside)⟩

theorem PrivateWrite.preserves {frame : Descriptor} {before after : Shared}
    (write : PrivateWrite frame before after) : Preservation frame before after := by
  cases write with
  | store64 slot success =>
    have effect := Borrowing.store64_effect success
    exact ⟨.next (.mutate success) .refl, effect.allocations, effect.frontier,
      effect.loans, effect.nextLoan, effect.permissions,
      fun query outside => effect.outside query
        (fun inside => outside (Borrowing.subregion_inside slot inside))⟩

theorem PrivateHistory.preserves {frame : Descriptor} {before after : Shared}
    (history : PrivateHistory frame before after) : Preservation frame before after := by
  induction history with
  | refl => exact .refl _ _
  | next first _ ih => exact first.preserves.trans ih

theorem PrivateHistory.borrowing {frame : Descriptor} {before after : Shared}
    (history : PrivateHistory frame before after) : Borrowing.History before after :=
  history.preserves.history

theorem PrivateHistory.trans {frame : Descriptor} {a b c : Shared}
    (first : PrivateHistory frame a b) (last : PrivateHistory frame b c) : PrivateHistory frame a c := by
  induction first with
  | refl => exact last
  | next step _ ih => exact .next step (ih last)

theorem PrivateHistory.contract {frame : Descriptor} {before after : Shared}
    (history : PrivateHistory frame before after) (contract : Contract frame before) :
    Contract frame after := by
  induction history with
  | refl => exact contract
  | next first _ ih =>
    cases first with
    | store64 _ success => exact ih (contract_store64 contract success).1

/-- Current endpoint resources require coupling to the actual endpoint world.
Registers, RSP, RIP and flags must be justified by the CPU trace separately. -/
theorem PrivateHistory.current {frame : Descriptor} {before after : Shared} {machine : X86.State}
    (history : PrivateHistory frame before after) (contract : Contract frame before)
    (coupled : machine.memory = toMemory after.resources.space) : Current frame after machine :=
  ⟨history.contract contract, coupled⟩

theorem Preservation.loan_contents {frame : Descriptor} {before after : Shared}
    (preservation : Preservation frame before after) (valid : Borrowing.WellFormed before)
    {identifier : Nat} {loan : Borrowing.Loan} (live : before.loans identifier = some loan) :
    ∀ query, loan.region.Contains query →
      after.resources.space.cells query = before.resources.space.cells query := by
  exact (preservation.history.loan_stable valid identifier (valid.2 _ _ live).1 loan
    ((congrFun preservation.loans identifier).trans live)).2

end EDSL.OS.StackFrame
