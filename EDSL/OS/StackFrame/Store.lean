/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame.Read

set_option warningAsError true

namespace EDSL.OS.StackFrame
open X86 AddressSpace

/-- Present per-word authority, permissions and the whole-allocation borrow gate
suffice for every value. No successful future mutation is an admission premise. -/
theorem PresentSlot.store64_enabled {frame : Descriptor} {shared : Shared} {address : Word}
    (present : PresentSlot frame shared address) (value : Word) :
    ∃ evolved, Borrowing.mutate shared (.store64 frame.owner frame.ticket address value) =
      .ok (evolved, none) := by
  obtain ⟨allocation, authorized, fits⟩ := present.currentRW.authorize
  exact Borrowing.store64_admitted _ _ _ _ value allocation authorized fits
    present.currentRW.writable present.contract.unborrowed

theorem current_store64_enabled {frame : Descriptor} {shared : Shared} {machine : X86.State}
    {address : Word} (current : Current frame shared machine) (slot : Slot frame address)
    (value : Word) :
    ∃ evolved, Borrowing.mutate shared (.store64 frame.owner frame.ticket address value) =
      .ok (evolved, none) :=
  (PresentSlot.mk current.contract slot).store64_enabled value

/-- Transport the complete current contract using a real checked mutation.
All live loan records and their cells survive, including code and caller slots. -/
theorem contract_store64 {frame : Descriptor} {shared evolved : Shared} {address value : Word}
    (contract : Contract frame shared)
    (success : Borrowing.mutate shared (.store64 frame.owner frame.ticket address value) =
      .ok (evolved, none)) :
    Contract frame evolved ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  have effect := Borrowing.store64_effect success
  have history : Borrowing.History shared evolved := .next (.mutate success) .refl
  obtain ⟨codeLoan, codeCells⟩ := contract.pureCall.codeLoan.frame contract.wellFormed history
    (congrFun effect.loans frame.call.codeLoan)
  obtain ⟨stackLoan, stackCells⟩ := contract.pureCall.stackLoan.frame contract.wellFormed history
    (congrFun effect.loans frame.call.stackLoan)
  have pureCall : CallResources.Contract frame.call evolved :=
    ⟨history.wellFormed contract.wellFormed, codeLoan, stackLoan,
      AddressSpace.agrees_code _ _ _ _ codeCells contract.pureCall.code,
      (readWord_congr _ _ _ (AddressSpace.agrees_read _ _ _ _ stackCells)).trans contract.pureCall.stack,
      contract.pureCall.returnCanonical, contract.pureCall.stackBound,
      contract.pureCall.postStackCanonical⟩
  obtain ⟨allocation, authorized, region⟩ := contract.allocation
  refine ⟨⟨pureCall, ⟨allocation, ?_, region⟩, contract.topBound,
    fun query slot => (contract.ready query slot).permissions effect.allocations effect.permissions,
    fun identifier loan live => contract.unborrowed identifier loan (by rwa [← effect.loans])⟩, ?_⟩
  · simpa only [Ownership.authorize, effect.allocations] using authorized
  · intro identifier loan live query inside
    have below := (contract.wellFormed.2 identifier loan live).1
    exact (history.loan_stable contract.wellFormed identifier below loan
      ((congrFun effect.loans identifier).trans live)).2 query inside

/-- A successful private mutation cannot cross the complete frame boundary. -/
theorem store64_slot {frame : Descriptor} {shared evolved : Shared} {address value : Word}
    (contract : Contract frame shared)
    (success : Borrowing.mutate shared (.store64 frame.owner frame.ticket address value) =
      .ok (evolved, none)) : Slot frame address := by
  obtain ⟨world, stored, _⟩ := Borrowing.store64_shape success
  obtain ⟨allocation, _, authorized, fits, _, _⟩ := Ownership.storeWord64_ok _ _ _ _ _ _ stored
  obtain ⟨current, currentAt, region⟩ := contract.allocation
  have same : allocation = current := Except.ok.inj (authorized.symm.trans currentAt)
  subst allocation
  have bounds := of_decide_eq_true fits
  simpa only [Slot, Borrowing.Subregion, qwordRegion, region] using bounds

/-- A view coupled to an evolved OS world. This definition alone asserts no CPU
instruction transition; CALL/PUSH bindings require their own execution lemmas. -/
def recouple (machine : X86.State) (shared : Shared) : X86.State :=
  { machine with memory := toMemory shared.resources.space }

/-- Present resources derive the real store, exact full64 effect/readback and a
current view of that same evolved world. All slots remain writable by this owner. -/
theorem current_store64 {frame : Descriptor} {shared : Shared} {machine : X86.State}
    {address : Word} (current : Current frame shared machine) (slot : Slot frame address)
    (value : Word) :
    ∃ evolved, Borrowing.mutate shared (.store64 frame.owner frame.ticket address value) =
        .ok (evolved, none) ∧
      Current frame evolved (recouple machine evolved) ∧
      Borrowing.StoreEffect64 shared evolved address value ∧
      Borrowing.loadOwnedWord64 evolved frame.owner frame.ticket address = .ok value ∧
      readWord (recouple machine evolved).memory address = .ok value ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  obtain ⟨evolved, success⟩ := current_store64_enabled current slot value
  obtain ⟨contract, loans⟩ := contract_store64 current.contract success
  exact ⟨evolved, success, ⟨contract, rfl⟩, Borrowing.store64_effect success,
    Borrowing.store64_owned_readback success, Borrowing.store64_readWord success, loans⟩

end EDSL.OS.StackFrame
