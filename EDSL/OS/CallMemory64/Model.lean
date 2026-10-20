/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame.Transport

set_option warningAsError true

namespace EDSL.OS.CallMemory64
open X86 AddressSpace

abbrev Shared := Borrowing.State

/-- Separate handles for the private stack and one ordinary DATA8 operand. -/
structure Descriptor where
  frame : StackFrame.Descriptor
  ticket : Ownership.Ticket
  target : Word

def Descriptor.owner (descriptor : Descriptor) : Nat := descriptor.frame.owner

/-- Present capabilities for both allocations. Distinct live allocations derive
separation; neither a future store nor a claimed successful execution is assumed. -/
structure Contract (descriptor : Descriptor) (shared : Shared) : Prop where
  stack : StackFrame.Contract descriptor.frame shared
  word : WordResources64.WordValid shared descriptor.owner descriptor.ticket descriptor.target
  unborrowed : ∀ identifier loan, shared.loans identifier = some loan →
    loan.ticket.identifier ≠ descriptor.ticket.identifier
  separate : descriptor.ticket.identifier ≠ descriptor.frame.ticket.identifier

structure Current (descriptor : Descriptor) (shared : Shared) (machine : X86.State) : Prop where
  contract : Contract descriptor shared
  coupled : machine.memory = toMemory shared.resources.space

theorem Contract.wellFormed {descriptor : Descriptor} {shared : Shared}
    (contract : Contract descriptor shared) : Borrowing.WellFormed shared :=
  contract.stack.wellFormed

theorem Current.stack {descriptor : Descriptor} {shared : Shared} {machine : X86.State}
    (current : Current descriptor shared machine) : StackFrame.Current descriptor.frame shared machine :=
  ⟨current.contract.stack, current.coupled⟩

theorem Current.sameMemory {descriptor : Descriptor} {shared : Shared} {before after : X86.State}
    (current : Current descriptor shared before) (memory : after.memory = before.memory) :
    Current descriptor shared after := ⟨current.contract, memory.trans current.coupled⟩

/-- A contained private operand derives a checked store under the same owner. -/
theorem Contract.private_store64_enabled {descriptor : Descriptor} {shared : Shared}
    {address : Word} (contract : Contract descriptor shared)
    (slot : StackFrame.Slot descriptor.frame address) (value : Word) :
    ∃ evolved, Borrowing.mutate shared
      (.store64 descriptor.owner descriptor.frame.ticket address value) = .ok (evolved, none) :=
  (StackFrame.PresentSlot.mk contract.stack slot).store64_enabled value

/-- Complete DATA8 authority derives a real checked store for every value. -/
theorem Contract.data_store64_enabled {descriptor : Descriptor} {shared : Shared}
    (contract : Contract descriptor shared) (value : Word) :
    ∃ evolved, Borrowing.mutate shared
      (.store64 descriptor.owner descriptor.ticket descriptor.target value) = .ok (evolved, none) := by
  obtain ⟨allocation, authorized, fits⟩ := contract.word.authorize
  exact Borrowing.store64_admitted _ _ _ _ value allocation authorized fits
    contract.word.writable contract.unborrowed

/-- Current owner observation has no loan side effect and reads the current OS world. -/
theorem Contract.data_read {descriptor : Descriptor} {shared : Shared}
    (contract : Contract descriptor shared) :
    ∃ value, Borrowing.loadOwnedWord64 shared descriptor.owner descriptor.ticket descriptor.target =
        .ok value ∧
      readWord (toMemory shared.resources.space) descriptor.target = .ok value ∧
      Ownership.Current shared.resources descriptor.owner descriptor.ticket := by
  obtain ⟨allocation, authorized, fits⟩ := contract.word.authorize
  obtain ⟨value, observed⟩ := Borrowing.loadOwnedWord64_exists _ _ _ _ allocation authorized fits
    contract.word.writable
  exact ⟨value, observed, Borrowing.loadOwnedWord64_readWord _ _ _ _ _ observed,
    Borrowing.loadOwnedWord64_current _ _ _ _ _ observed⟩

/-- The full target word inherits a valid natural interval from its current allocation. -/
theorem Contract.target_valid {descriptor : Descriptor} {shared : Shared}
    (contract : Contract descriptor shared) : (qwordRegion descriptor.target).valid = true := by
  obtain ⟨allocation, found, _, _, fits, _⟩ := contract.word
  have valid := of_decide_eq_true (contract.wellFormed.1.1 _ _ found).2.1
  have bounds : allocation.region.base.toNat ≤ descriptor.target.toNat ∧
      descriptor.target.toNat + 8 ≤ allocation.region.base.toNat + allocation.region.length :=
    of_decide_eq_true fits
  apply decide_eq_true
  change 0 < 8 ∧ descriptor.target.toNat + 8 ≤ 2^64 ∧
    (descriptor.target.toNat + 8 ≤ 2^47 ∨ 2^64 - 2^47 ≤ descriptor.target.toNat)
  omega

/-- The DATA allocation and the entire private frame are separate by current
well-formed allocation identity, including non-aligned contained stack slots. -/
theorem Contract.target_private_disjoint {descriptor : Descriptor} {shared : Shared}
    (contract : Contract descriptor shared) :
    Ownership.Disjoint (qwordRegion descriptor.target) descriptor.frame.region := by
  obtain ⟨data, dataAt, _, _, fits, _⟩ := contract.word
  obtain ⟨stack, stackAt, _, _, region⟩ := contract.stack.authority
  have disjoint := contract.wellFormed.1.2 _ _ _ _ dataAt stackAt contract.separate
  have bounds : data.region.base.toNat ≤ descriptor.target.toNat ∧
      descriptor.target.toNat + 8 ≤ data.region.base.toNat + data.region.length :=
    of_decide_eq_true fits
  rw [region] at disjoint
  rcases disjoint with left | right
  · exact .inl (Nat.le_trans bounds.2 left)
  · exact .inr (Nat.le_trans right bounds.1)

/-- In particular, no byte of the target word is a private stack byte. -/
theorem Contract.target_outside_private {descriptor : Descriptor} {shared : Shared}
    (contract : Contract descriptor shared) {query : Word}
    (inside : (qwordRegion descriptor.target).Contains query) :
    ¬descriptor.frame.region.Contains query := by
  intro privateByte
  exact Ownership.disjoint_outside contract.target_private_disjoint privateByte inside

/-- Metadata/permission transport preserves both live capabilities through a
checked history, including external target writes and private stack writes. -/
theorem Contract.transport {descriptor : Descriptor} {before after : Shared}
    (contract : Contract descriptor before) (history : Borrowing.History before after)
    (allocations : after.resources.allocations = before.resources.allocations)
    (permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
      (before.resources.space.cells query).map Cell.permissions)
    (loans : after.loans = before.loans) : Contract descriptor after :=
  ⟨contract.stack.transport history allocations permissions loans,
    contract.word.permissions allocations permissions,
    fun identifier loan live => contract.unborrowed identifier loan (by rwa [← loans]),
    contract.separate⟩

end EDSL.OS.CallMemory64
