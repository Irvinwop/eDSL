/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources
import EDSL.OS.WordResources64
import EDSL.OS.Borrowing.OwnedRead64

set_option warningAsError true

namespace EDSL.OS.StackFrame
open X86 AddressSpace

abbrev Shared := Borrowing.State

/-- Immutable code and original caller-slot handles are separate from the
current private allocation. No splitting of a borrowed allocation is assumed. -/
structure Descriptor where
  call : CallResources.Call
  ticket : Ownership.Ticket
  capacity : Nat

def Descriptor.owner (frame : Descriptor) : Nat := Threads.principal frame.call.worker

def Descriptor.top (frame : Descriptor) : Word := frame.call.stack

/-- Natural interval below the original caller slot, independent of current RSP. -/
def Descriptor.region (frame : Descriptor) : Region :=
  ⟨BitVec.ofNat 64 (frame.top.toNat - frame.capacity), frame.capacity⟩

/-- The entire eight-byte operand fits. No alignment is required by this RAM model. -/
def Slot (frame : Descriptor) (address : Word) : Prop :=
  Borrowing.Subregion (qwordRegion address) frame.region

instance (frame : Descriptor) (address : Word) : Decidable (Slot frame address) :=
  inferInstanceAs (Decidable (Borrowing.Subregion _ _))

/-- Present authority and permissions only. The code/caller loans refer to other
allocations from the outset; the whole private allocation is unborrowed.
`ready` describes current per-word permissions, never future execution. -/
structure Contract (frame : Descriptor) (shared : Shared) : Prop where
  pureCall : CallResources.Contract frame.call shared
  allocation : ∃ allocation,
    Ownership.authorize shared.resources frame.owner frame.ticket = .ok allocation ∧
      allocation.region = frame.region
  topBound : frame.capacity ≤ frame.top.toNat
  ready : ∀ address, Slot frame address →
    WordResources64.WordValid shared frame.owner frame.ticket address
  unborrowed : ∀ identifier loan, shared.loans identifier = some loan →
    loan.ticket.identifier ≠ frame.ticket.identifier

structure Current (frame : Descriptor) (shared : Shared) (machine : X86.State) : Prop where
  contract : Contract frame shared
  coupled : machine.memory = toMemory shared.resources.space

/-- A contained slot in a current frame, with no assumed successful store. -/
structure PresentSlot (frame : Descriptor) (shared : Shared) (address : Word) : Prop where
  contract : Contract frame shared
  fits : Slot frame address

theorem Contract.wellFormed {frame : Descriptor} {shared : Shared}
    (contract : Contract frame shared) : Borrowing.WellFormed shared :=
  contract.pureCall.wellFormed

theorem Contract.authority {frame : Descriptor} {shared : Shared}
    (contract : Contract frame shared) :
    ∃ allocation, shared.resources.allocations frame.ticket.identifier = some allocation ∧
      allocation.owner = frame.owner ∧ allocation.epoch = frame.ticket.epoch ∧
      allocation.region = frame.region := by
  obtain ⟨allocation, authorized, region⟩ := contract.allocation
  obtain ⟨found, owner, epoch⟩ := Ownership.authorize_ok _ _ _ _ authorized
  exact ⟨allocation, found, owner, epoch, region⟩

theorem Contract.region_valid {frame : Descriptor} {shared : Shared}
    (contract : Contract frame shared) : frame.region.valid = true := by
  obtain ⟨allocation, found, _, _, region⟩ := contract.authority
  rw [← region]
  exact (contract.wellFormed.1.1 _ _ found).2.1

theorem Contract.capacity_pos {frame : Descriptor} {shared : Shared}
    (contract : Contract frame shared) : 0 < frame.capacity :=
  (of_decide_eq_true contract.region_valid).1

theorem Contract.region_bounds {frame : Descriptor} {shared : Shared}
    (contract : Contract frame shared) :
    frame.region.base.toNat = frame.top.toNat - frame.capacity ∧
      frame.region.base.toNat + frame.region.length = frame.top.toNat := by
  have small : frame.top.toNat - frame.capacity < 2^64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) frame.top.isLt
  have base : frame.region.base.toNat = frame.top.toNat - frame.capacity := by
    simp only [Descriptor.region, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  refine ⟨base, ?_⟩
  rw [base]
  exact Nat.sub_add_cancel contract.topBound

theorem Contract.slot_bounds {frame : Descriptor} {shared : Shared} {address : Word}
    (contract : Contract frame shared) (slot : Slot frame address) :
    frame.top.toNat - frame.capacity ≤ address.toNat ∧
      address.toNat + 8 ≤ frame.top.toNat := by
  have bounds := contract.region_bounds
  exact ⟨by simpa only [qwordRegion, bounds.1] using slot.1,
    Nat.le_trans slot.2 (Nat.le_of_eq bounds.2)⟩

theorem Contract.currentRW {frame : Descriptor} {shared : Shared} {address : Word}
    (contract : Contract frame shared) (slot : Slot frame address) :
    WordResources64.WordValid shared frame.owner frame.ticket address :=
  contract.ready address slot

theorem PresentSlot.currentRW {frame : Descriptor} {shared : Shared} {address : Word}
    (present : PresentSlot frame shared address) :
    WordResources64.WordValid shared frame.owner frame.ticket address :=
  present.contract.currentRW present.fits

theorem Current.pureCall {frame : Descriptor} {shared : Shared} {machine : X86.State}
    (current : Current frame shared machine) : CallResources.Current frame.call shared machine :=
  ⟨current.contract.pureCall, current.coupled⟩

theorem Current.sameMemory {frame : Descriptor} {shared : Shared} {before after : X86.State}
    (current : Current frame shared before) (memory : after.memory = before.memory) :
    Current frame shared after := ⟨current.contract, memory.trans current.coupled⟩

end EDSL.OS.StackFrame
