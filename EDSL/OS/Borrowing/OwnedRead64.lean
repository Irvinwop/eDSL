/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Read64
import EDSL.OS.Borrowing.Store64

namespace EDSL.OS.Borrowing
open X86 AddressSpace

/-- Observe through current ownership without taking a read loan. Existing
loans are compatible with observation; they still gate every mutation. -/
def loadOwnedWord64 (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word) :
    Except Ownership.ReadFault Word :=
  Ownership.loadWord64 state.resources owner ticket address

theorem loadOwnedWord64_ok (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) (success : loadOwnedWord64 state owner ticket address = .ok value) :
    ∃ authorizedAllocation, Ownership.authorize state.resources owner ticket = .ok authorizedAllocation ∧
      Ownership.containsQWord authorizedAllocation address = true ∧
      loadQWord (toMemory state.resources.space) address = .ok value :=
  Ownership.loadWord64_ok _ _ _ _ _ success

theorem loadOwnedWord64_success (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) (authorizedAllocation : Ownership.Allocation)
    (authorized : Ownership.authorize state.resources owner ticket = .ok authorizedAllocation)
    (fits : Ownership.containsQWord authorizedAllocation address = true)
    (observed : loadQWord (toMemory state.resources.space) address = .ok value) :
    loadOwnedWord64 state owner ticket address = .ok value :=
  Ownership.loadWord64_success _ _ _ _ _ authorizedAllocation authorized fits observed

theorem loadOwnedWord64_success_iff (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) :
    loadOwnedWord64 state owner ticket address = .ok value ↔
      ∃ authorizedAllocation, Ownership.authorize state.resources owner ticket = .ok authorizedAllocation ∧
        Ownership.containsQWord authorizedAllocation address = true ∧
        loadQWord (toMemory state.resources.space) address = .ok value :=
  Ownership.loadWord64_success_iff _ _ _ _ _

theorem loadOwnedWord64_current (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) (success : loadOwnedWord64 state owner ticket address = .ok value) :
    Ownership.Current state.resources owner ticket :=
  Ownership.loadWord64_current _ _ _ _ _ success

theorem loadOwnedWord64_readWord (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) (success : loadOwnedWord64 state owner ticket address = .ok value) :
    readWord (toMemory state.resources.space) address = .ok value :=
  Ownership.loadWord64_readWord _ _ _ _ _ success

theorem loadOwnedWord64_exists (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (authorizedAllocation : Ownership.Allocation)
    (authorized : Ownership.authorize state.resources owner ticket = .ok authorizedAllocation)
    (fits : Ownership.containsQWord authorizedAllocation address = true)
    (readable : canStoreQWord (toMemory state.resources.space) address = true) :
    ∃ value, loadOwnedWord64 state owner ticket address = .ok value :=
  Ownership.loadWord64_exists _ _ _ _ authorizedAllocation authorized fits readable

/-- Exact readback follows a real successful mutation, including its existing
loan gate. The checked store preserves allocation authorization and bounds. -/
theorem store64_owned_readback {before after : State} {owner : Nat}
    {ticket : Ownership.Ticket} {address value : Word}
    (success : mutate before (.store64 owner ticket address value) = .ok (after, none)) :
    loadOwnedWord64 after owner ticket address = .ok value := by
  obtain ⟨world, stored, same⟩ := store64_shape success
  obtain ⟨allocation, space, authorized, fits, _, worldEq⟩ :=
    Ownership.storeWord64_ok _ _ _ _ _ _ stored
  have observed := (store64_effect success).readback
  apply loadOwnedWord64_success _ _ _ _ _ allocation ?_ fits observed
  simpa only [same, worldEq, Ownership.authorize] using authorized

theorem store64_readWord {before after : State} {owner : Nat}
    {ticket : Ownership.Ticket} {address value : Word}
    (success : mutate before (.store64 owner ticket address value) = .ok (after, none)) :
    readWord (toMemory after.resources.space) address = .ok value :=
  loadOwnedWord64_readWord _ _ _ _ _ (store64_owned_readback success)

/-- A disjoint store in the same allocation can follow an owned observation.
Authorization is retained, and the actual eight-byte read is framed. -/
theorem store64_preserves_owned_read {before after : State} {writer reader : Nat}
    {writeTicket readTicket : Ownership.Ticket} {address readAddress value observed : Word}
    (stored : mutate before (.store64 writer writeTicket address value) = .ok (after, none))
    (read : loadOwnedWord64 before reader readTicket readAddress = .ok observed)
    (disjoint : QWordDisjoint address readAddress 8) :
    loadOwnedWord64 after reader readTicket readAddress = .ok observed := by
  obtain ⟨allocation, authorized, fits, machine⟩ := loadOwnedWord64_ok _ _ _ _ _ read
  have effect := store64_effect stored
  refine loadOwnedWord64_success _ _ _ _ _ allocation ?_ fits ?_
  · simpa only [Ownership.authorize, effect.allocations] using authorized
  · rw [effect.projection]
    exact (loadQWord_congr _ _ _ (X86.writeQWord_agrees _ _ _ _ _ disjoint)).trans machine

end EDSL.OS.Borrowing
