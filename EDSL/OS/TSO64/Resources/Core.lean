/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAddMachine64
import EDSL.X86.StoreBuffer.Mixed
import EDSL.X86.Sequential.Return

namespace EDSL.OS.TSO64
open X86 AddressSpace

abbrev World := Atomics64.State
abbrev Buffer := StoreBuffer.Mixed.Buffer
abbrev Store := StoreBuffer.Mixed.Store

/-- A loan identity and its ORIGINAL descriptor. It never follows a changed RSP. -/
structure Lease where
  identifier : Nat
  loan : Borrowing.Loan
  deriving DecidableEq, Repr

/-- Finite lookup makes this a check of present authority, including epoch. -/
def OwnsRegion (world : World) (actor : Nat) (ticket : Ownership.Ticket)
    (region : Region) : Prop :=
  match world.legacy.shared.resources.allocations ticket.identifier with
  | none => False
  | some allocation => allocation.owner = actor ∧ allocation.epoch = ticket.epoch ∧
      Borrowing.Subregion region allocation.region

instance (world : World) (actor : Nat) (ticket : Ownership.Ticket) (region : Region) :
    Decidable (OwnsRegion world actor ticket region) := by
  unfold OwnsRegion
  split <;> infer_instance

def TicketCurrent (world : World) (actor : Nat) (ticket : Ownership.Ticket) : Bool :=
  (Ownership.authorize world.legacy.shared.resources actor ticket).isOk

def LeaseCurrent (world : World) (actor : Nat) (lease : Lease) : Prop :=
  world.legacy.shared.loans lease.identifier = some lease.loan ∧
  lease.loan.borrower = actor ∧
  OwnsRegion world lease.loan.lender lease.loan.ticket lease.loan.region ∧
  lease.loan.region.valid = true ∧
  Borrowing.allReadable world.legacy.shared.resources.space lease.loan.region = true

instance (world : World) (actor : Nat) (lease : Lease) : Decidable (LeaseCurrent world actor lease) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def published (world : World) : Memory := toMemory world.legacy.shared.resources.space

def operation (actor : Nat) (ticket : Ownership.Ticket) (store : Store) : Ownership.Mutation :=
  match store.value with
  | .dword value => .store actor ticket store.address value
  | .qword value => .store64 actor ticket store.address value

/-- Naturally aligned, non-crossing scalar RAM only. No tearing guarantee is
silently extended to an unaligned, MMIO, or unsupported address. -/
def scalar (memory : Memory) (store : Store) : Bool :=
  match store.value with
  | .dword _ => atomicAddressable store.address && canStoreDWord memory store.address
  | .qword _ => atomicAddressable64 store.address && canStoreQWord memory store.address

def dataOnly (memory : Memory) (store : Store) : Bool :=
  (List.range store.width).all fun offset =>
    !(memory.executable (store.address + BitVec.ofNat 64 offset))

/-- A Mixed overlay is NOT access authority. The whole allocation must be in
ordinary mode, without a read loan, and every operand byte must be current RW
data. The same conservative gate is used for ordinary loads in this profile. -/
def StoreGate (world : World) (actor : Nat) (ticket : Ownership.Ticket) (store : Store) : Prop :=
  OwnsRegion world actor ticket ⟨store.address, store.width⟩ ∧
  scalar (published world) store = true ∧ dataOnly (published world) store = true ∧
  Atomics64.reserved world ticket.identifier = false ∧
  Atomics.reserved world.legacy ticket.identifier = false ∧
  Borrowing.allowed world.legacy.shared (operation actor ticket store) = true

instance (world : World) (actor : Nat) (ticket : Ownership.Ticket) (store : Store) :
    Decidable (StoreGate world actor ticket store) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure Resources where
  actor : Nat
  code : Lease
  caller : Lease
  callerAddress : Word
  grants : List Ownership.Ticket
  atomics : List Atomics64.HandleId64

inductive Fault where
  | missingWorker | alreadyReturned | emptyBuffer | resource | codeBounds
  | unsupported | noGrant | noAtomicGrant | callerSlot | unexpected
  | machine (fault : X86.Error)
  | os (fault : Atomics64.Fault)
  | loan (fault : Borrowing.Fault)
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def grantFor (world : World) (resources : Resources) (store : Store) : Option Ownership.Ticket :=
  resources.grants.find? fun ticket => decide (StoreGate world resources.actor ticket store)

def atomicFor (world : World) (resources : Resources) (address : Word) :
    Option (Atomics64.HandleId64 × Atomics64.Handle × Atomics64.Cell) :=
  resources.atomics.findSome? fun identifier =>
    match Atomics64.authorize world resources.actor identifier with
    | .error _ => none
    | .ok (handle, cell) => if cell.address = address then some (identifier, handle, cell) else none

theorem grantFor_sound {world : World} {resources : Resources} {store : Store} {ticket : Ownership.Ticket}
    (selected : grantFor world resources store = some ticket) :
    ticket ∈ resources.grants ∧ StoreGate world resources.actor ticket store :=
  ⟨List.mem_of_find?_eq_some selected,
    of_decide_eq_true (List.find?_some (p := fun candidate => decide (StoreGate world resources.actor candidate store)) selected)⟩

theorem atomicFor_sound {world : World} {resources : Resources} {address : Word}
    {identifier : Atomics64.HandleId64} {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    (selected : atomicFor world resources address = some (identifier, handle, cell)) :
    identifier ∈ resources.atomics ∧ Atomics64.authorize world resources.actor identifier = .ok (handle, cell) ∧
      cell.address = address := by
  obtain ⟨id, member, selected⟩ := List.exists_of_findSome?_eq_some selected
  cases authorized : Atomics64.authorize world resources.actor id with
  | error fault => simp [authorized] at selected
  | ok pair =>
    by_cases same : pair.2.address = address
    · simp [authorized, same] at selected
      rcases selected with ⟨rfl, rfl, rfl⟩
      exact ⟨member, authorized, same⟩
    · simp [authorized, same] at selected

end EDSL.OS.TSO64
