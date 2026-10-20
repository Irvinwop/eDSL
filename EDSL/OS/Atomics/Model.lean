/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicExchange.Core

namespace EDSL.OS.Atomics
open X86 AddressSpace

/-- Stored shared atomic authority. Actor labels are logical principals, not
runtime authentication. Several actors can hold distinct handles for one cell. -/
structure Handle where
  owner : Nat
  ticket : Ownership.Ticket
  actor : Nat
  address : Word
  deriving DecidableEq, Repr

structure State where
  shared : Borrowing.State
  nextHandle : Nat
  handles : Nat → Option Handle

def empty (shared : Borrowing.State) : State := ⟨shared, 0, fun _ => none⟩

def ValidHandle (shared : Borrowing.State) (handle : Handle) : Prop :=
  ∃ allocation, shared.resources.allocations handle.ticket.identifier = some allocation ∧
    allocation.owner = handle.owner ∧ allocation.epoch = handle.ticket.epoch ∧
    Ownership.containsWord allocation handle.address = true ∧
    atomicAddressable handle.address = true ∧
    canStoreDWord (toMemory shared.resources.space) handle.address = true

/-- One reserved word per allocation. Read loans retain their original
whole-allocation freeze contract and therefore cannot name this allocation. -/
structure WellFormed (state : State) : Prop where
  shared : Borrowing.WellFormed state.shared
  handles : ∀ identifier handle, state.handles identifier = some handle →
    identifier < state.nextHandle ∧ ValidHandle state.shared handle
  noReaders : ∀ identifier handle, state.handles identifier = some handle →
    ∀ loanId loan, state.shared.loans loanId = some loan →
      loan.ticket.identifier ≠ handle.ticket.identifier
  agreement : ∀ left a right b, state.handles left = some a → state.handles right = some b →
    a.ticket.identifier = b.ticket.identifier →
      a.owner = b.owner ∧ a.ticket = b.ticket ∧ a.address = b.address

inductive Fault where
  | authority (fault : Borrowing.Fault)
  | exchange (fault : AtomicExchange.Fault)
  | machine (fault : X86.Error)
  | reserved
  | conflictingCell
  | missingHandle
  | wrongActor
  | identityCollision
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def reserved (state : State) (allocation : Nat) : Bool :=
  (List.range state.nextHandle).any fun identifier =>
    match state.handles identifier with
    | none => false
    | some handle => decide (handle.ticket.identifier = allocation)

def compatible (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word) : Bool :=
  (List.range state.nextHandle).all fun identifier =>
    match state.handles identifier with
    | none => true
    | some handle => decide (handle.ticket.identifier ≠ ticket.identifier ∨
        (handle.owner = owner ∧ handle.ticket = ticket ∧ handle.address = address))

def allowed (state : State) (operation : Ownership.Mutation) : Bool :=
  (List.range state.nextHandle).all fun identifier =>
    match state.handles identifier with
    | none => true
    | some handle => decide (operation.target ≠ some handle.ticket.identifier)

def install (state : State) (handle : Handle) : State :=
  { state with
    nextHandle := state.nextHandle + 1
    handles := fun query => if query = state.nextHandle then some handle else state.handles query }

/-- Issuance pins the entire allocation against ordinary managed mutation and
new read loans. Existing handles can share only this exact cell and authority. -/
def issue (state : State) (owner : Nat) (ticket : Ownership.Ticket) (actor : Nat) (address : Word) :
    Except Fault (State × Nat) := do
  let allocation ← (Ownership.authorize state.shared.resources owner ticket).mapError
    (fun fault => Fault.authority (.ownership fault))
  if (state.handles state.nextHandle).isSome then throw .identityCollision
  if !compatible state owner ticket address then throw .conflictingCell
  if !Borrowing.allowed state.shared (.store owner ticket address 0) then throw (.authority .borrowed)
  if !Ownership.containsWord allocation address then throw (.authority (.ownership .outsideAllocation))
  if !atomicAddressable address then throw (.machine (.unsupportedAtomicAddress address))
  if !canStoreDWord (toMemory state.shared.resources.space) address then throw (.machine (.writeDenied address))
  return (install state ⟨owner, ticket, actor, address⟩, state.nextHandle)

def authorize (state : State) (actor identifier : Nat) : Except Fault Handle :=
  match state.handles identifier with
  | none => .error .missingHandle
  | some handle => if handle.actor = actor then .ok handle else .error .wrongActor

def close (state : State) (actor identifier : Nat) : Except Fault State := do
  let _ ← authorize state actor identifier
  return { state with handles := fun query => if query = identifier then none else state.handles query }

/-- These wrappers, rather than raw Borrowing operations, delimit admissible
environment changes while shared atomic handles exist. -/
def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  if !allowed state operation then throw .reserved
  let result ← (Borrowing.mutate state.shared operation).mapError Fault.authority
  return ({ state with shared := result.1 }, result.2)

def readBorrow (state : State) (lender : Nat) (ticket : Ownership.Ticket) (borrower : Nat) (region : Region) :
    Except Fault (State × Nat) := do
  if reserved state ticket.identifier then throw .reserved
  let result ← (Borrowing.readBorrow state.shared lender ticket borrower region).mapError Fault.authority
  return ({ state with shared := result.1 }, result.2)

def finishLoan (state : State) (borrower identifier : Nat) : Except Fault State := do
  let result ← (Borrowing.finishLoan state.shared borrower identifier).mapError Fault.authority
  return { state with shared := result }

/-- The address and underlying owner/ticket come from the authorized stored
handle. The old word is read from current shared cells at this operation. -/
def exchange (state : State) (actor identifier : Nat) (value : BitVec 32) :
    Except Fault (State × BitVec 32) := do
  let handle ← authorize state actor identifier
  let result ← (AtomicExchange.exchangeWord state.shared handle.owner handle.ticket handle.address value).mapError Fault.exchange
  return ({ state with shared := result.1 }, result.2)

theorem empty_wellFormed (shared : Borrowing.State) (valid : Borrowing.WellFormed shared) :
    WellFormed (empty shared) :=
  ⟨valid, by simp [empty], by simp [empty], by simp [empty]⟩

theorem authorize_ok (state : State) (actor identifier : Nat) (handle : Handle)
    (success : authorize state actor identifier = .ok handle) :
    state.handles identifier = some handle ∧ handle.actor = actor := by
  cases found : state.handles identifier with
  | none => simp [authorize, found] at success
  | some current =>
    by_cases owns : current.actor = actor
    · simp [authorize, found, owns] at success
      cases success
      exact ⟨rfl, owns⟩
    · simp [authorize, found, owns] at success

theorem fresh_identity (state : State) (valid : WellFormed state) : state.handles state.nextHandle = none := by
  cases found : state.handles state.nextHandle with
  | none => rfl
  | some handle => have below := (valid.handles _ _ found).1; omega

theorem allowed_sound (state : State) (operation : Ownership.Mutation)
    (valid : WellFormed state) (checked : allowed state operation = true)
    (identifier : Nat) (handle : Handle) (live : state.handles identifier = some handle) :
    operation.target ≠ some handle.ticket.identifier := by
  have below := (valid.handles _ _ live).1
  have observed := List.all_eq_true.mp checked identifier (List.mem_range.mpr below)
  simpa [live] using observed

theorem reserved_of_live (state : State) (valid : WellFormed state)
    (identifier : Nat) (handle : Handle) (live : state.handles identifier = some handle) :
    reserved state handle.ticket.identifier = true := by
  apply List.any_eq_true.mpr
  exact ⟨identifier, List.mem_range.mpr (valid.handles _ _ live).1, by simp [live]⟩

theorem compatible_sound (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (valid : WellFormed state) (checked : compatible state owner ticket address = true)
    (identifier : Nat) (handle : Handle) (live : state.handles identifier = some handle)
    (same : handle.ticket.identifier = ticket.identifier) :
    handle.owner = owner ∧ handle.ticket = ticket ∧ handle.address = address := by
  have observed := List.all_eq_true.mp checked identifier (List.mem_range.mpr (valid.handles _ _ live).1)
  simpa [live, same] using observed

end EDSL.OS.Atomics
