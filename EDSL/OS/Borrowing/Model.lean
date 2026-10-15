/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Interference
import EDSL.X86.Buffer

namespace EDSL.OS.Borrowing
open X86 AddressSpace

/-- Logical shared read authority. The entire referenced allocation is frozen
while this record is live, even when the requested region is smaller. -/
structure Loan where
  ticket : Ownership.Ticket
  lender : Nat
  borrower : Nat
  region : Region
  deriving DecidableEq, Repr

structure State where
  resources : Ownership.World
  nextLoan : Nat
  loans : Nat → Option Loan

def empty (resources : Ownership.World) : State := ⟨resources, 0, fun _ => none⟩

def Subregion (inner outer : Region) : Prop :=
  outer.base.toNat ≤ inner.base.toNat ∧
    inner.base.toNat + inner.length ≤ outer.base.toNat + outer.length

instance (inner outer : Region) : Decidable (Subregion inner outer) :=
  inferInstanceAs (Decidable (_ ∧ _))

def allReadable (space : Space) (region : Region) : Bool :=
  region.addresses.all fun address =>
    match space.cells address with
    | none => false
    | some cell => cell.permissions.readable

/-- Validity refers to actual mapped readable cells; no caller-supplied snapshot
is trusted as a substitute for those cells. -/
def ValidLoan (resources : Ownership.World) (loan : Loan) : Prop :=
  ∃ allocation, resources.allocations loan.ticket.identifier = some allocation ∧
    allocation.owner = loan.lender ∧ allocation.epoch = loan.ticket.epoch ∧
    Subregion loan.region allocation.region ∧ loan.region.valid = true ∧
    ∀ address, loan.region.Contains address →
      ∃ cell, resources.space.cells address = some cell ∧ cell.permissions.readable = true

def WellFormed (state : State) : Prop :=
  Ownership.WellFormed state.resources ∧
  ∀ identifier loan, state.loans identifier = some loan →
    identifier < state.nextLoan ∧ ValidLoan state.resources loan

inductive Fault where
  | ownership (fault : Ownership.Fault)
  | invalidRegion
  | outsideAllocation
  | unreadable
  | identityCollision
  | borrowed
  | missingLoan
  | wrongBorrower
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def installLoan (state : State) (loan : Loan) : State :=
  { state with
    nextLoan := state.nextLoan + 1
    loans := fun query => if query = state.nextLoan then some loan else state.loans query }

def readBorrow (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) : Except Fault (State × Nat) := do
  let allocation ← (Ownership.authorize state.resources lender ticket).mapError Fault.ownership
  if (state.loans state.nextLoan).isSome then throw .identityCollision
  if !region.valid then throw .invalidRegion
  if !decide (Subregion region allocation.region) then throw .outsideAllocation
  if !allReadable state.resources.space region then throw .unreadable
  return (installLoan state ⟨ticket, lender, borrower, region⟩, state.nextLoan)

/-- Only a stored live loan with the requested borrower supplies read authority.
IDs and principal names are proof data, not authenticated runtime identities. -/
def authorize (state : State) (borrower identifier : Nat) : Except Fault Loan :=
  match state.loans identifier with
  | none => .error .missingLoan
  | some loan => if loan.borrower = borrower then .ok loan else .error .wrongBorrower

def finishLoan (state : State) (borrower identifier : Nat) : Except Fault State := do
  let _ ← authorize state borrower identifier
  return { state with loans := fun query => if query = identifier then none else state.loans query }

/-- The bounded scan covers every live loan under WellFormed. Freezing uses the
allocation identity, including loans on other subregions of that allocation. -/
def allowed (state : State) (operation : Ownership.Mutation) : Bool :=
  (List.range state.nextLoan).all fun identifier =>
    match state.loans identifier with
    | none => true
    | some loan => decide (operation.target ≠ some loan.ticket.identifier)

/-- All allocation changes enter through this gate. Raw Ownership operations
and arbitrary machine interference are outside the borrowing discipline. -/
def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  if !allowed state operation then throw .borrowed
  let result ← (operation.run state.resources).mapError Fault.ownership
  return ({ state with resources := result.1 }, result.2)

theorem empty_wellFormed (resources : Ownership.World) (valid : Ownership.WellFormed resources) :
    WellFormed (empty resources) := ⟨valid, by simp [empty]⟩

theorem subregion_inside {inner outer : Region} (fits : Subregion inner outer)
    {address : Word} (inside : inner.Contains address) : outer.Contains address := by
  have lower := fits.1
  have upper := fits.2
  have start := inside.1
  have stop := inside.2
  exact ⟨by omega, by omega⟩

theorem allReadable_inside (space : Space) (region : Region)
    (checked : allReadable space region = true) (address : Word) (inside : region.Contains address) :
    ∃ cell, space.cells address = some cell ∧ cell.permissions.readable = true := by
  have observed := List.all_eq_true.mp checked address (contains_mem_addresses region address inside)
  cases found : space.cells address with
  | none => simp [found] at observed
  | some cell => exact ⟨cell, rfl, by simpa [found] using observed⟩

theorem authorize_ok (state : State) (borrower identifier : Nat) (loan : Loan)
    (success : authorize state borrower identifier = .ok loan) :
    state.loans identifier = some loan ∧ loan.borrower = borrower := by
  cases found : state.loans identifier with
  | none => simp [authorize, found] at success
  | some entry =>
    by_cases owns : entry.borrower = borrower
    · simp [authorize, found, owns] at success
      cases success
      exact ⟨rfl, owns⟩
    · simp [authorize, found, owns] at success

theorem allowed_sound (state : State) (operation : Ownership.Mutation)
    (valid : WellFormed state) (checked : allowed state operation = true)
    (identifier : Nat) (loan : Loan) (live : state.loans identifier = some loan) :
    operation.target ≠ some loan.ticket.identifier := by
  have below := (valid.2 identifier loan live).1
  have observed := List.all_eq_true.mp checked identifier (List.mem_range.mpr below)
  simpa [live] using observed

end EDSL.OS.Borrowing
