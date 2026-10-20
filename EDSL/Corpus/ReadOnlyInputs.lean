/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.ReadOnlyResources

set_option autoImplicit false
set_option warningAsError true

/-! Checked borrowing for any finite collection of input snapshots. These
operations supply current read loans, never snapshot values or a result proof.
Empty inputs do not inspect their pointer, owner or ticket. -/

namespace EDSL.Corpus.ReadOnlyInputs
open X86 OS OS.AddressSpace ReadOnlyResources
open BufferResources (Managed)

structure Request where
  owner : Nat
  ticket : Ownership.Ticket
  buffer : BufferCall.Buffer

structure Result (before : Managed) (worker : Nat) (requests : List Request) where
  managed : Managed
  identifiers : List Nat
  length : identifiers.length = requests.length
  held : ∀ (index : Nat) (request : Request), requests[index]? = some request → request.buffer.bytes ≠ [] →
    Threads.HasLoan managed.shared worker ((identifiers[index]?).getD 0) request.buffer.region
  resources : managed.shared.resources = before.shared.resources
  loans : ∀ identifier loan, before.shared.loans identifier = some loan →
    managed.shared.loans identifier = some loan
  history : Borrowing.History before.shared managed.shared

theorem Result.original_loan {before : Managed} {worker : Nat} {requests : List Request}
    (result : Result before worker requests) {identifier : Nat} {region : Region}
    (original : Threads.HasLoan before.shared worker identifier region) :
    Threads.HasLoan result.managed.shared worker identifier region := by
  obtain ⟨loan, live, borrower, same⟩ := original
  exact ⟨loan, result.loans _ _ live, borrower, same⟩

theorem Result.frame {before : Managed} {worker : Nat} {requests : List Request}
    (result : Result before worker requests) (address : Word) :
    result.managed.shared.resources.space.cells address =
      before.shared.resources.space.cells address :=
  congrArg (fun resources => resources.space.cells address) result.resources

theorem Result.authorize {before : Managed} {worker : Nat} {requests : List Request}
    (result : Result before worker requests) {owner : Nat} {ticket : Ownership.Ticket}
    {allocation : Ownership.Allocation}
    (authorized : Ownership.authorize before.shared.resources owner ticket = .ok allocation) :
    Ownership.authorize result.managed.shared.resources owner ticket = .ok allocation := by
  rw [result.resources]
  exact authorized

def Result.prependEmpty {before : Managed} {worker : Nat} {tail : List Request}
    (rest : Result before worker tail) (request : Request) (empty : request.buffer.bytes = []) :
    Result before worker (request :: tail) where
  managed := rest.managed
  identifiers := 0 :: rest.identifiers
  length := congrArg Nat.succ rest.length
  held := by
    intro index current present nonempty
    cases index with
    | zero =>
      have same : request = current := Option.some.inj present
      cases same
      exact False.elim (nonempty empty)
    | succ index => exact rest.held index current present nonempty
  resources := rest.resources
  loans := rest.loans
  history := rest.history

def Result.prependBorrowed {before : Managed} {worker : Nat} {tail : List Request}
    (request : Request) (first : Borrowed before worker request.buffer.region)
    (rest : Result first.managed worker tail) : Result before worker (request :: tail) where
  managed := rest.managed
  identifiers := first.identifier :: rest.identifiers
  length := congrArg Nat.succ rest.length
  held := by
    intro index current present nonempty
    cases index with
    | zero =>
      have same : request = current := Option.some.inj present
      cases same
      exact rest.original_loan first.held
    | succ index => exact rest.held index current present nonempty
  resources := rest.resources.trans first.resources
  loans := fun identifier loan live => rest.loans _ _ (first.loans identifier loan live)
  history := history_trans first.history rest.history

/-- Every positive request executes the real checked readBorrow operation.
All previous loans, allocation/epoch metadata and complete memory survive. -/
def borrow (before : Managed) (worker : Nat) :
    (requests : List Request) → Except Borrowing.Fault (Result before worker requests)
  | [] => .ok {
      managed := before
      identifiers := []
      length := rfl
      held := by intro index request present _; simp at present
      resources := rfl
      loans := fun _ _ live => live
      history := .refl }
  | request :: tail => do
      if empty : request.buffer.bytes = [] then
        let rest ← borrow before worker tail
        return rest.prependEmpty request empty
      else
        let first ← ReadOnlyResources.borrow before request.owner request.ticket worker request.buffer.region
        let rest ← borrow first.managed worker tail
        return Result.prependBorrowed request first rest

/-- Arbitrary empty pointers and invalid unused ticket identifiers cause no
manager operation: all-empty borrowing succeeds with the exact original state. -/
theorem all_empty (before : Managed) (worker : Nat) (requests : List Request) :
    (∀ request ∈ requests, request.buffer.bytes = []) →
      ∃ result, borrow before worker requests = .ok result ∧
        result.managed = before ∧ result.identifiers = List.replicate requests.length 0 := by
  induction requests with
  | nil =>
    intro _
    exact ⟨_, rfl, rfl, rfl⟩
  | cons request tail induction =>
    intro empty
    have head := empty request (by simp)
    have remaining : ∀ current ∈ tail, current.buffer.bytes = [] :=
      fun current member => empty current (by simp [member])
    obtain ⟨rest, success, unchanged, identifiers⟩ := induction remaining
    refine ⟨rest.prependEmpty request head, ?_, unchanged, ?_⟩
    · rw [borrow, dite_eq_left head, success]
      rfl
    · change 0 :: rest.identifiers = 0 :: List.replicate tail.length 0
      exact congrArg (List.cons 0) identifiers

#print axioms borrow
#print axioms Result.original_loan
#print axioms Result.frame
#print axioms Result.authorize
#print axioms all_empty
end EDSL.Corpus.ReadOnlyInputs
#audit_edsl
