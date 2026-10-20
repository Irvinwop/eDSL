/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Preservation

namespace EDSL.OS.Atomics
open X86 AddressSpace

/-- All admitted environment transitions pass the reservation guards.
Raw Borrowing/Ownership operations are not environment transitions here. -/
inductive Step : State → State → Prop where
  | issue {before owner ticket actor address result}
      (success : Atomics.issue before owner ticket actor address = .ok result) : Step before result.1
  | close {before actor identifier after}
      (success : Atomics.close before actor identifier = .ok after) : Step before after
  | exchange {before actor identifier value result}
      (success : Atomics.exchange before actor identifier value = .ok result) : Step before result.1
  | mutate {before operation result}
      (success : Atomics.mutate before operation = .ok result) : Step before result.1
  | readBorrow {before lender ticket borrower region result}
      (success : Atomics.readBorrow before lender ticket borrower region = .ok result) : Step before result.1
  | finishLoan {before borrower identifier after}
      (success : Atomics.finishLoan before borrower identifier = .ok after) : Step before after
  | idle {state} : Step state state

inductive History : State → State → Prop where
  | refl {state} : History state state
  | next {before middle after} (first : Step before middle) (tail : History middle after) : History before after

theorem Step.wellFormed {before after : State} (step : Step before after) (valid : WellFormed before) :
    WellFormed after := by
  cases step with
  | issue success => exact (issue_wellFormed _ _ _ _ _ _ valid success).1
  | close success => exact close_wellFormed _ _ _ _ valid success
  | exchange success => exact exchange_wellFormed _ _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | readBorrow success => exact readBorrow_wellFormed _ _ _ _ _ _ valid success
  | finishLoan success => exact finishLoan_wellFormed _ _ _ _ valid success
  | idle => exact valid

theorem History.wellFormed {before after : State} (history : History before after) (valid : WellFormed before) :
    WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

/-- Surviving handles keep their stored authority/actor/address records; IDs
below the monotonically increasing frontier can never be reinstalled. Values
at the shared cell are deliberately not snapshots stored in a handle. -/
def Advances (before after : State) : Prop :=
  before.nextHandle ≤ after.nextHandle ∧
  ∀ identifier, identifier < before.nextHandle → ∀ handle,
    after.handles identifier = some handle → before.handles identifier = some handle

theorem advances_refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ _ live => live⟩

theorem advances_trans {before middle after : State} (first : Advances before middle)
    (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below handle live
  exact first.2 identifier below handle (last.2 identifier (by have next := first.1; omega) handle live)

theorem Step.advances {before after : State} (step : Step before after) : Advances before after := by
  cases step with
  | issue success =>
    obtain ⟨_, _, _, _, _, _, _, same⟩ := issue_ok _ _ _ _ _ _ success
    rw [same]
    refine ⟨by simp [install], ?_⟩
    intro identifier below handle live
    have old : identifier ≠ before.nextHandle := by omega
    simpa [install, old] using live
  | close success =>
    obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
    subst_vars
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ handle live
    dsimp only at live
    split at live
    · cases live
    · exact live
  | exchange success =>
    obtain ⟨_, _, _, _, same⟩ := exchange_ok _ _ _ _ _ success
    rw [same]
    exact advances_refl _
  | mutate success =>
    obtain ⟨_, _, _, same⟩ := mutate_ok _ _ _ success
    rw [same]
    exact advances_refl _
  | readBorrow success =>
    obtain ⟨_, _, _, same⟩ := readBorrow_ok _ _ _ _ _ _ success
    rw [same]
    exact advances_refl _
  | finishLoan success =>
    obtain ⟨_, _, same⟩ := finishLoan_ok _ _ _ _ success
    rw [same]
    exact advances_refl _
  | idle => exact advances_refl _

theorem History.advances {before after : State} (history : History before after) : Advances before after := by
  induction history with
  | refl => exact advances_refl _
  | next first _ induction => exact advances_trans first.advances induction

def Revoked (state : State) (identifier : Nat) : Prop :=
  identifier < state.nextHandle ∧ state.handles identifier = none

theorem Revoked.persists {before after : State} {identifier : Nat}
    (revoked : Revoked before identifier) (history : History before after) : Revoked after identifier := by
  have advances := history.advances
  refine ⟨by have a := revoked.1; have b := advances.1; omega, ?_⟩
  cases found : after.handles identifier with
  | none => rfl
  | some handle =>
    have original := advances.2 identifier revoked.1 handle found
    rw [revoked.2] at original
    cases original

theorem close_revokes (state : State) (actor identifier : Nat) (after : State)
    (valid : WellFormed state) (success : close state actor identifier = .ok after) : Revoked after identifier := by
  obtain ⟨handle, authorized, same⟩ := close_ok _ _ _ _ success
  have live := (authorize_ok _ _ _ _ authorized).1
  subst after
  exact ⟨(valid.handles _ _ live).1, by simp⟩

theorem closed_for_history {before middle after : State} (actor identifier : Nat)
    (valid : WellFormed before) (closed : close before actor identifier = .ok middle)
    (history : History middle after) : Revoked after identifier :=
  (close_revokes before actor identifier middle valid closed).persists history

theorem Revoked.unauthorized {state : State} {identifier : Nat} (revoked : Revoked state identifier) (actor : Nat) :
    authorize state actor identifier = .error .missingHandle := by
  simp [authorize, revoked.2]

theorem Step.borrowing {before after : State} (step : Step before after) :
    Borrowing.History before.shared after.shared := by
  cases step with
  | issue success =>
    obtain ⟨_, _, _, _, _, _, _, same⟩ := issue_ok _ _ _ _ _ _ success
    rw [same]
    exact .refl
  | close success =>
    obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
    rw [same]
    exact .refl
  | exchange success =>
    obtain ⟨_, _, _, exchanged, same⟩ := exchange_ok _ _ _ _ _ success
    rw [same]
    exact .next (.mutate (AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchanged)) .refl
  | mutate success =>
    obtain ⟨_, _, changed, same⟩ := mutate_ok _ _ _ success
    rw [same]
    exact .next (.mutate changed) .refl
  | readBorrow success =>
    obtain ⟨_, _, borrowed, same⟩ := readBorrow_ok _ _ _ _ _ _ success
    rw [same]
    exact .next (.readBorrow borrowed) .refl
  | finishLoan success =>
    obtain ⟨_, finished, same⟩ := finishLoan_ok _ _ _ _ success
    rw [same]
    exact .next (.finishLoan finished) .refl
  | idle => exact .refl

theorem borrowing_trans {before middle after : Borrowing.State}
    (first : Borrowing.History before middle) (last : Borrowing.History middle after) :
    Borrowing.History before after := by
  induction first with
  | refl => exact last
  | next first _ induction => exact .next first (induction last)

theorem History.borrowing {before after : State} (history : History before after) :
    Borrowing.History before.shared after.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction => exact borrowing_trans first.borrowing induction

theorem History.loan_stable {before after : State} (history : History before after)
    (valid : WellFormed before) (identifier : Nat) (below : identifier < before.shared.nextLoan)
    (loan : Borrowing.Loan) (live : after.shared.loans identifier = some loan) :
    before.shared.loans identifier = some loan ∧
    ∀ query, loan.region.Contains query → after.shared.resources.space.cells query = before.shared.resources.space.cells query :=
  history.borrowing.loan_stable valid.shared identifier below loan live

/-- A live reservation forbids all targeted ordinary mutations, even when they
would only affect another subregion of the same allocation. -/
theorem mutate_reserved (state : State) (operation : Ownership.Mutation) (valid : WellFormed state)
    (identifier : Nat) (handle : Handle) (live : state.handles identifier = some handle)
    (target : operation.target = some handle.ticket.identifier) :
    mutate state operation = .error .reserved := by
  have blocked : allowed state operation = false := by
    cases checked : allowed state operation with
    | false => rfl
    | true => exact False.elim ((allowed_sound state operation valid checked identifier handle live) target)
  simp [mutate, blocked]

theorem readBorrow_reserved (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (valid : WellFormed state) (identifier : Nat) (handle : Handle)
    (live : state.handles identifier = some handle) (same : ticket.identifier = handle.ticket.identifier) :
    readBorrow state lender ticket borrower region = .error .reserved := by
  have pinned := reserved_of_live state valid identifier handle live
  simp [readBorrow, same, pinned]

theorem issue_reader_excluded (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (address : Word) (valid : WellFormed state) (loanId : Nat) (loan : Borrowing.Loan)
    (live : state.shared.loans loanId = some loan) (same : loan.ticket.identifier = ticket.identifier)
    (result : State × Nat) : issue state owner ticket actor address ≠ .ok result := by
  intro success
  obtain ⟨_, _, _, checked, _, _, _, _⟩ := issue_ok _ _ _ _ _ _ success
  have different := Borrowing.allowed_sound _ _ valid.shared checked loanId loan live
  exact different (congrArg some same.symm)

end EDSL.OS.Atomics
