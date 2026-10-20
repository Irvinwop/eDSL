/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Facts

namespace EDSL.OS.Borrowing
open X86 AddressSpace

/-- Exactly the successful operations of the shared-read borrowing discipline.
Raw resource updates and arbitrary concurrent interference are excluded. -/
inductive Step : State → State → Prop where
  | readBorrow {before lender ticket borrower region result}
      (success : Borrowing.readBorrow before lender ticket borrower region = .ok result) :
      Step before result.1
  | finishLoan {before borrower identifier after}
      (success : Borrowing.finishLoan before borrower identifier = .ok after) : Step before after
  | mutate {before operation result}
      (success : Borrowing.mutate before operation = .ok result) : Step before result.1

inductive History : State → State → Prop where
  | refl {state} : History state state
  | next {before middle after} (first : Step before middle) (tail : History middle after) :
      History before after

/-- Old loan IDs can disappear but cannot be reissued. A surviving loan retains
its stored record and every actual cell, including its permissions. -/
def Advances (before after : State) : Prop :=
  before.nextLoan ≤ after.nextLoan ∧
  ∀ identifier, identifier < before.nextLoan → ∀ loan,
    after.loans identifier = some loan →
    before.loans identifier = some loan ∧
    ∀ address, loan.region.Contains address →
      after.resources.space.cells address = before.resources.space.cells address

theorem advances_refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ _ live => ⟨live, fun _ _ => rfl⟩⟩

theorem advances_trans {before middle after : State}
    (first : Advances before middle) (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below loan live
  have nextLoan := first.1
  obtain ⟨middleAt, lastCells⟩ := last.2 identifier (by omega) loan live
  obtain ⟨beforeAt, firstCells⟩ := first.2 identifier below loan middleAt
  exact ⟨beforeAt, fun address inside => (lastCells address inside).trans (firstCells address inside)⟩

theorem Step.wellFormed {before after : State} (step : Step before after) (valid : WellFormed before) :
    WellFormed after := by
  cases step with
  | readBorrow success => exact (readBorrow_wellFormed _ _ _ _ _ _ valid success).1
  | finishLoan success => exact (finishLoan_wellFormed _ _ _ _ valid success).1
  | mutate success => exact mutate_wellFormed _ _ _ valid success

theorem Step.advances {before after : State} (step : Step before after) (valid : WellFormed before) :
    Advances before after := by
  cases step with
  | readBorrow success =>
    obtain ⟨_, _, _, _, _, same⟩ := readBorrow_ok _ _ _ _ _ _ success
    rw [same]
    refine ⟨by simp [installLoan], ?_⟩
    intro identifier below loan live
    have old : identifier ≠ before.nextLoan := by omega
    exact ⟨by simpa [installLoan, old] using live, fun _ _ => rfl⟩
  | @finishLoan borrower identifier after success =>
    obtain ⟨_, _, same⟩ := finishLoan_ok _ _ _ _ success
    subst after
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ loan live
    by_cases removed : query = identifier
    · simp [removed] at live
    · exact ⟨by simpa [removed] using live, fun _ _ => rfl⟩
  | @mutate operation result success =>
    obtain ⟨checked, resources, changed, same⟩ := mutate_ok _ _ _ success
    subst result
    refine ⟨Nat.le_refl _, ?_⟩
    intro identifier _ loan live
    have beforeAt : before.loans identifier = some loan := live
    obtain ⟨_, allocation, allocationAt, _, _, fits, _, _⟩ := valid.2 identifier loan beforeAt
    have preserves := operation.run_preserves _ _ _ valid.1 changed
      (allowed_sound before operation valid checked identifier loan beforeAt)
    obtain ⟨_, cells⟩ := preserves allocation allocationAt
    exact ⟨beforeAt, fun address inside => cells address (subregion_inside fits inside)⟩

theorem History.wellFormed {before after : State} (history : History before after)
    (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem History.advances {before after : State} (history : History before after)
    (valid : WellFormed before) : Advances before after := by
  induction history with
  | refl => exact advances_refl _
  | next first _ induction =>
    exact advances_trans (first.advances valid) (induction (first.wellFormed valid))

/-- This endpoint test is enough: an initially issued ID that remains live has
the same record and byte/permission observations across the entire history. -/
theorem History.loan_stable {before after : State} (history : History before after)
    (valid : WellFormed before) (identifier : Nat) (below : identifier < before.nextLoan)
    (loan : Loan) (live : after.loans identifier = some loan) :
    before.loans identifier = some loan ∧
    ∀ address, loan.region.Contains address →
      after.resources.space.cells address = before.resources.space.cells address :=
  (history.advances valid).2 identifier below loan live

/-- A removed ID is below the fresh-ID frontier, so no later admitted operation
can install another record with that identity. -/
def Revoked (state : State) (identifier : Nat) : Prop :=
  identifier < state.nextLoan ∧ state.loans identifier = none

theorem Revoked.persists {before after : State} {identifier : Nat}
    (revoked : Revoked before identifier) (valid : WellFormed before)
    (history : History before after) : Revoked after identifier := by
  have advances := history.advances valid
  have below := revoked.1
  have frontier := advances.1
  refine ⟨by omega, ?_⟩
  cases found : after.loans identifier with
  | none => rfl
  | some loan =>
    have original := (advances.2 identifier revoked.1 loan found).1
    rw [revoked.2] at original
    cases original

theorem finishLoan_revokes (state : State) (borrower identifier : Nat) (result : State)
    (valid : WellFormed state) (success : finishLoan state borrower identifier = .ok result) :
    Revoked result identifier := by
  obtain ⟨loan, authorized, same⟩ := finishLoan_ok _ _ _ _ success
  have found := (authorize_ok _ _ _ _ authorized).1
  have below := (valid.2 identifier loan found).1
  subst result
  exact ⟨below, by simp⟩

/-- Finishing a loan revokes that exact ID permanently, even after subsequent
loans are issued. Copying the old number cannot restore modeled authority. -/
theorem finished_for_history {before middle after : State} (borrower identifier : Nat)
    (valid : WellFormed before) (finished : finishLoan before borrower identifier = .ok middle)
    (history : History middle after) : Revoked after identifier :=
  (finishLoan_revokes before borrower identifier middle valid finished).persists
    ((finishLoan_wellFormed _ _ _ _ valid finished).1) history

theorem Revoked.unauthorized {state : State} {identifier : Nat} (revoked : Revoked state identifier)
    (borrower : Nat) : authorize state borrower identifier = .error .missingLoan := by
  simp [authorize, revoked.2]

end EDSL.OS.Borrowing
