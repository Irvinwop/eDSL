/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Preservation
import EDSL.OS.Atomics.History

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- Only checked current-resource operations are admitted. In particular there
is no constructor embedding a raw legacy step. RMW labels are operation outputs,
not independently supplied claims about an ordinary store. -/
inductive Step : State → Option Event → State → Prop where
  | enroll {before owner ticket address result}
      (success : Atomics64.enroll before owner ticket address = .ok result) : Step before none result.1
  | issue {before owner identifier actor result}
      (success : Atomics64.issue before owner identifier actor = .ok result) : Step before none result.1
  | close {before actor identifier after}
      (success : Atomics64.close before actor identifier = .ok after) : Step before none after
  | retire {before owner identifier after}
      (success : Atomics64.retire before owner identifier = .ok after) : Step before none after
  | mutate {before operation result}
      (success : Atomics64.mutate before operation = .ok result) : Step before none result.1
  | readBorrow {before lender ticket borrower region result}
      (success : Atomics64.readBorrow before lender ticket borrower region = .ok result) : Step before none result.1
  | finishLoan {before borrower identifier after}
      (success : Atomics64.finishLoan before borrower identifier = .ok after) : Step before none after
  | issue32 {before owner ticket actor address result}
      (success : Atomics64.issue32 before owner ticket actor address = .ok result) : Step before none result.1
  | close32 {before actor identifier after}
      (success : Atomics64.close32 before actor identifier = .ok after) : Step before none after
  | logicalDiscard {before actor identifier mask result}
      (success : Atomics64.logicalDiscard before actor identifier mask = .ok result) :
      Step before (some result.2) result.1
  | idle {state} : Step state none state

/-- The full schedule retains administrative positions and every actual event.
This general history permits retirement and re-enrollment: it does not assert
that a raw address denotes one persistent cell for the entire schedule. -/
inductive History : State → List (Option Event) → State → Prop where
  | refl {state} : History state [] state
  | next {before middle after label labels} (first : Step before label middle)
      (tail : History middle labels after) : History before (label :: labels) after

theorem Step.wellFormed {before after : State} {label : Option Event}
    (step : Step before label after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | enroll success => exact (enroll_wellFormed _ _ _ _ _ valid success).1
  | issue success => exact (issue_wellFormed _ _ _ _ _ valid success).1
  | close success => exact close_wellFormed _ _ _ _ valid success
  | retire success => exact retire_wellFormed _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | readBorrow success => exact readBorrow_wellFormed _ _ _ _ _ _ valid success
  | finishLoan success => exact finishLoan_wellFormed _ _ _ _ valid success
  | issue32 success => exact issue32_wellFormed _ _ _ _ _ _ valid success
  | close32 success => exact close32_wellFormed _ _ _ _ valid success
  | logicalDiscard success => exact logicalDiscard_wellFormed _ _ _ _ _ valid success
  | idle => exact valid

theorem Step.advances {before after : State} {label : Option Event}
    (step : Step before label after) : Advances before after := by
  cases step with
  | enroll success => exact enroll_advances _ _ _ _ _ success
  | issue success => exact issue_advances _ _ _ _ _ success
  | close success => exact close_advances _ _ _ _ success
  | retire success => exact retire_advances _ _ _ _ success
  | mutate success => exact mutate_advances _ _ _ success
  | readBorrow success => exact readBorrow_advances _ _ _ _ _ _ success
  | finishLoan success => exact finishLoan_advances _ _ _ _ success
  | issue32 success => exact issue32_advances _ _ _ _ _ _ success
  | close32 success => exact close32_advances _ _ _ _ success
  | logicalDiscard success => exact logicalDiscard_advances _ _ _ _ _ success
  | idle => exact .refl _

/-- A visible event is tied to one real checked RMW, including its actual
current read, fixed OR operation, mask, actor and handle. -/
theorem Step.event_sound {before after : State} {event : Event}
    (step : Step before (some event) after) :
    ∃ actor identifier mask, Atomics64.logicalDiscard before actor identifier mask = .ok (after, event) ∧
      RMWTransition64 (toMemory before.legacy.shared.resources.space) event.logical.event
        (toMemory after.legacy.shared.resources.space) ∧
      event.logical.op = .bor ∧ event.logical.mask = mask ∧
      event.logical.event.after = event.logical.event.before ||| mask ∧
      event.actor = actor ∧ event.handle = identifier := by
  cases step with
  | @logicalDiscard actor identifier mask result success =>
    have sound := logicalDiscard_sound _ _ _ _ _ success
    exact ⟨actor, identifier, mask, success, sound.1, sound.2.1, sound.2.2.1,
      sound.2.2.2.1, sound.2.2.2.2⟩

theorem Step.borrowing {before after : State} {label : Option Event}
    (step : Step before label after) :
    Borrowing.History before.legacy.shared after.legacy.shared := by
  cases step with
  | enroll success =>
    obtain ⟨_, _, _, _, same⟩ := enroll_ok _ _ _ _ _ success
    rw [same]
    exact .refl
  | issue success =>
    obtain ⟨_, _, same⟩ := issue_ok _ _ _ _ _ success
    rw [same]
    exact .refl
  | close success =>
    obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
    rw [same]
    exact .refl
  | retire success =>
    obtain ⟨_, _, _, same⟩ := retire_ok _ _ _ _ success
    rw [same]
    exact .refl
  | mutate success =>
    obtain ⟨_, _, changed, same⟩ := mutate_ok _ _ _ success
    rw [same]
    exact (Atomics.Step.mutate changed).borrowing
  | readBorrow success =>
    obtain ⟨_, _, borrowed, same⟩ := readBorrow_ok _ _ _ _ _ _ success
    rw [same]
    exact (Atomics.Step.readBorrow borrowed).borrowing
  | finishLoan success =>
    obtain ⟨_, finished, same⟩ := finishLoan_ok _ _ _ _ success
    rw [same]
    exact (Atomics.Step.finishLoan finished).borrowing
  | issue32 success =>
    obtain ⟨_, _, issued, same⟩ := issue32_ok _ _ _ _ _ _ success
    rw [same]
    exact (Atomics.Step.issue issued).borrowing
  | close32 success =>
    obtain ⟨_, closed, same⟩ := close32_ok _ _ _ _ success
    rw [same]
    exact (Atomics.Step.close closed).borrowing
  | logicalDiscard success =>
    obtain ⟨_, _, _, legacy, _, _, stored, same⟩ := logicalDiscard_ok _ _ _ _ _ success
    rw [same]
    exact (Atomics.Step.mutate stored).borrowing
  | idle => exact .refl

theorem History.wellFormed {before after : State} {labels : List (Option Event)}
    (history : History before labels after) (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem History.advances {before after : State} {labels : List (Option Event)}
    (history : History before labels after) : Advances before after := by
  induction history with
  | refl => exact .refl _
  | next first _ induction => exact first.advances.trans induction

theorem History.trans {before middle after : State} {firstLabels lastLabels : List (Option Event)}
    (first : History before firstLabels middle) (last : History middle lastLabels after) :
    History before (firstLabels ++ lastLabels) after := by
  induction first with
  | refl => exact last
  | next first _ induction => exact .next first (induction last)

theorem History.borrowing {before after : State} {labels : List (Option Event)}
    (history : History before labels after) :
    Borrowing.History before.legacy.shared after.legacy.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction => exact Atomics.borrowing_trans first.borrowing induction

theorem History.loan_stable {before after : State} {labels : List (Option Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (below : identifier < before.legacy.shared.nextLoan)
    (loan : Borrowing.Loan) (live : after.legacy.shared.loans identifier = some loan) :
    before.legacy.shared.loans identifier = some loan ∧
    ∀ query, loan.region.Contains query →
      after.legacy.shared.resources.space.cells query = before.legacy.shared.resources.space.cells query :=
  history.borrowing.loan_stable valid.legacy.shared identifier below loan live

theorem History.cell_revoked {before after : State} {labels : List (Option Event)}
    (history : History before labels after) {identifier : CellId64}
    (revoked : CellRevoked before identifier) : CellRevoked after identifier :=
  revoked.persists history.advances

theorem History.handle_revoked {before after : State} {labels : List (Option Event)}
    (history : History before labels after) {identifier : HandleId64}
    (revoked : HandleRevoked before identifier) : HandleRevoked after identifier :=
  revoked.persists history.advances

theorem History.loan_revoked {before after : State} {labels : List (Option Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Nat}
    (revoked : Borrowing.Revoked before.legacy.shared identifier) :
    Borrowing.Revoked after.legacy.shared identifier :=
  revoked.persists valid.legacy.shared history.borrowing

theorem closed_for_history {before middle after : State} {labels : List (Option Event)}
    (actor : Nat) (identifier : HandleId64) (valid : WellFormed before)
    (closed : close before actor identifier = .ok middle) (history : History middle labels after) :
    logicalDiscard after actor identifier = fun _ => .error .missingHandle := by
  funext mask
  exact (history.handle_revoked (close_revokes _ _ _ _ valid closed)).logicalDiscard_denied actor mask

theorem retired_for_history {before middle after : State} {labels : List (Option Event)}
    (owner : Nat) (identifier : CellId64) (valid : WellFormed before)
    (retired : retire before owner identifier = .ok middle) (history : History middle labels after) :
    CellRevoked after identifier :=
  history.cell_revoked (retire_revokes _ _ _ _ valid retired)

theorem finished_for_history {before middle after : State} {labels : List (Option Event)}
    (borrower identifier : Nat) (valid : WellFormed before)
    (finished : finishLoan before borrower identifier = .ok middle) (history : History middle labels after) :
    Borrowing.Revoked after.legacy.shared identifier := by
  obtain ⟨legacy, finishedLegacy, same⟩ := finishLoan_ok _ _ _ _ finished
  have revoked := Borrowing.finished_for_history borrower identifier valid.legacy.shared
    (by
      obtain ⟨_, finishedShared, legacySame⟩ := Atomics.finishLoan_ok _ _ _ _ finishedLegacy
      rw [same, legacySame]
      exact finishedShared)
    history.borrowing
  exact revoked

end EDSL.OS.Atomics64
