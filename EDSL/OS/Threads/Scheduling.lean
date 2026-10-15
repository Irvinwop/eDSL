/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Progress

namespace EDSL.OS.Threads
open X86

def Phase.remaining : Phase → Nat
  | .loading _ => 2
  | .returning _ => 1
  | .completed _ => 0

theorem dispatch_decreases (state : State) (identifier : Nat) (result : State)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    ∃ before after, state.workers identifier = some before ∧ result.workers identifier = some after ∧
      before.phase.remaining = after.phase.remaining + 1 := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    cases phase : worker.phase with
    | loading context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_loading _ _ _ _ found workerValid phase))
      rw [same]
      exact ⟨worker, { worker with phase := .returning (worker.entry.loaded worker.value) },
        rfl, by simp [replace], by simp [phase, Phase.remaining]⟩
    | returning context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ found workerValid phase))
      rw [same]
      exact ⟨worker, { worker with phase := .completed (worker.entry.returned worker.value worker.returnAddress) },
        rfl, by simp [replace], by simp [phase, Phase.remaining]⟩
    | completed context => rw [dispatch_completed _ _ _ _ found phase] at success; cases success

/-- Counts actual successful machine dispatches, allowing arbitrary peer
preemption between them. No instruction of the chosen worker is skipped. -/
theorem schedule_remaining (state : State) (selections : List Nat) (result : State)
    (valid : WellFormed state) (success : schedule state selections = .ok result)
    (identifier : Nat) (worker : Worker) (live : state.workers identifier = some worker) :
    ∃ final, result.workers identifier = some final ∧
      worker.phase.remaining = selections.count identifier + final.phase.remaining := by
  induction selections generalizing state worker with
  | nil =>
    simp [schedule] at success
    subst result
    exact ⟨worker, live, by simp⟩
  | cons selected rest induction =>
    cases first : dispatch state selected with
    | error fault => simp [schedule, first] at success
    | ok next =>
      simp [schedule, first] at success
      have nextValid := dispatch_wellFormed state selected next valid first
      by_cases chosen : selected = identifier
      · subst selected
        obtain ⟨before, after, old, now, decrease⟩ := dispatch_decreases state identifier next valid first
        have same := Option.some.inj (old.symm.trans live)
        cases same
        obtain ⟨final, finalAt, remaining⟩ := induction next nextValid success after now
        refine ⟨final, finalAt, ?_⟩
        simp only [List.count_cons_self]
        omega
      · have now : next.workers identifier = some worker :=
          ((dispatch_frame state selected next valid first).2.2 identifier (Ne.symm chosen)).trans live
        obtain ⟨final, finalAt, remaining⟩ := induction next nextValid success worker now
        refine ⟨final, finalAt, ?_⟩
        simpa [List.count_cons, chosen, Ne.symm chosen] using remaining

/-- Two selections suffice under arbitrary successful peer instruction
interleavings. A selection of a missing/completed worker still reports failure. -/
theorem schedule_two_completes (state : State) (selections : List Nat) (result : State)
    (valid : WellFormed state) (success : schedule state selections = .ok result)
    (identifier : Nat) (worker : Worker) (context : Context) (live : state.workers identifier = some worker)
    (loading : worker.phase = .loading context) (selectedTwice : selections.count identifier = 2) :
    ∃ final completed, result.workers identifier = some final ∧ final.phase = .completed completed ∧
      ∃ joined, join result worker.parent identifier = .ok joined ∧ joined.2 = worker.value.setWidth 64 := by
  obtain ⟨final, found, remaining⟩ := schedule_remaining state selections result valid success identifier worker live
  rw [loading, selectedTwice] at remaining
  have finalValid := schedule_wellFormed state selections result valid success
  cases phase : final.phase with
  | loading context => simp [phase, Phase.remaining] at remaining
  | returning context => simp [phase, Phase.remaining] at remaining
  | completed completed =>
    obtain ⟨joined, joinedAt⟩ := join_enabled result identifier final completed finalValid found phase
    have parentBefore := ((valid.2 _ _ live).2).1
    have parentAfter := ((finalValid.2 _ _ found).2).1
    have matchesParent : final.parent = worker.parent := parentAfter.trans parentBefore.symm
    rw [matchesParent] at joinedAt
    exact ⟨final, completed, found, phase, joined, joinedAt,
      joined_value_for_history (schedule_history state selections result success) valid identifier worker live
        worker.parent joined joinedAt⟩

/-- Joined worker loans remain revoked across all later admitted thread steps. -/
theorem joined_loans_for_history {before middle after : State} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok (middle, result))
    (history : History middle after) :
    ∃ worker, before.workers identifier = some worker ∧
      Borrowing.Revoked after.shared worker.dataLoan ∧ Borrowing.Revoked after.shared worker.codeLoan ∧
      Borrowing.Revoked after.shared worker.stackLoan := by
  obtain ⟨worker, live, data, code, stack⟩ := join_revokes before parent identifier (middle, result) valid joined
  have middleValid := join_wellFormed before parent identifier (middle, result) valid joined
  have resources := history.borrowing middleValid
  exact ⟨worker, live, data.persists middleValid.1 resources, code.persists middleValid.1 resources,
    stack.persists middleValid.1 resources⟩

end EDSL.OS.Threads
