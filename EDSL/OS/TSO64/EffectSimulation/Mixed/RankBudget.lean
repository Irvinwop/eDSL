/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPrefix

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Own-issue budgets for arbitrary finite successful schedules of an existing
ranked caller-only cohort.

The trace theorem consumes the supplied collective Step successors unchanged.
Its one-step law is derived from RankLaws, not supplied as another budget
assumption. RetirementTrace classifies every original scheduler position;
actual schedule closure derives it from present coverage, Current and empty
queues. No chosen suffix, fairness or future-success premise is used.

The bound is per exact Fin n slot, with the existing ChoiceTrace.issues counter:
own issues plus the final ghost's measure are at most its starting measure.
At that budget, positivity excludes running control. Related then supplies the
actual returned worker through Done.saved, and Done.no_issue excludes another
successful own issue. These facts do not assert current Post, native cost,
minimum execution length or termination of an arbitrary infinite schedule.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- The existing every-node positivity law excludes running control at zero
measure. No converse from a worker's phase to its ghost control is assumed. -/
theorem RankLaws.done_of_measure_zero {d : Descriptor} {initial state : S}
    {Post : Assertion} {rules : LocalRules d Post} (laws : RankLaws rules)
    {ghost : Ghost d initial Post} (related : rules.LocalRelated state ghost)
    (zero : ghost.measure laws.rank = 0) :
    ∃ response : Response d initial Post, ghost.control = .done response := by
  cases control : ghost.control with
  | running node _fuel =>
    have invariant : rules.Inv node ghost.current ghost.history := by
      simpa only [LocalRules.LocalAt, control] using related.2
    have positive := laws.positive invariant
    have impossible : laws.rank node ghost.current ghost.history = 0 := by
      simpa only [Ghost.measure, control] using zero
    exact False.elim ((Nat.ne_of_gt positive) impossible)
  | done response => exact ⟨response, rfl⟩

/-- Project zero measure to the current physical slot using its retained Done
response and saved worker. RAM and current Post are not projected from it. -/
theorem RankLaws.returned_of_measure_zero {d : Descriptor} {initial state : S}
    {Post : Assertion} {rules : LocalRules d Post} (laws : RankLaws rules)
    {ghost : Ghost d initial Post} (related : rules.LocalRelated state ghost)
    (zero : ghost.measure laws.rank = 0) :
    ∃ worker : Worker, state.workers[d.tid]? = some worker ∧
      worker.phase = .returned := by
  obtain ⟨response, control⟩ := laws.done_of_measure_zero related zero
  have retained : Done d initial Post response ghost.current ghost.history := by
    have atControl := related.1.2
    simpa only [control] using atControl
  obtain ⟨worker, live, saved⟩ := retained.saved
  refine ⟨worker, ?_, saved.phase.trans response.phase⟩
  rw [related.1.1]
  exact live

/-- A zero-measure related subject cannot successfully issue again, for either
AF choice. This uses the actual checked-step exclusion in Done.no_issue. -/
theorem RankLaws.no_issue_of_measure_zero {d : Descriptor} {initial state : S}
    {Post : Assertion} {rules : LocalRules d Post} (laws : RankLaws rules)
    {ghost : Ghost d initial Post} {af : Bool} {result : S × O}
    (related : rules.LocalRelated state ghost) (zero : ghost.measure laws.rank = 0) :
    TSO64.step state (.issue d.tid af) d.profile d.family ≠ .ok result := by
  obtain ⟨response, control⟩ := laws.done_of_measure_zero related zero
  have retained : Done d initial Post response state ghost.history := by
    have atControl := related.1.2
    rw [← related.1.1] at atControl
    simpa only [control] using atControl
  intro actual
  exact retained.no_issue actual

namespace RankedCohort

variable {n : Nat} {profile : Profile} {family : RMWFamily}

/-- Derive one slot's charge from this exact collective Step. Its own retired
issue decreases strictly; a different slot uses measure_advance. tid_eq and
Fin.ext justify that different slots cannot share the queried scheduler tid. -/
theorem step_own_issue_budget (cohort : RankedCohort n profile family)
    {initial : S} {before after : cohort.Ghosts initial}
    {action : Action} {seen : O}
    (advanced : cohort.Step before action seen after)
    (retiring : cohort.toCohort.Retires action seen) (i : Fin n) :
    ChoiceTrace.issues i.val [action] + (after i).measure (cohort.rankLaws i).rank ≤
      (before i).measure (cohort.rankLaws i).rank := by
  obtain ⟨issuer, af, rfl, labels⟩ := retiring
  by_cases same : i = issuer
  · subst issuer
    have unblocked : seen ≠ .blocked (cohort.descriptor i).tid := by
      rcases labels with rfl | rfl | ⟨_event, rfl⟩ <;>
        intro impossible <;> cases impossible
    have strict := (cohort.rankLaws i).measure_own_issue
      (advanced i).1 (advanced i).2.1 unblocked
    have charged : 1 + (after i).measure (cohort.rankLaws i).rank ≤
        (before i).measure (cohort.rankLaws i).rank := by
      simpa only [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_le_of_lt strict
    simpa only [RankedCohort.toCohort, ChoiceTrace.issues_cons_issue, ChoiceTrace.issues_nil,
      cohort.tid_eq i, ite_true, Nat.zero_add] using charged
  · have different : i.val ≠ (cohort.descriptor issuer).tid := by
      intro equal
      exact same (Fin.ext (equal.trans (cohort.tid_eq issuer)))
    have nonincrease := (cohort.rankLaws i).measure_advance
      (advanced i).1 (advanced i).2.1
    simpa only [RankedCohort.toCohort, ChoiceTrace.issues_cons_issue, ChoiceTrace.issues_nil,
      ite_eq_right different, Nat.zero_add] using nonincrease

/-- Fold over every supplied successor of this very trace. Retirement labels
are an explicit premise here; own/peer arithmetic is proved above from the
actual LocalStep and RankLaws APIs. The schedule adapter below derives those
labels, including exclusion of drains and blocked positions. -/
theorem trace_own_issue_budget (cohort : RankedCohort n profile family)
    {initial : S} {before after : cohort.Ghosts initial}
    {actions : List Action} {observations : List O}
    (trace : LiftTrace cohort.Step before actions observations after)
    (retiring : cohort.toCohort.RetirementTrace actions observations) (i : Fin n) :
    ChoiceTrace.issues i.val actions + (after i).measure (cohort.rankLaws i).rank ≤
      (before i).measure (cohort.rankLaws i).rank := by
  revert retiring
  induction trace with
  | @nil start =>
    intro _retiring
    simpa only [ChoiceTrace.issues_nil, Nat.zero_add] using
      Nat.le_refl ((start i).measure (cohort.rankLaws i).rank)
  | @cons first middle last action _seen rest _restSeen head _tail ih =>
    intro retiring
    cases retiring with
    | cons retiredHead retiredTail =>
      have one := cohort.step_own_issue_budget head retiredHead i
      have tailBound := ih retiredTail
      change ChoiceTrace.issues i.val ([action] ++ rest) +
        (last i).measure (cohort.rankLaws i).rank ≤
          (first i).measure (cohort.rankLaws i).rank
      rw [ChoiceTrace.issues_append]
      calc
        _ = ChoiceTrace.issues i.val [action] +
            (ChoiceTrace.issues i.val rest + (last i).measure (cohort.rankLaws i).rank) :=
          Nat.add_assoc _ _ _
        _ ≤ ChoiceTrace.issues i.val [action] +
            (middle i).measure (cohort.rankLaws i).rank :=
          Nat.add_le_add_left tailBound _
        _ ≤ (first i).measure (cohort.rankLaws i).rank := one

/-- Budget for any supplied collective trace of an arbitrary successful actual
schedule. Present Current, the exact worker count and empty queues derive
RetirementTrace on the entire unfiltered action/observation lists. The
existential ghosts inside ordinary Cohort closure are discarded; the bound
uses only the supplied trace's exact successors, measures and histories. -/
theorem own_issue_budget_of_schedule (cohort : RankedCohort n profile family)
    {initial before final : S} {ghosts next : cohort.Ghosts initial}
    {actions : List Action} {observations : List O}
    (count : before.workers.length = n) (current : cohort.Current before ghosts)
    (empty : Quiescent before)
    (actual : TSO64.schedule before actions profile family = .ok (final, observations))
    (trace : LiftTrace cohort.Step ghosts actions observations next) (i : Fin n) :
    ChoiceTrace.issues i.val actions + (next i).measure (cohort.rankLaws i).rank ≤
      (ghosts i).measure (cohort.rankLaws i).rank := by
  obtain ⟨_finalEmpty, _finalCovered, _otherCurrent, retiring⟩ :=
    cohort.toCohort.schedule_from_current (cohort.covers count)
      (cohort.current_toCohort current) empty actual
  exact cohort.trace_own_issue_budget trace retiring i

/-- Lift an arbitrary successful actual prefix exactly once, then derive all
slots' budgets on that returned trace and those same endpoint ghosts. This
adds no enabled successor, future suffix, choice schedule or outcome premise
to the existing current admission. trace_histories applies to these witnesses. -/
theorem prefix_with_own_issue_budget (cohort : RankedCohort n profile family)
    {initial before final : S} {ghosts : cohort.Ghosts initial}
    {actions : List Action} {observations : List O}
    (valid : WellFormed before profile) (count : before.workers.length = n)
    (current : cohort.Current before ghosts) (empty : Quiescent before)
    (actual : TSO64.schedule before actions profile family = .ok (final, observations)) :
    ∃ next : cohort.Ghosts initial,
      cohort.Current final next ∧
      LiftTrace cohort.Step ghosts actions observations next ∧
      ∀ i : Fin n, ChoiceTrace.issues i.val actions +
        (next i).measure (cohort.rankLaws i).rank ≤
          (ghosts i).measure (cohort.rankLaws i).rank := by
  obtain ⟨next, finalCurrent, trace⟩ := cohort.prefix_from_current valid current actual
  exact ⟨next, finalCurrent, trace,
    fun i => cohort.own_issue_budget_of_schedule count current empty actual trace i⟩

/-- If this actual finite prefix spends a subject's entire starting measure,
its same final ghost is done and its actual current slot is returned. Neither
the returned phase nor exhaustion is required for the budget theorem itself.
The second conclusion excludes any further successful own issue, for both AF
choices, through Done.no_issue rather than an assumed phase/control bridge. -/
theorem returned_at_own_issue_budget (cohort : RankedCohort n profile family)
    {initial before final : S} {ghosts next : cohort.Ghosts initial}
    {actions : List Action} {observations : List O}
    (count : before.workers.length = n) (current : cohort.Current before ghosts)
    (empty : Quiescent before)
    (actual : TSO64.schedule before actions profile family = .ok (final, observations))
    (trace : LiftTrace cohort.Step ghosts actions observations next)
    (finalCurrent : cohort.Current final next) (i : Fin n)
    (spent : (ghosts i).measure (cohort.rankLaws i).rank ≤ ChoiceTrace.issues i.val actions) :
    (∃ worker : Worker, final.workers[i.val]? = some worker ∧ worker.phase = .returned) ∧
      (∀ (af : Bool) (result : S × O),
        TSO64.step final (.issue i.val af) profile family ≠ .ok result) := by
  have budget := cohort.own_issue_budget_of_schedule count current empty actual trace i
  have exhausted : ChoiceTrace.issues i.val actions +
      (next i).measure (cohort.rankLaws i).rank ≤ ChoiceTrace.issues i.val actions + 0 := by
    simpa only [Nat.add_zero] using Nat.le_trans budget spent
  have zero : (next i).measure (cohort.rankLaws i).rank = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_left exhausted)
  constructor
  · have returned := (cohort.rankLaws i).returned_of_measure_zero (finalCurrent i) zero
    simpa only [cohort.tid_eq i] using returned
  · intro af result actualIssue
    have selected : TSO64.step final (.issue (cohort.descriptor i).tid af)
        (cohort.descriptor i).profile (cohort.descriptor i).family = .ok result := by
      simpa only [cohort.tid_eq i, cohort.profile_eq i, cohort.family_eq i] using actualIssue
    exact (cohort.rankLaws i).no_issue_of_measure_zero (finalCurrent i) zero selected

#print axioms step_own_issue_budget
#print axioms trace_own_issue_budget
#print axioms own_issue_budget_of_schedule
#print axioms prefix_with_own_issue_budget
#print axioms returned_at_own_issue_budget

end RankedCohort

#print axioms RankLaws.done_of_measure_zero
#print axioms RankLaws.returned_of_measure_zero
#print axioms RankLaws.no_issue_of_measure_zero

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
