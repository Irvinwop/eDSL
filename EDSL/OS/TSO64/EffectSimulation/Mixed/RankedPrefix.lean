/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedCohort
import EDSL.OS.TSO64.EffectSimulation.CheckedLifting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Exact collective ghosts across an already executed, possibly interleaved
prefix, followed by a newly constructed ranked completion. Checked lifting
selects each subject's successor through the same actual production step;
the collective trace retains those exact successors and their full histories.
No equality between independently obtained histories is used.

Prefix lifting alone accepts any successful actual schedule. Completion also
requires present initial validity, the actual slot count and quiescence, plus
the prefix's per-thread choices from arbitrary offsets. The ordinary cohort
closure derives quiescence and coverage at the cut. Actual schedule laws
derive validity and worker count there, including when the slot universe is
empty. RankedCohort.complete_from_current constructs the future suffix from
the exact lifted ghosts, with each thread's offset advanced by its own issues
in the entire prefix. No future success, returned value or fairness is assumed.

The result exposes the prefix ghosts and trace, a Suffix containing the actual
returned/quiescent endpoint and its exact final ghosts, and proofs for the
concatenated actual schedule, collective trace and choices. The total action
bound is prefix length plus the potential of the exact ghosts at the cut.
It is an upper bound, with no optimality, hardware cost or all-schedule
termination claim. Imported target, authority, lifetime, synchronization,
translation and protected-loan contracts remain in the local rules and
admissions. This module supplies no corpus admission or native refinement.
-/

namespace EDSL.OS.TSO64.EffectSimulation

universe u

/-- Concatenate through the very same intermediate ghost, retaining all
original action and observation positions and all transition witnesses. -/
theorem LiftTrace.append {G : Type u}
    {Advance : G → Action → Observation → G → Prop}
    {before middle final : G} {left right : List Action}
    {leftSeen rightSeen : List Observation}
    (first : LiftTrace Advance before left leftSeen middle)
    (second : LiftTrace Advance middle right rightSeen final) :
    LiftTrace Advance before (left ++ right) (leftSeen ++ rightSeen) final := by
  induction first with
  | nil => exact second
  | cons head _tail ih => exact .cons head (ih second)

#print axioms LiftTrace.append

namespace Mixed.RankedCohort
open X86

variable {n : Nat} {profile : Profile} {family : RMWFamily}

/-- Lift all subjects through the same checked actual step. Dependent choice
packages precisely the successor and LocalStep supplied by each local lift. -/
theorem checkedSimulation (cohort : RankedCohort n profile family) {initial : S} :
    CheckedSimulation profile (cohort.Current (initial := initial)) cohort.Step family := by
  classical
  constructor
  intro before after action seen ghosts valid current actual
  have successors : ∀ i : Fin n,
      ∃ next : Ghost (cohort.descriptor i) initial (cohort.post i),
        (cohort.rules i).LocalStep (ghosts i) action seen next ∧
        (cohort.rules i).LocalRelated after next := by
    intro i
    have subjectValid : WellFormed before (cohort.descriptor i).profile := by
      simpa only [cohort.profile_eq i] using valid
    have selected : TSO64.step before action (cohort.descriptor i).profile
        (cohort.descriptor i).family = .ok (after, seen) := by
      simpa only [cohort.profile_eq i, cohort.family_eq i] using actual
    exact (cohort.rules i).localSimulation.lift subjectValid (current i) selected
  let next : cohort.Ghosts initial := fun i => Classical.choose (successors i)
  exact ⟨next, fun i => (Classical.choose_spec (successors i)).1,
    fun i => (Classical.choose_spec (successors i)).2⟩

/-- An arbitrary successful actual prefix retains collective local invariants
and one collective trace of the exact chosen ghosts. No queue assumption is
needed for this conditional lifting law. -/
theorem prefix_from_current (cohort : RankedCohort n profile family)
    {initial before cut : S} {ghosts : cohort.Ghosts initial}
    {actions : List Action} {observations : List O}
    (valid : WellFormed before profile) (current : cohort.Current before ghosts)
    (actual : TSO64.schedule before actions profile family = .ok (cut, observations)) :
    ∃ next : cohort.Ghosts initial, cohort.Current cut next ∧
      LiftTrace cohort.Step ghosts actions observations next :=
  cohort.checkedSimulation.schedule valid current actual

/-- The exact endpoint ghosts authenticate their full histories, whose
projections extend each subject's own starting history by the entire trace.
This applies equally to an executed prefix and its constructed completion. -/
theorem trace_histories (cohort : RankedCohort n profile family)
    {initial final : S} {before after : cohort.Ghosts initial}
    {actions : List Action} {observations : List O}
    (current : cohort.Current final after)
    (trace : LiftTrace cohort.Step before actions observations after) (i : Fin n) :
    OriginTrace (cohort.descriptor i).profile initial (after i).history
        final (cohort.descriptor i).family ∧
      (after i).history.map Tick.action = (before i).history.map Tick.action ++ actions ∧
      (after i).history.map (fun tick => tick.result.2) =
        (before i).history.map (fun tick => tick.result.2) ++ observations := by
  have subjectTrace := cohort.localTrace trace i
  have logs := liftTrace_logs ((cohort.rules i).localTrace_forget subjectTrace)
  exact ⟨(current i).1.authentic, logs⟩

/-- Compose two actual runs in the same production profile and RMW family.
This helper consumes the suffix run only after completion constructs it. -/
private theorem prefix_schedule_append {state : S} {leftActions suffix : List Action}
    {middle result : S × List O} {profile : Profile} {family : RMWFamily}
    (firstRun : TSO64.schedule state leftActions profile family = .ok middle)
    (lastRun : TSO64.schedule middle.1 suffix profile family = .ok result) :
    TSO64.schedule state (leftActions ++ suffix) profile family =
      .ok (result.1, middle.2 ++ result.2) := by
  induction leftActions generalizing state middle with
  | nil =>
    have same : (state, []) = middle := Except.ok.inj firstRun
    subst middle
    exact lastRun
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok firstRun
    rw [same] at lastRun ⊢
    have appended := ih following lastRun
    simp only [List.cons_append, TSO64.schedule, stepped, ok_bind, appended, pure_ok]

/-- Complete after an already executed prefix, using the exact collectively
lifted ghosts at its cut. Only the prefix's success is a premise. The returned
Suffix carries its constructed execution, current final ghosts, all-done and
actual returned workers, final validity/count/quiescence, retirement trace,
choices and suffix potential bound. Both concatenated traces share the very
same cut ghosts; per-thread choice offsets count the whole actual prefix. -/
theorem complete_after_prefix (cohort : RankedCohort n profile family)
    {initial before cut : S} {ghosts : cohort.Ghosts initial}
    {prefixActions : List Action} {prefixObservations : List O}
    (valid : WellFormed before profile) (count : before.workers.length = n)
    (current : cohort.Current before ghosts) (empty : Quiescent before)
    (choices : Nat → Nat → Bool) (offset : Nat → Nat)
    (actual : TSO64.schedule before prefixActions profile family =
      .ok (cut, prefixObservations))
    (chosen : ChoiceTrace.ChosenFrom choices offset prefixActions) :
    ∃ atCut : cohort.Ghosts initial,
      cohort.Current cut atCut ∧
      LiftTrace cohort.Step ghosts prefixActions prefixObservations atCut ∧
      Quiescent cut ∧ cohort.toCohort.Covers cut ∧
      ∃ suffix : cohort.Suffix (before := cut) atCut choices
          (fun tid => offset tid + ChoiceTrace.issues tid prefixActions),
        TSO64.schedule before (prefixActions ++ suffix.actions) profile family =
          .ok (suffix.final, prefixObservations ++ suffix.observations) ∧
        LiftTrace cohort.Step ghosts (prefixActions ++ suffix.actions)
          (prefixObservations ++ suffix.observations) suffix.finalGhosts ∧
        ChoiceTrace.ChosenFrom choices offset (prefixActions ++ suffix.actions) ∧
        (prefixActions ++ suffix.actions).length ≤
          prefixActions.length + cohort.potential atCut := by
  obtain ⟨atCut, cutCurrent, prefixLifted⟩ :=
    cohort.prefix_from_current valid current actual
  obtain ⟨cutEmpty, cutCovered, _otherCurrent, _prefixRetiring⟩ :=
    cohort.toCohort.schedule_from_current (cohort.covers count)
      (cohort.current_toCohort current) empty actual
  have cutValid : WellFormed cut profile := schedule_wellFormed valid actual
  have cutCount : cut.workers.length = n :=
    (ScheduleTrace.workers_length actual).trans count
  obtain ⟨suffix⟩ := cohort.complete_from_current cutValid cutCount cutCurrent cutEmpty
    choices (fun tid => offset tid + ChoiceTrace.issues tid prefixActions)
  refine ⟨atCut, cutCurrent, prefixLifted, cutEmpty, cutCovered, suffix,
    prefix_schedule_append actual suffix.actual, prefixLifted.append suffix.lifted,
    ChoiceTrace.chosen_append chosen suffix.chosen, ?_⟩
  simpa only [List.length_append] using
    Nat.add_le_add_left suffix.issue_upper_bound prefixActions.length

#print axioms checkedSimulation
#print axioms prefix_from_current
#print axioms trace_histories
#print axioms prefix_schedule_append
#print axioms complete_after_prefix

end Mixed.RankedCohort

end EDSL.OS.TSO64.EffectSimulation

#audit_edsl
