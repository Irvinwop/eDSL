/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Lifting

/-!
Ghost simulation from actual successful production TSO64 steps. The local law
receives just the present checked step, so clients can retain evidence such as
the selected atomic handle that a native `Origin` deliberately forgets. It has
no future-schedule premise and supplies no instruction evaluator or converse
from arbitrary origins to checked steps.

The schedule and cut laws reuse `LiftTrace` and `ScheduleTrace`, retaining every
action and observation, including blocked attempts and drains. Their successful
run premises do not establish enabledness, fault freedom, fairness or termination.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.EffectSimulation

universe u

/-- A ghost transition for one actual successful step at the current state.
The checked-step premise exposes actual selection and execution evidence; it
does not assume any later schedule succeeds. -/
structure CheckedSimulation {G : Type u} (profile : Profile)
    (Rel : State → G → Prop)
    (Advance : G → Action → Observation → G → Prop)
    (family : RMWFamily := .xaddOnly) : Prop where
  lift : ∀ {before after : State} {action : Action} {observation : Observation} {g : G},
    WellFormed before profile → Rel before g →
    step before action profile family = .ok (after, observation) →
    ∃ next, Advance g action observation next ∧ Rel after next

/-- An origin-indexed simulation also lifts actual checked steps, using only
the native forward implication from step success to its origin. -/
theorem Simulation.toChecked {G : Type u} {profile : Profile} {family : RMWFamily}
    {Rel : State → G → Prop}
    {Advance : G → Action → Observation → G → Prop}
    (laws : Simulation profile Rel Advance family) :
    CheckedSimulation profile Rel Advance family := by
  refine ⟨?_⟩
  intro before after action observation g valid related actual
  exact laws.lift valid related (step_origin (family := family) actual)

/-- Fold the local checked-step law over an actual successful schedule.
Only the initial state needs supplied validity and relatedness; subsequent
validity follows from each actual production step. -/
theorem CheckedSimulation.schedule {G : Type u} {profile : Profile} {family : RMWFamily}
    {Rel : State → G → Prop}
    {Advance : G → Action → Observation → G → Prop}
    (laws : CheckedSimulation profile Rel Advance family)
    {initial final : State} {actions : List Action}
    {observations : List Observation} {g : G}
    (valid : WellFormed initial profile) (related : Rel initial g)
    (actual : TSO64.schedule initial actions profile family = .ok (final, observations)) :
    ∃ next, Rel final next ∧ LiftTrace Advance g actions observations next := by
  induction actions generalizing initial final observations g with
  | nil =>
    have same : (initial, []) = (final, observations) := Except.ok.inj actual
    have finalEq : initial = final := congrArg Prod.fst same
    have observationsEq : [] = observations := congrArg Prod.snd same
    subst final
    subst observations
    exact ⟨g, related, .nil⟩
  | cons action rest ih =>
    obtain ⟨⟨after, observation⟩, ⟨last, seen⟩, stepped, scheduled, same⟩ :=
      schedule_cons_ok (family := family) actual
    obtain ⟨middle, advanced, middleRelated⟩ := laws.lift valid related stepped
    obtain ⟨next, finalRelated, lifted⟩ :=
      ih (initial := after) (final := last) (observations := seen) (g := middle)
        (step_wellFormed (family := family) valid stepped) middleRelated scheduled
    have finalEq : final = last := congrArg Prod.fst same
    have observationsEq : observations = observation :: seen := congrArg Prod.snd same
    rw [finalEq, observationsEq]
    exact ⟨next, finalRelated, .cons advanced lifted⟩

/-- Every cut of an actual successful schedule has a related ghost state and
the complete lifted prefix, together with the same family's successful suffix.
Indices count all scheduler positions; past-end cuts use the final state and
empty suffix, as in `ScheduleTrace.cut`. -/
theorem CheckedSimulation.schedule_cut {G : Type u} {profile : Profile} {family : RMWFamily}
    {Rel : State → G → Prop}
    {Advance : G → Action → Observation → G → Prop}
    (laws : CheckedSimulation profile Rel Advance family)
    {initial final : State} {actions : List Action}
    {observations : List Observation} {g : G}
    (valid : WellFormed initial profile) (related : Rel initial g)
    (actual : TSO64.schedule initial actions profile family = .ok (final, observations))
    (index : Nat) :
    ∃ before next,
      TSO64.schedule initial (actions.take index) profile family =
        .ok (before, observations.take index) ∧
      TSO64.schedule before (actions.drop index) profile family =
        .ok (final, observations.drop index) ∧
      Rel before next ∧
      LiftTrace Advance g (actions.take index) (observations.take index) next := by
  obtain ⟨before, prefixRun, suffixRun⟩ := ScheduleTrace.cut (family := family) actual index
  obtain ⟨next, cutRelated, lifted⟩ := laws.schedule (family := family) valid related prefixRun
  exact ⟨before, next, prefixRun, suffixRun, cutRelated, lifted⟩

end EDSL.OS.TSO64.EffectSimulation

#print axioms EDSL.OS.TSO64.EffectSimulation.CheckedSimulation
#print axioms EDSL.OS.TSO64.EffectSimulation.Simulation.toChecked
#print axioms EDSL.OS.TSO64.EffectSimulation.CheckedSimulation.schedule
#print axioms EDSL.OS.TSO64.EffectSimulation.CheckedSimulation.schedule_cut
#audit_edsl
