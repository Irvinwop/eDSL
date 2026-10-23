/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.OS.TSO64.ScheduleTrace
import EDSL.Audit

/-!
Generic ghost simulation of successful production TSO64 schedules. The client
supplies a law for every native `Origin`, at the actual current scheduler state.
The fold retains every action and observation, including blocks and drains.
It proves no scheduler fault freedom, termination, fairness or concurrency
contract independently of those client laws and the successful-run premise.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.EffectSimulation

universe u

/-- One ghost transition per actual scheduler position, even if the observed
action retires no instruction. Labels are the original, unfiltered lists. -/
inductive LiftTrace {G : Type u}
    (Advance : G → Action → Observation → G → Prop) :
    G → List Action → List Observation → G → Prop where
  | nil {g : G} : LiftTrace Advance g [] [] g
  | cons {g middle final : G} {action : Action} {observation : Observation}
      {actions : List Action} {observations : List Observation}
      (head : Advance g action observation middle)
      (tail : LiftTrace Advance middle actions observations final) :
      LiftTrace Advance g (action :: actions) (observation :: observations) final

/-- Explicit protocol obligations over the real evolving scheduler state.
Native origins retain ordinary, blocked, full64 RMW and publication evidence;
this record supplies no instruction interpreter or fixed-program phase model. -/
structure Simulation {G : Type u} (profile : Profile)
    (Rel : State → G → Prop)
    (Advance : G → Action → Observation → G → Prop)
    (family : RMWFamily := .xaddOnly) : Prop where
  lift : ∀ {before after : State} {action : Action} {observation : Observation} {g : G},
    WellFormed before profile → Rel before g →
    Origin before action (after, observation) profile family →
    ∃ next, Advance g action observation next ∧ Rel after next

/-- Fold the client's origin law along an actual successful schedule. Only
initial validity and relatedness are assumed; each successor invariant follows
from the production step, with its actual world and unfiltered observation. -/
theorem Simulation.schedule {G : Type u} {profile : Profile} {family : RMWFamily}
    {Rel : State → G → Prop}
    {Advance : G → Action → Observation → G → Prop}
    (laws : Simulation profile Rel Advance family)
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
    obtain ⟨middle, advanced, middleRelated⟩ :=
      laws.lift valid related (step_origin (family := family) stepped)
    obtain ⟨next, finalRelated, lifted⟩ :=
      ih (initial := after) (final := last) (observations := seen) (g := middle)
        (step_wellFormed (family := family) valid stepped) middleRelated scheduled
    have finalEq : final = last := congrArg Prod.fst same
    have observationsEq : observations = observation :: seen := congrArg Prod.snd same
    rw [finalEq, observationsEq]
    exact ⟨next, finalRelated, .cons advanced lifted⟩

/-- Every actual cut has a related ghost state and the lifted real prefix.
The suffix is the same successful run from that cut's actual world. Indices
count all actions; past-end indices inherit `ScheduleTrace.cut`'s final state
and empty suffix. No relatedness premise is required at intermediate cuts. -/
theorem Simulation.schedule_cut {G : Type u} {profile : Profile} {family : RMWFamily}
    {Rel : State → G → Prop}
    {Advance : G → Action → Observation → G → Prop}
    (laws : Simulation profile Rel Advance family)
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

#print axioms EDSL.OS.TSO64.EffectSimulation.Simulation
#print axioms EDSL.OS.TSO64.EffectSimulation.Simulation.schedule
#print axioms EDSL.OS.TSO64.EffectSimulation.Simulation.schedule_cut
#audit_edsl
