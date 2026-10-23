/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.ScheduleTrace
open X86

/-- Schedule observations have precisely the original action positions,
including blocked attempts and publications that retire no instruction. -/
theorem length {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (success : schedule state actions profile family = .ok result) : result.2.length = actions.length := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact congrArg Nat.succ (ih following)

/-- Every cut of an actual successful run has the actual prefix state and a
successful remaining suffix. Both lists retain all scheduler actions and
observations, including drains and blocked attempts. Indices past the end use
the final state and empty suffix; no new action position is manufactured. -/
theorem cut {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (success : schedule state actions profile family = .ok result) (index : Nat) :
    ∃ before,
      schedule state (actions.take index) profile family = .ok (before, result.2.take index) ∧
      schedule before (actions.drop index) profile family = .ok (result.1, result.2.drop index) := by
  induction actions generalizing state result index with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    refine ⟨state, ?_, ?_⟩ <;> simp only [List.take_nil, List.drop_nil, schedule]
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    cases index with
    | zero =>
      refine ⟨state, rfl, ?_⟩
      simpa only [List.drop_zero] using success
    | succ index =>
      obtain ⟨before, prefixRun, suffixRun⟩ := ih following index
      refine ⟨before, ?_, ?_⟩
      · simp only [same, List.take_succ_cons, schedule, stepped, ok_bind, prefixRun, pure_ok]
      · simpa only [same, List.drop_succ_cons] using suffixRun

/-- An independently supplied successful prefix is the prefix of the same
full run. Determinism recovers both its observations and the real suffix,
without accepting a caller's intended intermediate or final state as fact. -/
theorem suffix {state before : State} {actions : List Action}
    {result : State × List Observation} {observations : List Observation}
    {profile : Profile} {family : RMWFamily} {index : Nat}
    (success : schedule state actions profile family = .ok result)
    (prefixRun : schedule state (actions.take index) profile family = .ok (before, observations)) :
    observations = result.2.take index ∧
      schedule before (actions.drop index) profile family = .ok (result.1, result.2.drop index) := by
  obtain ⟨middle, actualPrefix, actualSuffix⟩ := cut success index
  have same : (before, observations) = (middle, result.2.take index) :=
    Except.ok.inj (prefixRun.symm.trans actualPrefix)
  have stateEq := congrArg Prod.fst same
  have observationsEq := congrArg Prod.snd same
  refine ⟨observationsEq, ?_⟩
  change before = middle at stateEq
  rw [stateEq]
  exact actualSuffix

/-- An actual observation at a supplied index exposes the real prefix run,
its selected action and the actual step that produced that observation. No
trace is reconstructed from values or from a desired successor state. -/
theorem observation_at {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily} {index : Nat}
    {observation : Observation}
    (success : schedule state actions profile family = .ok result)
    (found : result.2[index]? = some observation) :
    ∃ before action next,
      schedule state (actions.take index) profile family = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧ step before action profile family = .ok (next, observation) := by
  induction actions generalizing state result index with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    simp at found
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    cases index with
    | zero =>
      have selected : first.2 = observation := by
        simpa only [same, List.getElem?_cons_zero, Option.some.injEq] using found
      subst observation
      exact ⟨state, action, first.1, rfl, rfl, stepped⟩
    | succ index =>
      have selected : tail.2[index]? = some observation := by
        simpa only [same, List.getElem?_cons_succ] using found
      obtain ⟨before, selectedAction, next, prefixRun, actionAt, executed⟩ := ih following selected
      refine ⟨before, selectedAction, next, ?_, ?_, executed⟩
      · simp only [same, List.take_succ_cons, schedule, stepped, ok_bind,
          prefixRun, pure_ok]
      · simpa only [List.getElem?_cons_succ] using actionAt

/-- Persistent managed-cell descriptors are unchanged along an actual run.
This is metadata stability; it does not assert memory contents are unchanged. -/
theorem cells {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (success : schedule state actions profile family = .ok result) :
    result.1.world.cells = state.world.cells := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact (ih following).trans (step_stable stepped).cells

private theorem step_workers_length {state : State} {action : Action}
    {result : State × Observation} {profile : Profile} {family : RMWFamily}
    (success : step state action profile family = .ok result) :
    result.1.workers.length = state.workers.length := by
  cases step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> simp only [install, List.length_set]
  | blocked => rfl
  | rmw => simp only [install, List.length_set]
  | drained => simp only [install, List.length_set]

/-- Successful steps retain the fixed worker universe. This covers every
scheduler profile and every intermediate prefix, including drains and RETs. -/
theorem workers_length {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (success : schedule state actions profile family = .ok result) :
    result.1.workers.length = state.workers.length := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨first, tail, actual, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact (ih following).trans (step_workers_length actual)

end EDSL.OS.TSO64.ScheduleTrace
