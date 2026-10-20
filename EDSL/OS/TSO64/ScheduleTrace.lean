/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run

set_option autoImplicit false

namespace EDSL.OS.TSO64.ScheduleTrace
open X86

/-- Schedule observations have precisely the original action positions,
including blocked attempts and publications that retire no instruction. -/
theorem length {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    (success : schedule state actions profile = .ok result) : result.2.length = actions.length := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact congrArg Nat.succ (ih following)

/-- An actual observation at a supplied index exposes the real prefix run,
its selected action and the actual step that produced that observation. No
trace is reconstructed from values or from a desired successor state. -/
theorem observation_at {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index : Nat}
    {observation : Observation}
    (success : schedule state actions profile = .ok result)
    (found : result.2[index]? = some observation) :
    ∃ before action next,
      schedule state (actions.take index) profile = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧ step before action profile = .ok (next, observation) := by
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
    {result : State × List Observation} {profile : Profile}
    (success : schedule state actions profile = .ok result) :
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

end EDSL.OS.TSO64.ScheduleTrace
