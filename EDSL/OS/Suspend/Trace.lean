/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Model

namespace EDSL.OS.Suspend

theorem schedule_cons_ok (state : State) (action : Action) (rest : List Action)
    (result : State × List Observation) (success : schedule state (action :: rest) = .ok result) :
    ∃ head tail, step state action = .ok head ∧ schedule head.1 rest = .ok tail ∧
      result = (tail.1, head.2 :: tail.2) := by
  cases first : step state action with
  | error fault => simp [schedule, first] at success
  | ok head =>
    cases following : schedule head.1 rest with
    | error fault => simp [schedule, first, following] at success
    | ok tail =>
      simp [schedule, first, following] at success
      exact ⟨head, tail, rfl, following, success.symm⟩

inductive Trace : State → List Action → List Observation → State → Prop where
  | nil {state} : Trace state [] [] state
  | cons {before middle after action observation actions observations}
      (transition : step before action = .ok (middle, observation))
      (tail : Trace middle actions observations after) :
      Trace before (action :: actions) (observation :: observations) after

theorem schedule_trace (state : State) (actions : List Action) (result : State × List Observation)
    (success : schedule state actions = .ok result) : Trace state actions result.2 result.1 := by
  induction actions generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .nil
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .cons first (ih _ _ following)

theorem Trace.schedule {before after : State} {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) : schedule before actions = .ok (after, observations) := by
  induction trace with
  | nil => rfl
  | cons first _ ih => simp [Suspend.schedule, first, ih]

theorem Trace.length {before after : State} {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) : observations.length = actions.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons]; omega

theorem schedule_append (state : State) (first second : List Action)
    (middle result : State × List Observation)
    (scheduledFirst : schedule state first = .ok middle) (suffix : schedule middle.1 second = .ok result) :
    schedule state (first ++ second) = .ok (result.1, middle.2 ++ result.2) := by
  induction first generalizing state middle with
  | nil => simp [schedule] at scheduledFirst; cases scheduledFirst; exact suffix
  | cons action rest ih =>
    obtain ⟨head, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ scheduledFirst
    rw [same] at suffix ⊢
    have following := ih _ _ scheduled suffix
    simp [schedule, selected, following]

theorem Trace.append {before middle after : State} {first second : List Action}
    {observedFirst suffix : List Observation} (left : Trace before first observedFirst middle)
    (right : Trace middle second suffix after) :
    Trace before (first ++ second) (observedFirst ++ suffix) after :=
  schedule_trace _ _ _ (schedule_append _ _ _ _ _ left.schedule right.schedule)

/-- Infinite environment traces record actual selected actions. They carry no
fairness or service-progress promise. -/
structure InfiniteTrace (initialState : State) where
  states : Nat → State
  actions : Nat → Action
  observations : Nat → Observation
  starts : states 0 = initialState
  transitions : ∀ index, step (states index) (actions index) =
    .ok (states (index + 1), observations index)

/-- The service-neutral mechanism explicitly admits indefinite environment
idling. Existence of a completion path is a separate assertion. -/
def idle_forever (state : State) : InfiniteTrace state :=
  ⟨fun _ => state, fun _ => .idle, fun _ => .idle, rfl, fun _ => rfl⟩

end EDSL.OS.Suspend
