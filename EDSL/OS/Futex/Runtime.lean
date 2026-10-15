/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Physical
import EDSL.OS.Futex.Service

namespace EDSL.OS.Futex.Runtime
open X86

inductive Action where
  | issue (worker : Nat)
  | drain (worker : Nat)
  | service (action : Futex.Action)
  deriving DecidableEq, Repr

inductive Observation where
  | physical (observation : Suspend.Observation)
  | serviced (action : Futex.Action)
  deriving DecidableEq, Repr

def step (profile : Physical.Profile) (state : State) : Action → Except Physical.Fault (State × Observation)
  | .issue worker => do
    let result ← Physical.issue profile state worker
    return (result.1, .physical result.2)
  | .drain worker => do
    let result ← Physical.drain profile state worker
    return (result.1, .physical result.2)
  | .service action => do
    let after ← (Futex.step profile.service state action).mapError Physical.Fault.service
    return (after, .serviced action)

def schedule (profile : Physical.Profile) (state : State) : List Action →
    Except Physical.Fault (State × List Observation)
  | [] => .ok (state, [])
  | action :: rest => do
    let head ← step profile state action
    let tail ← schedule profile head.1 rest
    return (tail.1, head.2 :: tail.2)

def retiredCount (observations : List Observation) : Nat :=
  Suspend.retiredCount (observations.filterMap fun observation => match observation with
    | .physical actual => some actual
    | .serviced _ => none)

inductive Trace (profile : Physical.Profile) : State → List Action → List Observation → State → Prop where
  | nil {state} : Trace profile state [] [] state
  | cons {before middle after action observation actions observations}
      (first : step profile before action = .ok (middle, observation))
      (tail : Trace profile middle actions observations after) :
      Trace profile before (action :: actions) (observation :: observations) after

theorem schedule_cons_ok (profile : Physical.Profile) (state : State) (action : Action) (rest : List Action)
    (result : State × List Observation) (success : schedule profile state (action :: rest) = .ok result) :
    ∃ head tail, step profile state action = .ok head ∧ schedule profile head.1 rest = .ok tail ∧
      result = (tail.1, head.2 :: tail.2) := by
  cases first : step profile state action with
  | error fault => simp [schedule, first] at success
  | ok head =>
    cases following : schedule profile head.1 rest with
    | error fault => simp [schedule, first, following] at success
    | ok tail =>
      simp [schedule, first, following] at success
      exact ⟨head, tail, rfl, following, success.symm⟩

theorem schedule_trace (profile : Physical.Profile) (state : State) (actions : List Action)
    (result : State × List Observation) (success : schedule profile state actions = .ok result) :
    Trace profile state actions result.2 result.1 := by
  induction actions generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .nil
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ _ success
    rw [same]
    exact .cons first (ih _ _ following)

theorem Trace.schedule {profile : Physical.Profile} {before after : State}
    {actions : List Action} {observations : List Observation}
    (trace : Trace profile before actions observations after) :
    schedule profile before actions = .ok (after, observations) := by
  induction trace with
  | nil => rfl
  | cons first tail ih => simp [Runtime.schedule, first, ih]

theorem schedule_append (profile : Physical.Profile) (state : State) (first second : List Action)
    (middle result : State × List Observation) (head : schedule profile state first = .ok middle)
    (tail : schedule profile middle.1 second = .ok result) :
    schedule profile state (first ++ second) = .ok (result.1, middle.2 ++ result.2) := by
  induction first generalizing state middle with
  | nil => simp [schedule] at head; cases head; exact tail
  | cons action rest ih =>
    obtain ⟨next, suffix, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ _ head
    rw [same] at tail ⊢
    have following := ih _ _ scheduled tail
    simp [schedule, selected, following]

/-- Infinite behavior is admitted one actual step at a time. No fairness or
service progress condition is hidden in this definition. -/
def Infinite (profile : Physical.Profile) (states : Nat → State) (actions : Nat → Action)
    (observations : Nat → Observation) : Prop :=
  ∀ index, step profile (states index) (actions index) = .ok (states (index + 1), observations index)

end EDSL.OS.Futex.Runtime
