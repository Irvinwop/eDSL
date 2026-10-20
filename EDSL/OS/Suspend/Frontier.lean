/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Counts
import EDSL.OS.Suspend.Effects

namespace EDSL.OS.Suspend
open X86

/-- No currently pending invocation uses this identity, regardless of worker. -/
def InvocationAbsent (state : State) (invocation : Nat) : Prop :=
  ∀ identifier saved, state.pending identifier = some saved → saved.identifier ≠ invocation

/-- Fresh identity allocation is counted by actual syscall-entry observations,
not parked selections, completions or ordinary machine retirements. -/
theorem step_call_count {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) :
    result.1.nextCall = state.nextCall + enteredCount [result.2] := by
  cases action with
  | issue identifier =>
    cases issue_effect _ _ _ success with
    | parked live running pending => simp [enteredCount]
    | entered live running pending decoded empty executed stepped user continuation =>
      simp [capture, enteredCount]
    | machine pending issued => simp [enteredCount]
  | drain identifier =>
    cases drained : TSO.drain state.machine identifier with
    | error fault => simp [step, drain, drained, Except.mapError] at success
    | ok output =>
      have same : result = ({ state with machine := output.1 }, .machine output.2) := by
        simpa [step, drain, drained, Except.mapError] using success.symm
      rw [same]
      simp [enteredCount]
  | resume identifier invocation raw flags rcx r11 =>
    cases resumed : resume state identifier invocation raw flags rcx r11 with
    | error fault => simp [step, resumed] at success
    | ok after =>
      have same : result = (after, .resumed identifier invocation raw) := by
        simpa [step, resumed] using success.symm
      rw [same]
      simpa only [enteredCount, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.length_nil, Nat.add_zero] using resume_nextCall resumed
  | idle => simp [step] at success; cases success; simp [enteredCount]

theorem Trace.call_count {before after : State} {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) :
    after.nextCall = before.nextCall + enteredCount observations := by
  induction trace with
  | nil => simp [enteredCount]
  | @cons before middle after action observation actions observations first tail ih =>
    have head := step_call_count first
    dsimp only at head
    have count := enteredCount_append [observation] observations
    simp only [List.singleton_append] at count
    omega

theorem schedule_call_count {state : State} {actions : List Action}
    {result : State × List Observation} (success : schedule state actions = .ok result) :
    result.1.nextCall = state.nextCall + enteredCount result.2 :=
  (schedule_trace _ _ _ success).call_count

/-- A consumed old identity cannot be introduced by any future action.
The bound is on the allocation frontier, not a fairness or future-success assumption. -/
theorem step_preserves_absent {state : State} {invocation : Nat}
    (absent : InvocationAbsent state invocation) (older : invocation < state.nextCall)
    {action : Action} {result : State × Observation} (success : step state action = .ok result) :
    InvocationAbsent result.1 invocation := by
  intro query saved pending
  rcases step_pending_origin success pending with prior | fresh
  · exact absent query saved prior
  · rw [fresh.1]
    omega

theorem Trace.preserves_absent {before after : State} {invocation : Nat}
    {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) (absent : InvocationAbsent before invocation)
    (older : invocation < before.nextCall) : InvocationAbsent after invocation := by
  induction trace with
  | nil => exact absent
  | cons first tail ih =>
    have next := step_call_count first
    dsimp only at next
    exact ih (step_preserves_absent absent older first) (by omega)

theorem schedule_preserves_absent {state : State} {invocation : Nat}
    (absent : InvocationAbsent state invocation) (older : invocation < state.nextCall)
    {actions : List Action} {result : State × List Observation}
    (success : schedule state actions = .ok result) : InvocationAbsent result.1 invocation :=
  (schedule_trace _ _ _ success).preserves_absent absent older


end EDSL.OS.Suspend
