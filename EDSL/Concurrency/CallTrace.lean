/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.Linearizability

namespace EDSL.Concurrency.CallTrace

/-- An annotation adapter for an actual transition system. The client proves
what its emitted list means from the very transition used by replay. `Origin`
is a client relation, not an assumed invariant or a generic semantic guarantee.
No callback accepts a desired successor or future successful execution. -/
structure Adapter (State Action Observation Fault Mark Id Thread Input Output : Type) where
  step : State → Action → Except Fault (State × Observation)
  Origin : State → Action → State × Observation → Mark →
    List (Linearizability.Event Id Thread Input Output) → Prop
  emit : State → Action → State × Observation → Mark →
    Option (List (Linearizability.Event Id Thread Input Output))
  emit_sound : ∀ {before action result mark events},
    step before action = .ok result → emit before action result mark = some events →
    Origin before action result mark events

/-- Invocation annotations mark environmental prefix boundaries. Their labels
alone establish neither program entry nor an ABI argument or resource origin. -/
inductive Entry (Action Mark Id Thread Input : Type) where
  | invoke (id : Id) (thread : Thread) (input : Input)
  | execute (action : Action) (mark : Mark)
  deriving DecidableEq, Repr

structure Result (State Observation Id Thread Input Output : Type) where
  state : State
  observations : List Observation
  events : List (Linearizability.Event Id Thread Input Output)

variable {State Action Observation Fault Mark Id Thread Input Output : Type}

abbrev Event := Linearizability.Event Id Thread Input Output

/-- Erase annotations, retaining every actual selected action in order. -/
def actions (entries : List (Entry Action Mark Id Thread Input)) : List Action :=
  entries.filterMap fun entry => match entry with
    | .invoke .. => none
    | .execute action _ => some action

variable (adapter : Adapter State Action Observation Fault Mark Id Thread Input Output)

/-- Run the client's actual step once per execute entry, then annotate that
exact result. Emission may be empty or contain several ordered events. Any
transition error or rejected annotation fails closed. -/
def replay (state : State) : List (Entry Action Mark Id Thread Input) →
    Option (Result State Observation Id Thread Input Output)
  | [] => some ⟨state, [], []⟩
  | .invoke id thread input :: rest =>
    (replay state rest).map fun tail =>
      ⟨tail.state, tail.observations, .invoke id thread input :: tail.events⟩
  | .execute action mark :: rest =>
    match adapter.step state action with
    | .error _ => none
    | .ok head =>
      match adapter.emit state action head mark with
      | none => none
      | some events => (replay head.1 rest).map fun tail =>
          ⟨tail.state, head.2 :: tail.observations, events ++ tail.events⟩

/-- A semantic annotation run. Every execute constructor retains the actual
transition and the client's justified origin relation for its whole event list.
Invocations remain environmental annotations. -/
inductive Run : State → List (Entry Action Mark Id Thread Input) → List Observation →
    State → List (@Event Id Thread Input Output) → Prop where
  | nil {state} : Run state [] [] state []
  | invoke {state rest observations after events} (id : Id) (thread : Thread) (input : Input)
      (tail : Run state rest observations after events) :
      Run state (.invoke id thread input :: rest) observations after (.invoke id thread input :: events)
  | execute {before middle after action mark rest observations observation head events}
      (step : adapter.step before action = .ok (middle, observation))
      (origin : adapter.Origin before action (middle, observation) mark head)
      (tail : Run middle rest observations after events) :
      Run before (.execute action mark :: rest) (observation :: observations) after (head ++ events)

theorem replay_sound {before : State} {entries : List (Entry Action Mark Id Thread Input)}
    {result : Result State Observation Id Thread Input Output}
    (accepted : replay adapter before entries = some result) :
    Run adapter before entries result.observations result.state result.events := by
  induction entries generalizing before result with
  | nil =>
    simp only [replay, Option.some.injEq] at accepted
    subst result
    exact .nil
  | cons entry rest ih =>
    cases entry with
    | invoke id thread input =>
      cases tailEq : replay adapter before rest with
      | none => simp [replay, tailEq] at accepted
      | some tail =>
        simp only [replay, tailEq, Option.map_some, Option.some.injEq] at accepted
        subst result
        exact .invoke id thread input (ih tailEq)
    | execute action mark =>
      cases first : adapter.step before action with
      | error fault => simp [replay, first] at accepted
      | ok head =>
        cases emitted : adapter.emit before action head mark with
        | none => simp [replay, first, emitted] at accepted
        | some events =>
          cases tailEq : replay adapter head.1 rest with
          | none => simp [replay, first, emitted, tailEq] at accepted
          | some tail =>
            simp only [replay, first, emitted, tailEq, Option.map_some, Option.some.injEq] at accepted
            subst result
            exact .execute first (adapter.emit_sound first emitted) (ih tailEq)

/-- Ordinary transition-system trace, with no annotation or instruction model. -/
inductive Trace : State → List Action → List Observation → State → Prop where
  | nil {state} : Trace state [] [] state
  | cons {before middle after action actions observation observations}
      (step : adapter.step before action = .ok (middle, observation))
      (tail : Trace middle actions observations after) :
      Trace before (action :: actions) (observation :: observations) after

/-- The same actual transition callback folded over an unannotated schedule. -/
def schedule (state : State) : List Action → Except Fault (State × List Observation)
  | [] => .ok (state, [])
  | action :: rest => do
    let head ← adapter.step state action
    let tail ← schedule head.1 rest
    return (tail.1, head.2 :: tail.2)

theorem Trace.schedule {before after : State} {selected : List Action} {observations : List Observation}
    (trace : Trace adapter before selected observations after) :
    schedule adapter before selected = .ok (after, observations) := by
  induction trace with
  | nil => rfl
  | @cons before middle after action actions observation observations step _ ih =>
    rw [CallTrace.schedule, step]
    change Except.bind (CallTrace.schedule adapter middle actions)
      (fun tail => .ok (tail.1, observation :: tail.2)) = .ok (after, observation :: observations)
    rw [ih]
    rfl

theorem Run.trace {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter before entries observations after events) :
    Trace adapter before (actions entries) observations after := by
  induction run with
  | nil => exact .nil
  | invoke id thread input _ ih => simpa [actions] using ih
  | execute step _ _ ih => simpa [actions] using Trace.cons step ih

theorem Run.schedule {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter before entries observations after events) :
    schedule adapter before (actions entries) = .ok (after, observations) :=
  run.trace.schedule

/-- An event boundary is an environmental invocation or a selected event at
its exact offset within one client's justified emitted list. Multiple events
from one transition share that transition, retaining their internal order. -/
inductive EventBoundary (state : State) : Entry Action Mark Id Thread Input → Nat →
    @Event Id Thread Input Output → Prop where
  | invoke (id : Id) (thread : Thread) (input : Input) :
      EventBoundary state (.invoke id thread input) 0 (.invoke id thread input)
  | execute {action mark result emitted offset event}
      (step : adapter.step state action = .ok result)
      (origin : adapter.Origin state action result mark emitted)
      (selected : emitted[offset]? = some event) :
      EventBoundary state (.execute action mark) offset event

/-- An exact event index has a concrete entry and an actual earlier Run of
this very entry list. The index includes the offset inside the selected entry's
emitted list; it is not merely an existential occurrence of an equal event. -/
def EventAt (before : State) (entries : List (Entry Action Mark Id Thread Input))
    (index : Nat) (event : @Event Id Thread Input Output) : Prop :=
  ∃ earlier later state observations priorEvents selected offset,
    entries = earlier ++ selected :: later ∧
    Run adapter before earlier observations state priorEvents ∧
    priorEvents.length + offset = index ∧ EventBoundary adapter state selected offset event

private theorem eventAt_head {before : State} {entry : Entry Action Mark Id Thread Input}
    {offset : Nat} {event : @Event Id Thread Input Output}
    {rest : List (Entry Action Mark Id Thread Input)}
    (boundary : EventBoundary adapter before entry offset event) :
    EventAt adapter before (entry :: rest) offset event :=
  ⟨[], rest, before, [], [], entry, offset, rfl, .nil, Nat.zero_add offset, boundary⟩

private theorem eventAt_invoke {before : State} {rest : List (Entry Action Mark Id Thread Input)}
    {index : Nat} {event : @Event Id Thread Input Output}
    (id : Id) (thread : Thread) (input : Input)
    (laterEvent : EventAt adapter before rest index event) :
    EventAt adapter before (.invoke id thread input :: rest) (index + 1) event := by
  obtain ⟨earlier, later, state, observations, priorEvents, selected, offset,
    same, run, length, boundary⟩ := laterEvent
  refine ⟨.invoke id thread input :: earlier, later, state, observations,
    .invoke id thread input :: priorEvents, selected, offset, ?_, .invoke id thread input run, ?_, boundary⟩
  · simp [same]
  · simp only [List.length_cons]
    omega

private theorem eventAt_execute {before middle : State}
    {action : Action} {observation : Observation} {mark : Mark}
    {head : List (@Event Id Thread Input Output)} {rest : List (Entry Action Mark Id Thread Input)}
    {index : Nat} {event : @Event Id Thread Input Output}
    (step : adapter.step before action = .ok (middle, observation))
    (origin : adapter.Origin before action (middle, observation) mark head)
    (laterEvent : EventAt adapter middle rest index event) :
    EventAt adapter before (.execute action mark :: rest) (head.length + index) event := by
  obtain ⟨earlier, later, state, observations, priorEvents, selected, offset,
    same, run, length, boundary⟩ := laterEvent
  refine ⟨.execute action mark :: earlier, later, state, observation :: observations,
    head ++ priorEvents, selected, offset, ?_, .execute step origin run, ?_, boundary⟩
  · simp [same]
  · simp only [List.length_append]
    omega

/-- Indexed origin correspondence for arbitrary empty or multi-event
emissions, with all earlier entries replayed through the same actual system. -/
theorem Run.event_at {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter before entries observations after events) {index : Nat}
    {event : @Event Id Thread Input Output} (found : events[index]? = some event) :
    EventAt adapter before entries index event := by
  induction run generalizing index with
  | nil => simp at found
  | invoke id thread input _ ih =>
    cases index with
    | zero =>
      have same := Option.some.inj found
      subst event
      exact eventAt_head adapter (.invoke id thread input)
    | succ index => exact eventAt_invoke adapter id thread input (ih (by simpa using found))
  | @execute before middle after action mark rest observations observation head events step origin tail ih =>
    by_cases inHead : index < head.length
    · have selected : head[index]? = some event := by
        simpa only [List.getElem?_append_left inHead] using found
      exact eventAt_head adapter (.execute step origin selected)
    · have inTail : head.length ≤ index := Nat.le_of_not_gt inHead
      have selected : events[index - head.length]? = some event := by
        simpa only [List.getElem?_append_right inTail] using found
      simpa only [Nat.add_sub_of_le inTail] using eventAt_execute adapter step origin (ih selected)

/-- The existing protocol supplies interval containment and label matching;
this theorem binds all three positions to the very same actual annotated run.
It asserts only the client's Origin at execute boundaries. -/
theorem Run.interval_boundaries [DecidableEq Id]
    {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter before entries observations after events) (valid : Linearizability.Protocol events)
    {interval : Linearizability.Interval Id Thread Input Output}
    (member : interval ∈ Linearizability.intervals events) :
    EventAt adapter before entries interval.invocation
      (.invoke interval.call.id interval.call.thread interval.call.input) ∧
    EventAt adapter before entries interval.point (.point interval.call) ∧
    EventAt adapter before entries interval.response
      (.respond interval.call.id interval.call.thread interval.call.output) := by
  have labels := valid.2.2.1 interval member
  exact ⟨Run.event_at adapter run labels.2.2.1, Run.event_at adapter run labels.2.2.2.1,
    Run.event_at adapter run labels.2.2.2.2⟩

/-- Complete logical-label admission after actual replay. Object arithmetic,
function entry, RET/resource origins and liveness are separate client theorems.
In particular, missing responses are rejected instead of manufactured. -/
def checkComplete [DecidableEq Id] [DecidableEq Thread] [DecidableEq Input] [DecidableEq Output]
    (before : State) (entries : List (Entry Action Mark Id Thread Input)) : Bool :=
  match replay adapter before entries with
  | none => false
  | some result => Linearizability.check result.events

theorem checkComplete_sound [DecidableEq Id] [DecidableEq Thread] [DecidableEq Input] [DecidableEq Output]
    {before : State} {entries : List (Entry Action Mark Id Thread Input)}
    (checked : checkComplete adapter before entries = true) :
    ∃ result, replay adapter before entries = some result ∧
      Run adapter before entries result.observations result.state result.events ∧
      schedule adapter before (actions entries) = .ok (result.state, result.observations) ∧
      Linearizability.Protocol result.events := by
  cases accepted : replay adapter before entries with
  | none => simp [checkComplete, accepted] at checked
  | some result =>
    have run := replay_sound adapter accepted
    exact ⟨result, rfl, run, run.schedule,
      Linearizability.check_sound (by simpa [checkComplete, accepted] using checked)⟩

end EDSL.Concurrency.CallTrace

#audit_edsl
