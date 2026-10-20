/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.CallTrace

namespace EDSL.Concurrency.CallTrace.Invocations

variable {State Action Observation Fault Mark Id Thread Input Output : Type}

/-- A client check of the present state and invocation labels only. Any ABI,
resource or entry interpretation requires a separate client soundness proof. -/
abbrev Gate (State Id Thread Input : Type) := State → Id → Thread → Input → Bool

variable (adapter : Adapter State Action Observation Fault Mark Id Thread Input Output)
  (currentState : Gate State Id Thread Input)

/-- Execute emitters may also emit invokes: those cannot bypass admission.
Every event in one emission shares the execute entry's current pre-state;
list offsets do not manufacture intermediate machine states. -/
def admitEvent (state : State) : @Event Id Thread Input Output → Bool
  | .invoke id thread input => currentState state id thread input
  | .point _ | .respond .. => true

def admitEvents (state : State) (events : List (@Event Id Thread Input Output)) : Bool :=
  events.all (admitEvent currentState state)

/-- One replay of the actual adapter. A failed invoke returns immediately,
before replaying its suffix. Each execute calls step once and, on success,
emit once on that very result. No desired result enters the gate. -/
def replay (state : State) : List (Entry Action Mark Id Thread Input) →
    Option (Result State Observation Id Thread Input Output)
  | [] => some ⟨state, [], []⟩
  | .invoke id thread input :: rest =>
    if currentState state id thread input then
      (replay state rest).map fun tail =>
        ⟨tail.state, tail.observations, .invoke id thread input :: tail.events⟩
    else none
  | .execute action mark :: rest =>
    match adapter.step state action with
    | .error _ => none
    | .ok head =>
      match adapter.emit state action head mark with
      | none => none
      | some events =>
        if admitEvents currentState state events then
          (replay head.1 rest).map fun tail =>
            ⟨tail.state, head.2 :: tail.observations, events ++ tail.events⟩
        else none

theorem replay_reject_invoke {state : State} {id : Id} {thread : Thread} {input : Input}
    {rest : List (Entry Action Mark Id Thread Input)}
    (rejected : currentState state id thread input = false) :
    replay adapter currentState state (.invoke id thread input :: rest) = none := by
  simp [replay, rejected]

/-- One entry's actual transition and whole emission, with both executable
emission equality and justified Origin, enriched with present admission.
The explicit equality fixes the emitted length without inverting Origin. -/
inductive Boundary (state : State) : Entry Action Mark Id Thread Input → State →
    List Observation → List (@Event Id Thread Input Output) → Prop where
  | invoke (id : Id) (thread : Thread) (input : Input)
      (admitted : currentState state id thread input = true) :
      Boundary state (.invoke id thread input) state [] [.invoke id thread input]
  | execute {action mark middle observation events}
      (step : adapter.step state action = .ok (middle, observation))
      (emitted : adapter.emit state action (middle, observation) mark = some events)
      (origin : adapter.Origin state action (middle, observation) mark events)
      (admitted : admitEvents currentState state events = true) :
      Boundary state (.execute action mark) middle [observation] events

inductive Run : State → List (Entry Action Mark Id Thread Input) → List Observation →
    State → List (@Event Id Thread Input Output) → Prop where
  | nil {state} : Run state [] [] state []
  | cons {before middle after entry rest headObservations observations head events}
      (boundary : Boundary adapter currentState before entry middle headObservations head)
      (tail : Run middle rest observations after events) :
      Run before (entry :: rest) (headObservations ++ observations) after (head ++ events)

theorem replay_sound {before : State} {entries : List (Entry Action Mark Id Thread Input)}
    {result : Result State Observation Id Thread Input Output}
    (accepted : replay adapter currentState before entries = some result) :
    Run adapter currentState before entries result.observations result.state result.events := by
  induction entries generalizing before result with
  | nil =>
    simp only [replay, Option.some.injEq] at accepted
    subst result
    exact .nil
  | cons entry rest ih =>
    cases entry with
    | invoke id thread input =>
      by_cases admitted : currentState before id thread input = true
      · cases tailEq : replay adapter currentState before rest with
        | none => simp [replay, admitted, tailEq] at accepted
        | some tail =>
          simp only [replay, admitted, ↓reduceIte, tailEq, Option.map_some,
            Option.some.injEq] at accepted
          subst result
          exact .cons (.invoke id thread input admitted) (ih tailEq)
      · simp [replay, admitted] at accepted
    | execute action mark =>
      cases first : adapter.step before action with
      | error fault => simp [replay, first] at accepted
      | ok head =>
        cases emitted : adapter.emit before action head mark with
        | none => simp [replay, first, emitted] at accepted
        | some events =>
          by_cases admitted : admitEvents currentState before events = true
          · cases tailEq : replay adapter currentState head.1 rest with
            | none => simp [replay, first, emitted, admitted, tailEq] at accepted
            | some tail =>
              simp only [replay, first, emitted, admitted, ↓reduceIte, tailEq,
                Option.map_some, Option.some.injEq] at accepted
              subst result
              exact .cons (.execute first emitted (adapter.emit_sound first emitted) admitted) (ih tailEq)
          · simp [replay, first, emitted, admitted] at accepted

theorem Run.erase {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter currentState before entries observations after events) :
    CallTrace.Run adapter before entries observations after events := by
  induction run with
  | nil => exact .nil
  | cons boundary _ ih =>
    cases boundary with
    | invoke id thread input _ => exact .invoke id thread input ih
    | execute step _ origin _ => exact .execute step origin ih

theorem Run.schedule {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter currentState before entries observations after events) :
    CallTrace.schedule adapter before (actions entries) = .ok (after, observations) :=
  (run.erase).schedule

/-- Executable acceptance preserves the entire original result. This is proved
from replay, rather than treating the client's Origin as an inverse of emit. -/
theorem replay_original {before : State} {entries : List (Entry Action Mark Id Thread Input)}
    {result : Result State Observation Id Thread Input Output}
    (accepted : replay adapter currentState before entries = some result) :
    CallTrace.replay adapter before entries = some result := by
  induction entries generalizing before result with
  | nil => exact accepted
  | cons entry rest ih =>
    cases entry with
    | invoke id thread input =>
      by_cases admitted : currentState before id thread input = true
      · cases tailEq : replay adapter currentState before rest with
        | none => simp [replay, admitted, tailEq] at accepted
        | some tail =>
          simp only [replay, admitted, ↓reduceIte, tailEq, Option.map_some,
            Option.some.injEq] at accepted
          subst result
          simp only [CallTrace.replay, ih tailEq, Option.map_some]
      · simp [replay, admitted] at accepted
    | execute action mark =>
      cases first : adapter.step before action with
      | error fault => simp [replay, first] at accepted
      | ok head =>
        cases emitted : adapter.emit before action head mark with
        | none => simp [replay, first, emitted] at accepted
        | some events =>
          by_cases admitted : admitEvents currentState before events = true
          · cases tailEq : replay adapter currentState head.1 rest with
            | none => simp [replay, first, emitted, admitted, tailEq] at accepted
            | some tail =>
              simp only [replay, first, emitted, admitted, ↓reduceIte, tailEq,
                Option.map_some, Option.some.injEq] at accepted
              subst result
              simp only [CallTrace.replay, first, emitted, ih tailEq, Option.map_some]
          · simp [replay, first, emitted, admitted] at accepted

/-- This enriched Run retains actual emitter equality, so its earlier prefixes
are executable as well. No converse from the original Origin-only Run is used. -/
theorem Run.replay {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter currentState before entries observations after events) :
    Invocations.replay adapter currentState before entries = some ⟨after, observations, events⟩ := by
  induction run with
  | nil => rfl
  | cons boundary _ ih =>
    cases boundary with
    | invoke id thread input admitted =>
      simp only [Invocations.replay, admitted, ↓reduceIte, ih, Option.map_some,
        List.cons_append, List.nil_append]
    | execute step emitted _ admitted =>
      simp only [Invocations.replay, step, emitted, admitted, ↓reduceIte, ih, Option.map_some,
        List.cons_append, List.nil_append]

theorem Boundary.admits {state middle : State} {entry : Entry Action Mark Id Thread Input}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (boundary : Boundary adapter currentState state entry middle observations events) :
    admitEvents currentState state events = true := by
  cases boundary with
  | invoke id thread input admitted => simpa [admitEvents, admitEvent] using admitted
  | execute _ _ _ admitted => exact admitted

theorem Boundary.invocation {state middle : State} {entry : Entry Action Mark Id Thread Input}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (boundary : Boundary adapter currentState state entry middle observations events)
    {offset : Nat} {id : Id} {thread : Thread} {input : Input}
    (found : events[offset]? = some (.invoke id thread input)) :
    currentState state id thread input = true :=
  List.all_eq_true.mp boundary.admits _ (List.mem_of_getElem? found)

/-- An emitter cannot smuggle a rejected invocation into the event list.
Rejection precedes replay of the remaining entries, regardless of the offset. -/
theorem replay_reject_emitted_invoke {before : State} {action : Action} {mark : Mark}
    {head : State × Observation} {events : List (@Event Id Thread Input Output)}
    {rest : List (Entry Action Mark Id Thread Input)}
    (step : adapter.step before action = .ok head)
    (emitted : adapter.emit before action head mark = some events)
    {offset : Nat} {id : Id} {thread : Thread} {input : Input}
    (found : events[offset]? = some (.invoke id thread input))
    (rejected : currentState before id thread input = false) :
    replay adapter currentState before (.execute action mark :: rest) = none := by
  have blocked : admitEvents currentState before events = false := by
    cases admitted : admitEvents currentState before events with
    | false => rfl
    | true =>
      have allowed : currentState before id thread input = true :=
        List.all_eq_true.mp admitted _ (List.mem_of_getElem? found)
      simp [rejected] at allowed
  simp [replay, step, emitted, blocked]

/-- The exact event occurrence, including its containing entry, real earlier
run, complete emitted list and offset. The decomposition uses the very accepted
event list, so equal labels elsewhere cannot substitute for this index. -/
def EventAt (before : State) (entries : List (Entry Action Mark Id Thread Input))
    (events : List (@Event Id Thread Input Output)) (index : Nat)
    (event : @Event Id Thread Input Output) : Prop :=
  ∃ earlier later state observations priorEvents selected middle headObservations emitted following offset,
    entries = earlier ++ selected :: later ∧
    Run adapter currentState before earlier observations state priorEvents ∧
    events = priorEvents ++ (emitted ++ following) ∧
    priorEvents.length + offset = index ∧
    Boundary adapter currentState state selected middle headObservations emitted ∧
    emitted[offset]? = some event

private theorem eventAt_head {before middle : State} {entry : Entry Action Mark Id Thread Input}
    {observations : List Observation} {head events : List (@Event Id Thread Input Output)}
    {rest : List (Entry Action Mark Id Thread Input)} {offset : Nat} {event : @Event Id Thread Input Output}
    (boundary : Boundary adapter currentState before entry middle observations head)
    (found : head[offset]? = some event) :
    EventAt adapter currentState before (entry :: rest) (head ++ events) offset event :=
  ⟨[], rest, before, [], [], entry, middle, observations, head, events, offset,
    rfl, .nil, rfl, Nat.zero_add offset, boundary, found⟩

private theorem eventAt_cons {before middle : State} {entry : Entry Action Mark Id Thread Input}
    {observations : List Observation} {head events : List (@Event Id Thread Input Output)}
    {rest : List (Entry Action Mark Id Thread Input)} {index : Nat} {event : @Event Id Thread Input Output}
    (boundary : Boundary adapter currentState before entry middle observations head)
    (laterEvent : EventAt adapter currentState middle rest events index event) :
    EventAt adapter currentState before (entry :: rest) (head ++ events) (head.length + index) event := by
  obtain ⟨earlier, later, state, priorObservations, priorEvents, selected, next, selectedObservations,
    emitted, following, offset, same, run, eventEq, length, selectedBoundary, found⟩ := laterEvent
  refine ⟨entry :: earlier, later, state, observations ++ priorObservations, head ++ priorEvents,
    selected, next, selectedObservations, emitted, following, offset, ?_, .cons boundary run,
    ?_, ?_, selectedBoundary, found⟩
  · simp [same]
  · simp only [eventEq, List.append_assoc]
  · simp only [List.length_append]
    omega

theorem Run.event_at {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter currentState before entries observations after events) {index : Nat}
    {event : @Event Id Thread Input Output} (found : events[index]? = some event) :
    EventAt adapter currentState before entries events index event := by
  induction run generalizing index with
  | nil => simp at found
  | @cons before middle after entry rest headObservations observations head events boundary tail ih =>
    by_cases inHead : index < head.length
    · exact eventAt_head adapter currentState boundary
        (by simpa only [List.getElem?_append_left inHead] using found)
    · have inTail : head.length ≤ index := Nat.le_of_not_gt inHead
      have selected : events[index - head.length]? = some event := by
        simpa only [List.getElem?_append_right inTail] using found
      simpa only [Nat.add_sub_of_le inTail] using
        eventAt_cons adapter currentState boundary (ih selected)

/-- An invoke at precisely index has a matching actual prefix and succeeds at
that prefix's current state, even when it occurs inside an execute emission. -/
def InvocationAt (before : State) (entries : List (Entry Action Mark Id Thread Input))
    (events : List (@Event Id Thread Input Output)) (index : Nat) (id : Id) (thread : Thread)
    (input : Input) : Prop :=
  ∃ earlier later state observations priorEvents selected middle headObservations emitted following offset,
    entries = earlier ++ selected :: later ∧
    Run adapter currentState before earlier observations state priorEvents ∧
    replay adapter currentState before earlier = some ⟨state, observations, priorEvents⟩ ∧
    events = priorEvents ++ (emitted ++ following) ∧
    priorEvents.length + offset = index ∧
    Boundary adapter currentState state selected middle headObservations emitted ∧
    emitted[offset]? = some (.invoke id thread input) ∧
    currentState state id thread input = true

theorem Run.invocation_at {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter currentState before entries observations after events)
    {index : Nat} {id : Id} {thread : Thread} {input : Input}
    (found : events[index]? = some (.invoke id thread input)) :
    InvocationAt adapter currentState before entries events index id thread input := by
  obtain ⟨earlier, later, state, priorObservations, priorEvents, selected, middle, headObservations,
    emitted, following, offset, same, priorRun, eventEq, length, boundary, selectedEvent⟩ :=
    Run.event_at adapter currentState run found
  exact ⟨earlier, later, state, priorObservations, priorEvents, selected, middle, headObservations,
    emitted, following, offset, same, priorRun, Run.replay adapter currentState priorRun,
    eventEq, length, boundary, selectedEvent, Boundary.invocation adapter currentState boundary selectedEvent⟩

theorem replay_invocation_at {before : State} {entries : List (Entry Action Mark Id Thread Input)}
    {result : Result State Observation Id Thread Input Output}
    (accepted : replay adapter currentState before entries = some result)
    {index : Nat} {id : Id} {thread : Thread} {input : Input}
    (found : result.events[index]? = some (.invoke id thread input)) :
    InvocationAt adapter currentState before entries result.events index id thread input :=
  Run.invocation_at adapter currentState (replay_sound adapter currentState accepted) found

/-- Combine the original complete label protocol's invocation index with
admission at that very occurrence. The protocol contributes no ABI semantics. -/
theorem Run.interval_invocation [DecidableEq Id]
    {before after : State} {entries : List (Entry Action Mark Id Thread Input)}
    {observations : List Observation} {events : List (@Event Id Thread Input Output)}
    (run : Run adapter currentState before entries observations after events)
    (valid : Linearizability.Protocol events)
    {interval : Linearizability.Interval Id Thread Input Output}
    (member : interval ∈ Linearizability.intervals events) :
    InvocationAt adapter currentState before entries events interval.invocation
      interval.call.id interval.call.thread interval.call.input :=
  Run.invocation_at adapter currentState run (valid.2.2.1 interval member).2.2.1

end EDSL.Concurrency.CallTrace.Invocations

#audit_edsl
