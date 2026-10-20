/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.Linearizability
import EDSL.OS.TSO.CounterCheck
import EDSL.Audit

namespace EDSL.OS.TSO.CounterCalls
open X86
open EDSL.Concurrency

/-- This adapter is for the production scheduler's 32-bit modular counter,
not a 64-bit counter or a physical CPU execution. -/
abbrev Call := Linearizability.Call Nat Nat (BitVec 32) (BitVec 32)
abbrev Event := Linearizability.Event Nat Nat (BitVec 32) (BitVec 32)

/-- An RMW label names a call but supplies neither its input nor its result.
A response label claims a result at this actual issue, checked against RET. -/
inductive Mark where
  | quiet
  | rmw (id : Nat)
  | response (id thread : Nat) (value : BitVec 32)
  deriving DecidableEq, Repr

inductive Entry where
  | invoke (id thread : Nat) (input : BitVec 32)
  | execute (action : Action) (mark : Mark)
  deriving DecidableEq, Repr

def actions (entries : List Entry) : List Action :=
  entries.filterMap fun entry => match entry with
    | .invoke .. => none
    | .execute action _ => some action

def operation (call : Call) : Counter.Operation := ⟨call.thread, call.input, call.output⟩

def call (id : Nat) (operation : Counter.Operation) : Call :=
  ⟨id, operation.thread, operation.delta, operation.result⟩

def operations (events : List Event) : List Counter.Operation :=
  events.filterMap fun event => match event with
    | .point call => some (operation call)
    | _ => none

/-- Read the input from the real pre-issue context, not from event subtraction. -/
def operationAt (address : Word) (before : State) : Observation → Option Counter.Operation
  | .retired thread (some event) =>
    if event.address = address then
      before.workers[thread]?.map fun worker =>
        ⟨thread, (worker.context.registers .rax).setWidth 32, event.before⟩
    else none
  | _ => none

private theorem operationAt_quiet {address : Word} {before : State} {observation : Observation}
    (unobserved : Counter.eventsAt address [observation] = []) :
    operationAt address before observation = none := by
  cases observation with
  | retired thread event =>
    cases event with
    | none => rfl
    | some event =>
      by_cases same : event.address = address
      · simp [Counter.eventsAt, same] at unobserved
      · simp [operationAt, same]
  | blocked identifier => rfl
  | drained identifier store => rfl

private theorem operationAt_origin {address : Word} {before : State} {action : Action}
    {result : State × Observation} {op : Counter.Operation}
    (origin : Counter.Origin address before action result op) :
    operationAt address before result.2 = some op := by
  obtain ⟨worker, event, output, _, live, _, _, _, _, _, observed, addressEq, deltaEq, resultEq⟩ := origin
  simp only [operationAt, observed, addressEq, ↓reduceIte, live, Option.map_some]
  cases op
  simp_all

/-- Strong response evidence retains the actual decoded RET, its architectural
execution on the forwarded local view, the installed returned context, and the
zero-extended returned ticket. No future response is postulated. -/
def ReturnOrigin (before : State) (action : Action) (result : State × Observation)
    (thread : Nat) (value : BitVec 32) : Prop :=
  ∃ worker output,
    action = .issue thread ∧ before.workers[thread]? = some worker ∧ worker.returned = false ∧
    decodeAt (sharedState before worker) = .ok .ret ∧
    executeInstruction (localState before worker) .ret = .ok (.returned output) ∧
    result = (install before thread before.memory (.ofState output) true worker.buffer,
      .retired thread none) ∧ output.registers .rax = value.setWidth 64

def checkReturn (before : State) (action : Action) (result : State × Observation)
    (thread : Nat) (value : BitVec 32) : Bool :=
  match action, before.workers[thread]?, result.1.workers[thread]? with
  | .issue identifier, some prior, some after => decide (
      identifier = thread ∧ (decodeAt (sharedState before prior)).toOption = some .ret ∧
      after.returned = true ∧ after.context.registers .rax = value.setWidth 64 ∧
      result.2 = .retired thread none)
  | _, _, _ => false

theorem checkReturn_sound {before : State} {action : Action} {result : State × Observation}
    {thread : Nat} {value : BitVec 32} (success : TSO.step before action = .ok result)
    (checked : checkReturn before action result thread value = true) :
    ReturnOrigin before action result thread value := by
  cases action with
  | drain identifier => simp [checkReturn] at checked
  | issue identifier =>
    cases priorEq : before.workers[thread]? with
    | none => simp [checkReturn, priorEq] at checked
    | some prior =>
      cases afterEq : result.1.workers[thread]? with
      | none => simp [checkReturn, priorEq, afterEq] at checked
      | some after =>
        simp only [checkReturn, priorEq, afterEq] at checked
        have conditions : identifier = thread ∧ (decodeAt (sharedState before prior)).toOption = some .ret ∧
            after.returned = true ∧ after.context.registers .rax = value.setWidth 64 ∧
            result.2 = .retired thread none := of_decide_eq_true checked
        rcases conditions with ⟨rfl, decodedOption, returned, valueEq, _⟩
        have decoded : decodeAt (sharedState before prior) = .ok .ret := by
          cases decodedEq : decodeAt (sharedState before prior) <;> simp_all [Except.toOption]
        obtain ⟨worker, instruction, live, notReturned, actualDecode, _, effect⟩ :=
          issue_effect _ _ _ success
        have workerEq : worker = prior := Option.some.inj (live.symm.trans priorEq)
        subst worker
        have instructionEq : instruction = .ret := Except.ok.inj (actualDecode.symm.trans decoded)
        subst instruction
        cases effect with
        | queued pending _ _ _ _ _ => cases pending
        | ordinary _ _ _ executed _ =>
          cases executedRet : executeRet (localState before prior) <;>
            simp [executeInstruction, executedRet] at executed
        | @returned output _ _ _ executed _ =>
          have installed : (install before identifier before.memory (.ofState output) true prior.buffer
              ).workers[identifier]? = some ⟨.ofState output, true, prior.buffer⟩ :=
            List.getElem?_set_self (List.getElem_of_getElem? priorEq).1
          have same : after = ⟨.ofState output, true, prior.buffer⟩ :=
            Option.some.inj (afterEq.symm.trans installed)
          subst after
          exact ⟨prior, output, rfl, priorEq, notReturned, decoded, executed, rfl, valueEq⟩
        | atomic _ classified _ _ _ _ _ _ => cases classified
        | blocked _ classified _ => cases classified

/-- This is only label extraction. Its soundness below depends on actual
scheduler success and CounterCheck's current-state interference check. -/
def emit (address : Word) (before : State) (result : State × Observation) (action : Action) :
    Mark → Option (List Event)
  | .quiet => if operationAt address before result.2 = none then some [] else none
  | .rmw id => (operationAt address before result.2).map fun op => [.point (call id op)]
  | .response id thread value =>
    if operationAt address before result.2 = none then
      if checkReturn before action result thread value then some [.respond id thread value] else none
    else none

inductive Emission (address : Word) (before : State) (action : Action)
    (result : State × Observation) : Mark → List Event → Prop where
  | quiet (unchanged : loadDWord result.1.memory address = loadDWord before.memory address)
      (unobserved : Counter.eventsAt address [result.2] = []) :
      Emission address before action result .quiet []
  | point (id : Nat) (op : Counter.Operation) (origin : Counter.Origin address before action result op) :
      Emission address before action result (.rmw id) [.point (call id op)]
  | response (id thread : Nat) (value : BitVec 32)
      (unchanged : loadDWord result.1.memory address = loadDWord before.memory address)
      (unobserved : Counter.eventsAt address [result.2] = [])
      (origin : ReturnOrigin before action result thread value) :
      Emission address before action result (.response id thread value) [.respond id thread value]

theorem emit_sound {address : Word} {before : State} {action : Action}
    {result : State × Observation} {mark : Mark} {events : List Event}
    (permitted : Counter.checkPermitted address before action = true)
    (success : TSO.step before action = .ok result)
    (emitted : emit address before result action mark = some events) :
    Emission address before action result mark events := by
  cases Counter.step_effect (Counter.checkPermitted_sound permitted) success with
  | quiet unchanged unobserved =>
    have absent := operationAt_quiet (before := before) unobserved
    cases mark with
    | quiet =>
      simp only [emit, absent, ↓reduceIte, Option.some.injEq] at emitted
      subst events
      exact .quiet unchanged unobserved
    | rmw id => simp [emit, absent] at emitted
    | response id thread value =>
      have checked : checkReturn before action result thread value = true := by
        by_cases h : checkReturn before action result thread value = true
        · exact h
        · simp [emit, absent, h] at emitted
      have same : events = [.respond id thread value] := by simpa [emit, absent, checked] using emitted.symm
      subst events
      exact .response id thread value unchanged unobserved (checkReturn_sound success checked)
  | addition op origin =>
    have present := operationAt_origin origin
    cases mark with
    | quiet => simp [emit, present] at emitted
    | rmw id =>
      simp only [emit, present, Option.map_some, Option.some.injEq] at emitted
      subst events
      exact .point id op origin
    | response id thread value => simp [emit, present] at emitted

structure Result where
  state : State
  observations : List Observation
  events : List Event

/-- Invocation entries are environmental annotations at actual finite prefix
boundaries. Execute entries always call production `TSO.step`; no sequential
wrapper suppresses buffering, blocked attempts, drains, or peer interleaving. -/
def replay (address : Word) (state : State) : List Entry → Option Result
  | [] => some ⟨state, [], []⟩
  | .invoke id thread input :: rest =>
    (replay address state rest).map fun tail =>
      ⟨tail.state, tail.observations, .invoke id thread input :: tail.events⟩
  | .execute action mark :: rest =>
    if Counter.checkPermitted address state action then
      match TSO.step state action with
      | .error _ => none
      | .ok result =>
        match emit address state result action mark with
        | none => none
        | some head => (replay address result.1 rest).map fun tail =>
            ⟨tail.state, result.2 :: tail.observations, head ++ tail.events⟩
    else none

inductive Run (address : Word) : State → List Entry → List Observation → State → List Event → Prop where
  | nil {state} : Run address state [] [] state []
  | invoke {state rest observations after events} (id thread : Nat) (input : BitVec 32)
      (tail : Run address state rest observations after events) :
      Run address state (.invoke id thread input :: rest) observations after (.invoke id thread input :: events)
  | execute {before middle after action mark rest observations observation head events}
      (step : TSO.step before action = .ok (middle, observation))
      (emission : Emission address before action (middle, observation) mark head)
      (tail : Run address middle rest observations after events) :
      Run address before (.execute action mark :: rest) (observation :: observations) after (head ++ events)

theorem replay_sound {address : Word} {before : State} {entries : List Entry} {result : Result}
    (accepted : replay address before entries = some result) :
    Run address before entries result.observations result.state result.events := by
  induction entries generalizing before result with
  | nil => simp only [replay, Option.some.injEq] at accepted; subst result; exact .nil
  | cons entry rest ih =>
    cases entry with
    | invoke id thread input =>
      cases tailEq : replay address before rest with
      | none => simp [replay, tailEq] at accepted
      | some tail =>
        simp only [replay, tailEq, Option.map_some, Option.some.injEq] at accepted
        subst result
        exact .invoke id thread input (ih tailEq)
    | execute action mark =>
      by_cases permitted : Counter.checkPermitted address before action = true
      · cases first : TSO.step before action with
        | error fault => simp [replay, permitted, first] at accepted
        | ok head =>
          cases emitted : emit address before head action mark with
          | none => simp [replay, permitted, first, emitted] at accepted
          | some events =>
            cases tailEq : replay address head.1 rest with
            | none => simp [replay, permitted, first, emitted, tailEq] at accepted
            | some tail =>
              simp only [replay, permitted, ↓reduceIte, first, emitted, tailEq,
                Option.map_some, Option.some.injEq] at accepted
              subst result
              exact .execute first (emit_sound permitted first emitted) (ih tailEq)
      · simp [replay, permitted] at accepted

theorem Run.machineHistory {address : Word} {before after : State} {entries : List Entry}
    {observations : List Observation} {events : List Event}
    (run : Run address before entries observations after events) :
    Counter.MachineHistory address before (actions entries) observations after (operations events) := by
  induction run with
  | nil => exact .nil
  | invoke id thread input _ ih => simpa [actions, operations] using ih
  | execute step emission _ ih =>
    cases emission with
    | quiet unchanged unobserved =>
      simpa [actions, operations] using Counter.MachineHistory.quiet step unchanged unobserved ih
    | point id op origin =>
      simpa [actions, operations, operation, call] using Counter.MachineHistory.addition step origin ih
    | response id thread value unchanged unobserved _ =>
      simpa [actions, operations] using Counter.MachineHistory.quiet step unchanged unobserved ih

/-- Independent fetch-add results are proved from actual origins and RAM
continuity, not checked as part of label admission. -/
private theorem sequential_of_history {address : Word} {before after : State}
    {schedule : List Action} {observations : List Observation} {ops : List Counter.Operation}
    {initialValue : BitVec 32} (read : loadDWord before.memory address = .ok initialValue)
    (history : Counter.MachineHistory address before schedule observations after ops) :
    ∃ finalValue, loadDWord after.memory address = .ok finalValue ∧
      Counter.Sequential initialValue ops finalValue := by
  induction history generalizing initialValue with
  | nil => exact ⟨initialValue, read, .nil _⟩
  | quiet _ unchanged _ _ ih => exact ih (unchanged.trans read)
  | addition _ origin _ ih =>
    have effects := origin.effects
    have returned := Except.ok.inj (read.symm.trans effects.1)
    obtain ⟨finalValue, finalRead, sequential⟩ := ih effects.2.1
    exact ⟨finalValue, finalRead, .cons returned.symm (by rw [returned]) sequential⟩

/-- The action and state in an origin are tied to an actual prefix of this
very schedule. In particular they are not existential future execution. -/
def Occurs (before : State) (schedule : List Action)
    (property : State → Action → State × Observation → Prop) : Prop :=
  ∃ pastActions suffix state observations action result,
    schedule = pastActions ++ action :: suffix ∧
    TSO.schedule before pastActions = .ok (state, observations) ∧
    TSO.step state action = .ok result ∧ property state action result

private theorem occurs_head {before middle : State} {action : Action} {observation : Observation}
    {rest : List Action} {property : State → Action → State × Observation → Prop}
    (step : TSO.step before action = .ok (middle, observation))
    (origin : property before action (middle, observation)) :
    Occurs before (action :: rest) property :=
  ⟨[], rest, before, [], action, (middle, observation), rfl, rfl, step, origin⟩

private theorem occurs_prepend {before middle : State} {action : Action} {observation : Observation}
    {rest : List Action} {property : State → Action → State × Observation → Prop}
    (step : TSO.step before action = .ok (middle, observation))
    (later : Occurs middle rest property) : Occurs before (action :: rest) property := by
  obtain ⟨pastActions, suffix, state, observations, selected, result, same, scheduled, actual, origin⟩ := later
  refine ⟨action :: pastActions, suffix, state, observation :: observations, selected, result,
    ?_, ?_, actual, origin⟩
  · simp [same]
  · simp [TSO.schedule, step, scheduled]

def Backing (address : Word) : Event → State → Action → State × Observation → Prop
  | .invoke .. => fun _ _ _ => False
  | .point call => fun before action result => Counter.Origin address before action result (operation call)
  | .respond _ thread value => fun before action result => ReturnOrigin before action result thread value

private theorem Emission.backed {address : Word} {before : State} {action : Action}
    {result : State × Observation} {mark : Mark} {events : List Event}
    (emission : Emission address before action result mark events)
    {event : Event} (member : event ∈ events) : Backing address event before action result := by
  cases emission with
  | quiet unchanged unobserved => cases member
  | point id op origin =>
    simp only [List.mem_singleton] at member
    subst event
    simpa [Backing, operation, call] using origin
  | response id thread value _ _ origin =>
    simp only [List.mem_singleton] at member
    subst event
    exact origin

/-- Every internal point and every response has an execution origin at an
actual prefix. Only invocation labels are environmental. -/
theorem Run.backed {address : Word} {before after : State} {entries : List Entry}
    {observations : List Observation} {events : List Event}
    (run : Run address before entries observations after events)
    {event : Event} (member : event ∈ events) (internal : event.kind ≠ 0) :
    Occurs before (actions entries) (Backing address event) := by
  induction run with
  | nil => cases member
  | invoke id thread input _ ih =>
    rcases List.mem_cons.mp member with same | later
    · subst event
      exact False.elim (internal rfl)
    · simpa [actions] using ih later
  | execute step emission _ ih =>
    rcases List.mem_append.mp member with head | later
    · simpa [actions] using occurs_head step (emission.backed head)
    · simpa [actions] using occurs_prepend step (ih later)

/-- An invocation is environmental; a point/response boundary is one actual
selected step with a singleton justified emission. -/
inductive EventBoundary (address : Word) (state : State) : Entry → Event → Prop where
  | invoke (id thread : Nat) (input : BitVec 32) :
      EventBoundary address state (.invoke id thread input) (.invoke id thread input)
  | execute {action mark result event}
      (step : TSO.step state action = .ok result)
      (emission : Emission address state action result mark [event]) :
      EventBoundary address state (.execute action mark) event

/-- An exact event position is bound to an entry of this schedule, with the
actual earlier entries replayed as `Run`. The number of earlier emitted labels
is exactly the requested event index. -/
def EventAt (address : Word) (before : State) (entries : List Entry) (index : Nat) (event : Event) : Prop :=
  ∃ earlier later state observations priorEvents selected,
    entries = earlier ++ selected :: later ∧
    Run address before earlier observations state priorEvents ∧
    priorEvents.length = index ∧ EventBoundary address state selected event

private theorem eventAt_head {address : Word} {before : State} {entry : Entry}
    {event : Event} {rest : List Entry} (boundary : EventBoundary address before entry event) :
    EventAt address before (entry :: rest) 0 event :=
  ⟨[], rest, before, [], [], entry, rfl, .nil, rfl, boundary⟩

private theorem eventAt_invoke {address : Word} {before : State} {rest : List Entry}
    {index : Nat} {event : Event} (id thread : Nat) (input : BitVec 32)
    (laterEvent : EventAt address before rest index event) :
    EventAt address before (.invoke id thread input :: rest) (index + 1) event := by
  obtain ⟨earlier, later, state, observations, priorEvents, selected, same, run, length, boundary⟩ := laterEvent
  refine ⟨.invoke id thread input :: earlier, later, state, observations,
    .invoke id thread input :: priorEvents, selected, ?_, .invoke id thread input run, ?_, boundary⟩
  · simp [same]
  · simp [length]

private theorem eventAt_execute {address : Word} {before middle : State}
    {action : Action} {observation : Observation} {mark : Mark} {head : List Event} {rest : List Entry}
    {index : Nat} {event : Event} (step : TSO.step before action = .ok (middle, observation))
    (emission : Emission address before action (middle, observation) mark head)
    (laterEvent : EventAt address middle rest index event) :
    EventAt address before (.execute action mark :: rest) (head.length + index) event := by
  obtain ⟨earlier, later, state, observations, priorEvents, selected, same, run, length, boundary⟩ := laterEvent
  refine ⟨.execute action mark :: earlier, later, state, observation :: observations,
    head ++ priorEvents, selected, ?_, .execute step emission run, ?_, boundary⟩
  · simp [same]
  · simp [length]

/-- Indexed correspondence, retaining the exact annotation boundary as well as
its actual execution prefix. This is stronger than an existential origin of an
unlocated event with an equal arithmetic result. -/
theorem Run.event_at {address : Word} {before after : State} {entries : List Entry}
    {observations : List Observation} {events : List Event}
    (run : Run address before entries observations after events) {index : Nat} {event : Event}
    (found : events[index]? = some event) : EventAt address before entries index event := by
  induction run generalizing index with
  | nil => simp at found
  | invoke id thread input _ ih =>
    cases index with
    | zero =>
      have same := Option.some.inj found
      subst event
      exact eventAt_head (.invoke id thread input)
    | succ index => exact eventAt_invoke id thread input (ih (by simpa using found))
  | execute step emission _ ih =>
    cases emission with
    | quiet unchanged unobserved =>
      simpa using eventAt_execute step (.quiet unchanged unobserved) (ih found)
    | point id op origin =>
      cases index with
      | zero =>
        have same := Option.some.inj found
        subst event
        exact eventAt_head (.execute step (.point id op origin))
      | succ index =>
        simpa [Nat.add_comm] using eventAt_execute step (.point id op origin) (ih (by simpa using found))
    | response id thread value unchanged unobserved origin =>
      cases index with
      | zero =>
        have same := Option.some.inj found
        subst event
        exact eventAt_head (.execute step (.response id thread value unchanged unobserved origin))
      | succ index =>
        simpa [Nat.add_comm] using eventAt_execute step (.response id thread value unchanged unobserved origin)
          (ih (by simpa using found))

/-- All three boundaries of each complete call refer to this same actual run.
The strict invocation/point/response inequalities come from `Protocol`. -/
theorem Run.interval_boundaries {address : Word} {before after : State} {entries : List Entry}
    {observations : List Observation} {events : List Event}
    (run : Run address before entries observations after events) (valid : Linearizability.Protocol events)
    {interval : Linearizability.Interval Nat Nat (BitVec 32) (BitVec 32)}
    (member : interval ∈ Linearizability.intervals events) :
    EventAt address before entries interval.invocation
      (.invoke interval.call.id interval.call.thread interval.call.input) ∧
    EventAt address before entries interval.point (.point interval.call) ∧
    EventAt address before entries interval.response
      (.respond interval.call.id interval.call.thread interval.call.output) := by
  have labels := valid.2.2.1 interval member
  exact ⟨run.event_at labels.2.2.1, run.event_at labels.2.2.2.1, run.event_at labels.2.2.2.2⟩

private theorem calls_operations (events : List Event) :
    (Linearizability.calls events).map operation = operations events := by
  rw [Linearizability.calls_eq_points, List.map_filterMap]
  apply congrArg (fun f : Event → Option Counter.Operation => events.filterMap f)
  funext event
  cases event <;> rfl

/-- Complete-history admission. Missing responses are rejected, even if the
actual prefix is otherwise a valid machine execution. -/
def checkComplete (address : Word) (before : State) (entries : List Entry) : Bool :=
  match replay address before entries with
  | none => false
  | some result => Linearizability.check result.events

/-- Complete call linearizability for finite *production TSO32 model* schedules.
The two premises are an actual initial RAM read and executable admission of
environmental annotations. Sequential results and real-time order are derived.
`Run.interval_boundaries` locates all three call boundaries in this actual run;
`Run.backed` also exposes convenient prefix-bound LOCK XADD and RET origins. -/
theorem checked_linearization {address : Word} {before : State} {entries : List Entry}
    {initialValue : BitVec 32} (read : loadDWord before.memory address = .ok initialValue)
    (checked : checkComplete address before entries = true) :
    ∃ result finalValue,
      replay address before entries = some result ∧
      Run address before entries result.observations result.state result.events ∧
      TSO.schedule before (actions entries) = .ok (result.state, result.observations) ∧
      loadDWord result.state.memory address = .ok finalValue ∧
      Counter.MachineHistory address before (actions entries) result.observations result.state
        (operations result.events) ∧
      Linearizability.Linearization result.events (fun calls =>
        Counter.Sequential initialValue (calls.map operation) finalValue) ∧
      finalValue = initialValue + Counter.totalDelta (operations result.events) := by
  cases accepted : replay address before entries with
  | none => simp [checkComplete, accepted] at checked
  | some result =>
    have run := replay_sound accepted
    have valid : Linearizability.Protocol result.events :=
      Linearizability.check_sound (by simpa [checkComplete, accepted] using checked)
    have history := run.machineHistory
    obtain ⟨finalValue, finalRead, sequential⟩ := sequential_of_history read history
    refine ⟨result, finalValue, rfl, run, history.trace.schedule, finalRead, history,
      ?_, sequential.total⟩
    apply Linearizability.linearize valid
    simpa [calls_operations] using sequential

end EDSL.OS.TSO.CounterCalls

#audit_edsl
