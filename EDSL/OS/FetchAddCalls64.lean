/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.CallTrace
import EDSL.OS.TSO64History
import EDSL.OS.TSO64.Access
import EDSL.OS.TSO64.Return
import EDSL.X86.Sequential.Return

namespace EDSL.OS.FetchAddCalls64
open X86 Concurrency

abbrev Call (Id : Type) := ModuloCounter.Call 64 Id Nat
abbrev Event (Id : Type) := ModuloCounter.Event 64 Id Nat

/-- Point annotations name occurrences, including identical zero updates.
Inputs and outputs are captured from execution, not supplied by the mark. -/
inductive Mark (Id : Type) where
  | quiet
  | rmw (id : Id)
  | response (id : Id) (tid : Nat) (value : Word)
  deriving DecidableEq, Repr

abbrev Entry (Id : Type) := CallTrace.Entry TSO64.Action (Mark Id) Id Nat Word

variable {Id : Type}

/-- Present invariants only. The selected identity and entire original
descriptor persist; neither future success nor a desired value is stored. -/
structure CheckedState (target : Atomics64.CellId64) (cell : Atomics64.Cell) where
  state : TSO64.State
  valid : TSO64.WellFormed state
  live : state.world.cells target = some cell

def read (state : TSO64.State) (cell : Atomics64.Cell) : Except Error Word :=
  loadQWord (AddressSpace.toMemory state.world.legacy.shared.resources.space) cell.address

theorem CheckedState.read_exists {target cell} (state : CheckedState target cell) :
    ∃ value, read state.state cell = .ok value :=
  (state.valid.1.cells _ _ state.live).2.1.load_exists

/-- One actual selected scheduler step. Successor invariants are proved from
that very step; there is no poststate invariant oracle in this computation. -/
def step {target cell} (before : CheckedState target cell) (action : TSO64.Action) :
    Except TSO64.Fault (CheckedState target cell × TSO64.Observation) :=
  match success : TSO64.step before.state action with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, TSO64.step_wellFormed before.valid success,
      by rw [(TSO64.step_stable success).cells]; exact before.live⟩, result.2)

theorem step_underlying {target cell} {before after : CheckedState target cell}
    {action : TSO64.Action} {observation : TSO64.Observation}
    (success : step before action = .ok (after, observation)) :
    TSO64.step before.state action = .ok (after.state, observation) := by
  unfold step at success
  split at success
  · cases success
  · rename_i result actual
    have same := Except.ok.inj success
    exact actual.trans (congrArg Except.ok (congrArg
      (fun pair : CheckedState target cell × TSO64.Observation => (pair.1.state, pair.2)) same))

def targetEvent (target : Atomics64.CellId64) : TSO64.Observation →
    Option (Nat × Atomics64.FetchAddEvent)
  | .rmw tid event => if event.cell = target then some (tid, event) else none
  | _ => none

def call (id : Id) (tid : Nat) (event : Atomics64.FetchAddEvent) : Call Id :=
  ⟨id, tid, event.arithmetic.delta, event.arithmetic.event.before⟩

/-- The full source is authenticated by the actual decoded joint effect.
Scheduler list index and resource actor are separate, explicitly related facts. -/
def RMWOrigin (target : Atomics64.CellId64) (before : TSO64.State)
    (action : TSO64.Action) (result : TSO64.State × TSO64.Observation) (point : Call Id) : Prop :=
  ∃ event af worker instruction identifier machine,
    result.2 = .rmw point.thread event ∧ action = .issue point.thread af ∧
    before.workers[point.thread]? = some worker ∧ worker.phase ≠ .returned ∧ worker.pending = [] ∧
    TSO64.decode (TSO64.fetchCPU before worker) = .ok (.locked instruction) ∧
    Atomics64.FetchAddMachineEffect before.world worker.resources.actor identifier
      (TSO64.sharedCPU before worker) instruction (result.1.world, event) machine ∧
    event.cell = target ∧ point.input = (TSO64.sharedCPU before worker).registers instruction.source ∧
    point.output = event.arithmetic.event.before ∧ event.actor = worker.resources.actor ∧
    result.1 = TSO64.install before point.thread result.1.world
      { worker with context := .ofCPU machine.state }

theorem rmw_origin {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation}
    {tid : Nat} {event : Atomics64.FetchAddEvent} (id : Id)
    (success : TSO64.step before action = .ok result)
    (observed : result.2 = .rmw tid event) (selected : event.cell = target) :
    RMWOrigin target before action result (call id tid event) := by
  have actual : TSO64.step before action = .ok (result.1, .rmw tid event) := by
    exact success.trans (congrArg Except.ok (Prod.ext rfl observed))
  obtain ⟨af, worker, instruction, identifier, machine, issued, live, running, empty,
    fetched, effect, installed⟩ := TSO64History.step_event_origin actual
  exact ⟨event, af, worker, instruction, identifier, machine, observed, issued, live,
    running, empty, fetched, effect, selected, effect.delta, rfl,
    (Atomics64.fetchAdd_sound _ _ _ _ _ effect.checked).2.2.2.1, installed⟩

/-- A response is at actual RET, with the original caller loan and current
original-slot read, the local machine step, and the exact installed context.
The own FIFO is retained and is permitted to be nonempty. -/
def ReturnOrigin (before : TSO64.State) (action : TSO64.Action)
    (result : TSO64.State × TSO64.Observation) (tid : Nat) (value : Word) : Prop :=
  ∃ af worker output observation,
    action = .issue tid af ∧ before.workers[tid]? = some worker ∧ worker.phase ≠ .returned ∧
    TSO64.LeaseCurrent before.world worker.resources.actor worker.resources.caller ∧
    before.world.legacy.shared.loans worker.resources.caller.identifier = some worker.resources.caller.loan ∧
    worker.resources.caller.loan.region = AddressSpace.qwordRegion worker.resources.callerAddress ∧
    TSO64.decode (TSO64.fetchCPU before worker) = .ok (.ordinary (.legacy .ret)) ∧
    Sequential.decodeAt (TSO64.localCPU before worker) = .ok (.legacy .ret) ∧
    Sequential.execute (TSO64.localCPU before worker) (.legacy .ret) af = .ok observation ∧
    Sequential.step af (TSO64.localCPU before worker) = .ok observation ∧
    observation.result = .returned output ∧
    (TSO64.localCPU before worker).registers .rsp = worker.resources.callerAddress ∧
    (∃ target, Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok target ∧
      readWord (TSO64.localCPU before worker).memory worker.resources.callerAddress = .ok target) ∧
    result = (TSO64.install before tid before.world
      { worker with context := .ofCPU output, phase := .returned }, .returned tid) ∧
    output.registers .rax = value

def returnValue (result : TSO64.State × TSO64.Observation) : Option (Nat × Word) :=
  match result.2 with
  | .returned tid => result.1.workers[tid]?.map fun worker => (tid, worker.context.registers .rax)
  | _ => none

private theorem return_origin_legacy {before : TSO64.State} {action : TSO64.Action}
    {result : TSO64.State × TSO64.Observation} {tid : Nat} {value : Word}
    (origin : TSO64.Return.ReturnOrigin before action result tid value) :
    ReturnOrigin before action result tid value := by
  obtain ⟨af, worker, output, observation, issued, live, running, _code, caller,
    callerLive, callerRegion, _bounds, fetched, _effect, decoded, executed,
    stepped, outcome, slot, read, installed, actualValue⟩ := origin
  exact ⟨af, worker, output, observation, issued, live, running, caller,
    callerLive, callerRegion, fetched, decoded, executed, stepped, outcome,
    slot, read, installed, actualValue⟩

theorem returned_origin {before : TSO64.State} {action : TSO64.Action}
    {after : TSO64.State} {tid : Nat} (valid : TSO64.WellFormed before)
    (success : TSO64.step before action = .ok (after, .returned tid)) :
    ∃ value, returnValue (after, .returned tid) = some (tid, value) ∧
      ReturnOrigin before action (after, .returned tid) tid value := by
  obtain ⟨value, response, origin⟩ := TSO64.Return.returned_origin valid success
  exact ⟨value, response, return_origin_legacy origin⟩

private theorem returnValue_sound {before : TSO64.State} {action : TSO64.Action}
    {result : TSO64.State × TSO64.Observation} {tid : Nat} {value : Word}
    (valid : TSO64.WellFormed before) (success : TSO64.step before action = .ok result)
    (accepted : returnValue result = some (tid, value)) : ReturnOrigin before action result tid value := by
  exact return_origin_legacy (TSO64.Return.returnValue_sound valid success accepted)

private theorem quiet_load {target cell} {before after : CheckedState target cell}
    {action : TSO64.Action} {observation : TSO64.Observation}
    (success : step before action = .ok (after, observation))
    (silent : targetEvent target observation = none) : read after.state cell = read before.state cell := by
  obtain ⟨prior, readBefore⟩ := before.read_exists
  obtain ⟨next, readAfter⟩ := after.read_exists
  have projected := (TSO64History.step_history (step_underlying success)).projection
    before.valid.1 target cell before.live prior next readBefore readAfter
  have same : next = prior := by
    cases observation with
    | rmw tid event =>
      by_cases selected : event.cell = target
      · simp [targetEvent, selected] at silent
      · simpa only [TSO64History.label, AtomicFetchAddHistory64.Projection, selected,
          ↓reduceIte] using projected
    | ordinary _ | returned _ | blocked _ | drained _ _ => exact projected
  rw [readBefore, readAfter, same]

def emit {target cell} (_before : CheckedState target cell) (_action : TSO64.Action)
    (result : CheckedState target cell × TSO64.Observation) : Mark Id → Option (List (Event Id))
  | .quiet => if targetEvent target result.2 = none then some [] else none
  | .rmw id => (targetEvent target result.2).map fun (tid, event) => [.point (call id tid event)]
  | .response id tid value =>
    if returnValue (result.1.state, result.2) = some (tid, value)
    then some [.respond id tid value] else none

inductive Emission {target cell} (before : CheckedState target cell) (action : TSO64.Action)
    (result : CheckedState target cell × TSO64.Observation) : Mark Id → List (Event Id) → Prop where
  | quiet (silent : targetEvent target result.2 = none)
      (unchanged : read result.1.state cell = read before.state cell) : Emission before action result .quiet []
  | point {id tid event} (observed : result.2 = .rmw tid event) (selected : event.cell = target)
      (origin : RMWOrigin target before.state action (result.1.state, result.2) (call id tid event)) :
      Emission before action result (.rmw id) [.point (call id tid event)]
  | response {id tid value}
      (origin : ReturnOrigin before.state action (result.1.state, result.2) tid value)
      (unchanged : read result.1.state cell = read before.state cell) :
      Emission before action result (.response id tid value) [.respond id tid value]

theorem emit_sound {target cell} {before : CheckedState target cell} {action : TSO64.Action}
    {result : CheckedState target cell × TSO64.Observation} {mark : Mark Id} {events : List (Event Id)}
    (success : step before action = .ok result) (accepted : emit before action result mark = some events) :
    Emission before action result mark events := by
  cases mark with
  | quiet =>
    by_cases silent : targetEvent target result.2 = none
    · simp only [emit, silent, ↓reduceIte, Option.some.injEq] at accepted
      subst events
      exact .quiet silent (quiet_load success silent)
    · simp [emit, silent] at accepted
  | rmw id =>
    cases observed : result.2 with
    | rmw tid event =>
      by_cases selected : event.cell = target
      · simp only [emit, observed, targetEvent, selected, ↓reduceIte, Option.map_some,
          Option.some.injEq] at accepted
        subst events
        exact .point observed selected (rmw_origin id (step_underlying success) observed selected)
      · simp [emit, observed, targetEvent, selected] at accepted
    | ordinary _ | returned _ | blocked _ | drained _ _ => simp [emit, observed, targetEvent] at accepted
  | response id tid value =>
    by_cases returned : returnValue (result.1.state, result.2) = some (tid, value)
    · simp only [emit, returned, ↓reduceIte, Option.some.injEq] at accepted
      subst events
      have silent : targetEvent target result.2 = none := by
        cases observed : result.2 <;> simp_all [returnValue, targetEvent]
      exact .response (returnValue_sound before.valid (step_underlying success) returned)
        (quiet_load success silent)
    · simp [emit, returned] at accepted

def adapter (Id : Type) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :
    CallTrace.Adapter (CheckedState target cell) TSO64.Action TSO64.Observation TSO64.Fault
      (Mark Id) Id Nat Word Word := ⟨step, Emission, emit, emit_sound⟩

abbrev Result (Id : Type) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :=
  CallTrace.Result (CheckedState target cell) TSO64.Observation Id Nat Word Word

abbrev replay {Id : Type} (target : Atomics64.CellId64) (cell : Atomics64.Cell) :=
  CallTrace.replay (adapter Id target cell)
abbrev Run {Id : Type} (target : Atomics64.CellId64) (cell : Atomics64.Cell) :=
  CallTrace.Run (adapter Id target cell)
abbrev checkComplete {Id : Type} [DecidableEq Id] (target : Atomics64.CellId64) (cell : Atomics64.Cell) :=
  CallTrace.checkComplete (adapter Id target cell)

private theorem trace_underlying {target cell} {before after : CheckedState target cell}
    {selected : List TSO64.Action} {observations : List TSO64.Observation}
    (trace : CallTrace.Trace (adapter Id target cell) before selected observations after) :
    TSO64.schedule before.state selected = .ok (after.state, observations) := by
  induction trace with
  | nil => rfl
  | @cons before middle after action actions observation observations first tail ih =>
    rw [TSO64.schedule, step_underlying first]
    change Except.bind (TSO64.schedule middle.state actions)
      (fun tail => .ok (tail.1, observation :: tail.2)) = .ok (after.state, observation :: observations)
    rw [ih]
    rfl

theorem Run.underlying {target cell} {before after : CheckedState target cell}
    {entries : List (Entry Id)} {observations : List TSO64.Observation} {events : List (Event Id)}
    (run : Run target cell before entries observations after events) :
    TSO64.schedule before.state (CallTrace.actions entries) = .ok (after.state, observations) :=
  trace_underlying (CallTrace.Run.trace (adapter Id target cell) run)

/-- Specialize the generic indexed boundary to an actual RMW in the exact
selected prefix. Equal event values at another position cannot substitute. -/
theorem point_at {target cell} {before : CheckedState target cell} {entries : List (Entry Id)}
    {index : Nat} {point : Call Id}
    (located : CallTrace.EventAt (adapter Id target cell) before entries index (.point point)) :
    ∃ (earlier later : List (Entry Id)) (current : CheckedState target cell)
      (observations : List TSO64.Observation) (priorEvents : List (Event Id))
      (action : TSO64.Action) (mark : Mark Id)
      (result : CheckedState target cell × TSO64.Observation),
      entries = earlier ++ .execute action mark :: later ∧
      Run target cell before earlier observations current priorEvents ∧
      priorEvents.length = index ∧
      TSO64.schedule before.state (CallTrace.actions earlier) = .ok (current.state, observations) ∧
      TSO64.step current.state action = .ok (result.1.state, result.2) ∧
      RMWOrigin target current.state action (result.1.state, result.2) point := by
  obtain ⟨earlier, later, current, observations, priorEvents, entry, offset, same, earlierRun, length, boundary⟩ := located
  cases boundary with
  | execute first origin selected =>
    cases origin with
    | quiet silent unchanged => simp at selected
    | response origin unchanged => cases offset <;> simp at selected
    | point observed chosen origin =>
      cases offset with
      | succ offset => simp at selected
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Linearizability.Event.point.injEq] at selected
        cases selected
        exact ⟨earlier, later, current, observations, priorEvents, _, _, _, same, earlierRun,
          by simpa only [Nat.add_zero] using length, Run.underlying earlierRun, step_underlying first, origin⟩

/-- A response's exact indexed prefix contains the real RET and its current
original caller authority. It is not evidence of FIFO publication or release. -/
theorem response_at {target cell} {before : CheckedState target cell} {entries : List (Entry Id)}
    {index : Nat} {id : Id} {tid : Nat} {value : Word}
    (located : CallTrace.EventAt (adapter Id target cell) before entries index (.respond id tid value)) :
    ∃ (earlier later : List (Entry Id)) (current : CheckedState target cell)
      (observations : List TSO64.Observation) (priorEvents : List (Event Id))
      (action : TSO64.Action) (mark : Mark Id)
      (result : CheckedState target cell × TSO64.Observation),
      entries = earlier ++ .execute action mark :: later ∧
      Run target cell before earlier observations current priorEvents ∧
      priorEvents.length = index ∧
      TSO64.schedule before.state (CallTrace.actions earlier) = .ok (current.state, observations) ∧
      TSO64.step current.state action = .ok (result.1.state, result.2) ∧
      ReturnOrigin current.state action (result.1.state, result.2) tid value := by
  obtain ⟨earlier, later, current, observations, priorEvents, entry, offset, same, earlierRun, length, boundary⟩ := located
  cases boundary with
  | execute first origin selected =>
    cases origin with
    | quiet silent unchanged => simp at selected
    | point observed chosen origin => cases offset <;> simp at selected
    | response origin unchanged =>
      cases offset with
      | succ offset => simp at selected
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Linearizability.Event.respond.injEq] at selected
        rcases selected with ⟨rfl, rfl, rfl⟩
        exact ⟨earlier, later, current, observations, priorEvents, _, _, _, same, earlierRun,
          by simpa only [Nat.add_zero] using length, Run.underlying earlierRun, step_underlying first, origin⟩

private theorem Emission.sequential {target cell} {before after : CheckedState target cell}
    {action : TSO64.Action} {observation : TSO64.Observation} {mark : Mark Id} {events : List (Event Id)}
    (success : step before action = .ok (after, observation))
    (emission : Emission before action (after, observation) mark events)
    {prior next : Word} (readBefore : read before.state cell = .ok prior)
    (readAfter : read after.state cell = .ok next) :
    ModuloCounter.Sequential prior (events.filterMap Linearizability.Event.call?) next := by
  cases emission with
  | quiet silent unchanged | response origin unchanged =>
    have same := Except.ok.inj (readAfter.symm.trans (unchanged.trans readBefore))
    subst next
    exact .nil _
  | @point id tid event observed selected origin =>
    change observation = .rmw tid event at observed
    have projected := (TSO64History.step_history (step_underlying success)).projection
      before.valid.1 target cell before.live prior next readBefore readAfter
    change AtomicFetchAddHistory64.Projection target (TSO64History.label observation) prior next at projected
    have arithmetic : ModuloCounter.Step prior event.arithmetic.delta event.arithmetic.event.before next := by
      simpa only [observed, TSO64History.label, AtomicFetchAddHistory64.Projection,
        selected, ↓reduceIte] using projected
    exact .cons arithmetic (.nil _)

private theorem sequential_append {prior middle final : Word} {first last : List (Call Id)}
    (head : ModuloCounter.Sequential prior first middle)
    (tail : ModuloCounter.Sequential middle last final) :
    ModuloCounter.Sequential prior (first ++ last) final := by
  induction head with
  | nil => exact tail
  | cons arithmetic rest ih => exact .cons arithmetic (ih tail)

/-- Derive arithmetic from actual OS projection at each selected action.
Annotation IDs are kept per occurrence, never assigned by event-value lookup. -/
theorem Run.sequential {target cell} {before after : CheckedState target cell}
    {entries : List (Entry Id)} {observations : List TSO64.Observation} {events : List (Event Id)}
    (run : Run target cell before entries observations after events)
    {prior : Word} (initial : read before.state cell = .ok prior) :
    ∃ final, read after.state cell = .ok final ∧
      ModuloCounter.Sequential prior (events.filterMap Linearizability.Event.call?) final := by
  induction run generalizing prior with
  | nil => exact ⟨prior, initial, .nil _⟩
  | invoke id thread input tail ih => exact ih initial
  | @execute before middle after action mark rest observations observation head events first origin tail ih =>
    obtain ⟨value, current⟩ := middle.read_exists
    obtain ⟨final, observed, remaining⟩ := ih current
    refine ⟨final, observed, ?_⟩
    rw [List.filterMap_append]
    exact sequential_append (Emission.sequential first origin initial current) remaining

/-- Finite complete histories of this managed operational scheduler. Invocation
labels are environmental actual-prefix annotations, not ABI entry certificates.
RET is not publication or resource release. No physical/source/native refinement,
fairness, all-schedules property or frozen function credit follows. -/
theorem checked_complete {Id : Type} [DecidableEq Id] {target cell}
    {before : TSO64.State} {entries : List (Entry Id)} (valid : TSO64.WellFormed before)
    (live : before.world.cells target = some cell) {prior : Word} (initial : read before cell = .ok prior)
    (accepted : checkComplete target cell ⟨before, valid, live⟩ entries = true) :
    ∃ (result : Result Id target cell) (final : Word),
      replay target cell ⟨before, valid, live⟩ entries = some result ∧
      Run target cell ⟨before, valid, live⟩ entries result.observations result.state result.events ∧
      TSO64.schedule before (CallTrace.actions entries) = .ok (result.state.state, result.observations) ∧
      AtomicFetchAddHistory64.History before.world (result.observations.map TSO64History.label)
        result.state.state.world ∧
      read result.state.state cell = .ok final ∧
      ModuloCounter.LegalHistory prior final result.events ∧
      Linearizability.Linearization result.events (fun calls => ModuloCounter.Sequential prior calls final) ∧
      (∀ interval ∈ Linearizability.intervals result.events,
        CallTrace.EventAt (adapter Id target cell) ⟨before, valid, live⟩ entries interval.invocation
          (.invoke interval.call.id interval.call.thread interval.call.input) ∧
        CallTrace.EventAt (adapter Id target cell) ⟨before, valid, live⟩ entries interval.point (.point interval.call) ∧
        CallTrace.EventAt (adapter Id target cell) ⟨before, valid, live⟩ entries interval.response
          (.respond interval.call.id interval.call.thread interval.call.output)) ∧
      final = (Linearizability.calls result.events).foldl (fun value call => value + call.input) prior ∧
      final.toNat = (prior.toNat + ModuloCounter.inputSum (Linearizability.calls result.events)) % 2^64 := by
  obtain ⟨result, replayed, run, _, protocol⟩ := CallTrace.checkComplete_sound _ accepted
  obtain ⟨final, observed, arithmetic⟩ := Run.sequential run initial
  rw [← Linearizability.calls_eq_points] at arithmetic
  have legal : ModuloCounter.LegalHistory prior final result.events := ⟨protocol, arithmetic⟩
  have scheduled := Run.underlying run
  exact ⟨result, final, replayed, run, scheduled, TSO64History.schedule_history scheduled,
    observed, legal, legal.linearization, (fun _ member =>
      CallTrace.Run.interval_boundaries (adapter Id target cell) run protocol member),
    arithmetic.final_fold, arithmetic.total⟩

end EDSL.OS.FetchAddCalls64

#audit_edsl
