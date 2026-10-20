/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddABI64
import EDSL.Concurrency.Linearizability.Batch
import EDSL.X86.VCGen.AtomicMethods

set_option warningAsError true

/-!
Actual-schedule annotations and proof-side closed batches for the managed
full64 fetch-add family. Each context is used once and its list index names its
call occurrence. No Protocol or desired poststate is an admission premise.
This module introduces no machine transition or arithmetic semantics.
-/

namespace EDSL.OS.FetchAddBatch64
open X86 Concurrency TSO64 X86.VCGen.AtomicMethods

abbrev Entry := FetchAddCalls64.Entry Nat
abbrev Event := FetchAddCalls64.Event Nat
abbrev Call := FetchAddCalls64.Call Nat

/-- Deterministic labels of the actual checked successor and observation.
Every selected RMW is a point, including zero updates. RET labels use actual
post-context RAX, never an expected return supplied by a caller. -/
def label {target cell} (result : FetchAddCalls64.CheckedState target cell × Observation) :
    FetchAddCalls64.Mark Nat × List Event :=
  match FetchAddCalls64.targetEvent target result.2 with
  | some (tid, event) => (.rmw tid, [.point (FetchAddCalls64.call tid tid event)])
  | none =>
    match FetchAddCalls64.returnValue (result.1.state, result.2) with
    | some (tid, value) => (.response tid tid value, [.respond tid tid value])
    | none => (.quiet, [])

/-- Label selection satisfies the existing executable emitter. This is a
property of its actual input, not an inverse assumption about Origin. -/
theorem label_emitted {target cell} (before : FetchAddCalls64.CheckedState target cell)
    (action : Action) (result : FetchAddCalls64.CheckedState target cell × Observation) :
    FetchAddCalls64.emit before action result (label result).1 = some (label result).2 := by
  cases selected : FetchAddCalls64.targetEvent target result.2 with
  | some pair =>
    rcases pair with ⟨tid, event⟩
    simp only [label, selected, FetchAddCalls64.emit, Option.map_some]
  | none =>
    cases returned : FetchAddCalls64.returnValue (result.1.state, result.2) with
    | none => simp [label, selected, returned, FetchAddCalls64.emit]
    | some pair =>
      rcases pair with ⟨tid, value⟩
      simp [label, selected, returned, FetchAddCalls64.emit]

theorem label_admitted {target cell} (image : FetchAddABI64.Image)
    (before : FetchAddCalls64.CheckedState target cell)
    (result : FetchAddCalls64.CheckedState target cell × Observation) :
    CallTrace.Invocations.admitEvents (FetchAddABI64.gate image) before (label result).2 = true := by
  cases selected : FetchAddCalls64.targetEvent target result.2 with
  | some pair =>
    rcases pair with ⟨tid, event⟩
    simp only [label, selected]
    rfl
  | none =>
    simp only [label, selected]
    cases FetchAddCalls64.returnValue (result.1.state, result.2) with
    | none => rfl
    | some pair => rcases pair with ⟨tid, value⟩; rfl

/-- Exact selected-point projection. Occurrences retain order and multiplicity;
there is no event-value lookup used as an occurrence identifier. -/
def selectedCall (target : Atomics64.CellId64) (observation : Observation) : Option Call :=
  (FetchAddCalls64.targetEvent target observation).map fun (tid, event) =>
    FetchAddCalls64.call tid tid event

theorem label_points {target cell}
    (result : FetchAddCalls64.CheckedState target cell × Observation) :
    (label result).2.filterMap Linearizability.Event.call? = (selectedCall target result.2).toList := by
  cases selected : FetchAddCalls64.targetEvent target result.2 with
  | some pair =>
    rcases pair with ⟨tid, event⟩
    simp only [label, selectedCall, selected]
    rfl
  | none =>
    simp only [label, selected, selectedCall, Option.map_none, Option.toList_none]
    cases FetchAddCalls64.returnValue (result.1.state, result.2) with
    | none => rfl
    | some pair => rcases pair with ⟨tid, value⟩; rfl

private theorem lifted_step {target cell} {before : FetchAddCalls64.CheckedState target cell}
    {action : Action} {result : TSO64.State × Observation}
    (success : TSO64.step before.state action = .ok result) :
    ∃ after : FetchAddCalls64.CheckedState target cell,
      FetchAddCalls64.step before action = .ok (after, result.2) ∧ after.state = result.1 := by
  unfold FetchAddCalls64.step
  split
  next fault failed => rw [success] at failed; cases failed
  next actual equality =>
    have same := Except.ok.inj (equality.symm.trans success)
    cases same
    exact ⟨_, rfl, rfl⟩

/-- The generated execution annotations retain their selected label function,
not only a client Origin. This supports completeness of per-occurrence labels. -/
inductive Generated {target cell} :
    FetchAddCalls64.CheckedState target cell → List Action → List Entry → List Observation →
    FetchAddCalls64.CheckedState target cell → List Event → Prop where
  | nil {state} : Generated state [] [] [] state []
  | cons {before middle after action actions observation observations entries events}
      (step : FetchAddCalls64.step before action = .ok (middle, observation))
      (tail : Generated middle actions entries observations after events) :
      Generated before (action :: actions) (.execute action (label (middle, observation)).1 :: entries)
        (observation :: observations) after ((label (middle, observation)).2 ++ events)

/-- Annotations of one supplied actual schedule. The executable gated Run
retains its actual emit equalities. This record does not assert a complete
call protocol: that additionally needs a closed, completed admitted cohort. -/
structure Annotation {target cell} (image : FetchAddABI64.Image)
    (before : FetchAddCalls64.CheckedState target cell) (actions : List Action)
    (actual : TSO64.State × List Observation) where
  entries : List Entry
  result : FetchAddCalls64.Result Nat target cell
  actions_eq : CallTrace.actions entries = actions
  state_eq : result.state.state = actual.1
  observations_eq : result.observations = actual.2
  run : FetchAddABI64.Run image target cell before entries result.observations result.state result.events
  generated : Generated before actions entries result.observations result.state result.events
  points : result.events.filterMap Linearizability.Event.call? = actual.2.filterMap (selectedCall target)

/-- Every successful operational schedule has executable ABI-adapter
annotations with exactly the same actions, observations and final state.
No complete-label checker or protocol premise appears. -/
theorem schedule_annotation {target cell} (image : FetchAddABI64.Image)
    {before : FetchAddCalls64.CheckedState target cell} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual) :
    Nonempty (Annotation image before actions actual) := by
  induction actions generalizing before actual with
  | nil =>
    have same := Except.ok.inj success
    subst actual
    exact ⟨⟨[], ⟨before, [], []⟩, rfl, rfl, rfl, .nil, .nil, rfl⟩⟩
  | cons action actions ih =>
    obtain ⟨head, tail, first, following, same⟩ := TSO64.schedule_cons_ok success
    obtain ⟨middle, stepped, middle_eq⟩ := lifted_step first
    have remaining : TSO64.schedule middle.state actions = .ok tail := by
      rw [middle_eq]
      exact following
    obtain ⟨suffix⟩ := ih remaining
    let output : FetchAddCalls64.Result Nat target cell :=
      ⟨suffix.result.state, head.2 :: suffix.result.observations,
        (label (middle, head.2)).2 ++ suffix.result.events⟩
    refine ⟨⟨.execute action (label (middle, head.2)).1 :: suffix.entries, output,
      ?_, ?_, ?_, ?_, .cons stepped suffix.generated, ?_⟩⟩
    · change action :: CallTrace.actions suffix.entries = action :: actions
      rw [suffix.actions_eq]
    · rw [same]
      exact suffix.state_eq
    · rw [same]
      exact congrArg (List.cons head.2) suffix.observations_eq
    · exact .cons (.execute stepped (label_emitted before action (middle, head.2))
        (FetchAddCalls64.emit_sound stepped (label_emitted before action (middle, head.2)))
        (label_admitted image before (middle, head.2))) suffix.run
    · change ((label (middle, head.2)).2 ++ suffix.result.events).filterMap _ = _
      rw [List.filterMap_append, label_points, suffix.points, same]
      cases present : selectedCall target head.2 <;> simp [present]

theorem Annotation.replayed {target cell} {image : FetchAddABI64.Image}
    {before : FetchAddCalls64.CheckedState target cell} {actions : List Action}
    {actual : TSO64.State × List Observation} (annotation : Annotation image before actions actual) :
    FetchAddABI64.replay image target cell before annotation.entries = some annotation.result :=
  CallTrace.Invocations.Run.replay _ _ annotation.run

/-- Invoke annotations are environmental boundaries at the current state.
Prepending them advances no CPU and changes no scheduler observation. -/
def invocations (ids : List Nat) (input : Nat → Word) : List Entry :=
  ids.map fun tid => .invoke tid tid (input tid)

def invocationEvents (ids : List Nat) (input : Nat → Word) : List Event :=
  ids.map fun tid => .invoke tid tid (input tid)

theorem prepend_invocations {target cell} {image : FetchAddABI64.Image}
    {before after : FetchAddCalls64.CheckedState target cell} {entries : List Entry}
    {observations : List Observation} {events : List Event}
    (run : FetchAddABI64.Run image target cell before entries observations after events)
    (ids : List Nat) (input : Nat → Word)
    (admitted : ∀ tid ∈ ids, FetchAddABI64.gate image before tid tid (input tid) = true) :
    FetchAddABI64.Run image target cell before (invocations ids input ++ entries)
      observations after (invocationEvents ids input ++ events) := by
  induction ids with
  | nil => exact run
  | cons tid rest ih =>
    have first := admitted tid (by simp)
    have tail := ih (fun id member => admitted id (by simp [member]))
    exact .cons (.invoke tid tid (input tid) first) tail

/-- Proof-facing description of an admitted member of the shared method
family. A registry adapter must independently derive these facts from its
present ABI/resources; this is not itself an independent corpus registration. -/
structure Member (image : FetchAddABI64.Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell) where
  method : Method
  padding : List Padding
  base : method.base = image.base
  bytes : method.bytes = image.bytes
  source : method.locked.source = .rax
  input : method.input = .rsi
  object : method.cell = cell
  target : method.handle.cell = target

/-- One invocation per initial context, with no untracked context that could
write the selected cell. All fields describe current state, entry and resource
facts; none assumes future success, returned values or Protocol acceptance. -/
structure Pre {image : FetchAddABI64.Image} {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (members : List (Member image target cell))
    (before : FetchAddCalls64.CheckedState target cell) : Prop where
  length : before.state.workers.length = members.length
  current : ∀ i : Fin members.length, Current members[i].method before.state
  entry : ∀ i : Fin members.length, ∃ worker,
    before.state.workers[i.val]? = some worker ∧
      At members[i].method (.preamble 0 members[i].padding) worker
  abi : ∀ i : Fin members.length,
    FetchAddABI64.gate image before i.val i.val (members[i].method.entry .rsi) = true

/-- Existing body soundness applies simultaneously to every admitted context
in every successful completed interleaving, with actual old-value RAX, original
full RSI input, one own selected RMW and its exact real schedule origin. -/
theorem Pre.member_completed {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    (i : Fin members.length) {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual) {final : Worker}
    (live : actual.1.workers[i.val]? = some final) (returned : final.phase = .returned) :
    ∃ event, BodyPost members[i].method final event ∧
      final.context.registers .rax = event.arithmetic.event.before ∧
      event.arithmetic.delta = members[i].method.entry .rsi ∧ event.cell = target ∧
      actual.2.filterMap (ownEvent i.val) = [event] ∧
      RMWOrigin members[i].method i.val before.state actions actual event ∧
      ownIssues i.val actions = members[i].padding.length + 3 := by
  obtain ⟨initial, initialLive, initialAt⟩ := pre.entry i
  obtain ⟨_, event, post, unique, origin, count, _⟩ :=
    all_completed_origin (pre.current i) initialLive initialAt success live returned
  refine ⟨event, post, ?_, ?_, ?_, unique, origin, count⟩
  · rw [← members[i].source]
    exact post.response
  · rw [← members[i].input]
    exact post.correct.input
  · exact post.correct.cell.trans members[i].target

/-- Bounded own progress under arbitrary successful interleavings. This is
not fairness and is not an assumption that an announced schedule succeeds. -/
theorem Pre.member_progress {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    (i : Fin members.length) {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (enough : members[i].padding.length + 3 ≤ ownIssues i.val actions) :
    ∃ final, actual.1.workers[i.val]? = some final ∧ final.phase = .returned ∧ final.pending = [] := by
  obtain ⟨initial, initialLive, initialAt⟩ := pre.entry i
  exact enough_own_issues (pre.current i) initialLive initialAt success enough

/-- Events already observed at this per-context method cutpoint. The phase
component records a real RET once, independently of the RMW's value. -/
def returnedEvents (tid : Nat) (worker : Worker) : List Event :=
  if worker.phase = .returned then [.respond tid tid (worker.context.registers .rax)] else []

def pointEvents (tid : Nat) (events : List Atomics64.FetchAddEvent) : List Event :=
  events.map fun event => .point (FetchAddCalls64.call tid tid event)

def lifecycle (tid : Nat) (point : Point) (worker : Worker) : List Event :=
  pointEvents tid point.events ++ returnedEvents tid worker

def forId (events : List Event) (tid : Nat) : List Event :=
  events.filter fun event => decide (event.id = tid)

private theorem installed_worker {state : TSO64.State} {tid : Nat} {prior replacement after : Worker}
    {world : World} (live : state.workers[tid]? = some prior)
    (found : (TSO64.install state tid world replacement).workers[tid]? = some after) :
    after = replacement :=
  Option.some.inj (found.symm.trans (List.getElem?_set_self (List.getElem_of_getElem? live).1))

private theorem issue_labels {target cell} {before : FetchAddCalls64.CheckedState target cell}
    {after : FetchAddCalls64.CheckedState target cell} {tid : Nat} {af : Bool}
    {initial final : Worker} {observation : Observation}
    (live : before.state.workers[tid]? = some initial)
    (finalLive : after.state.workers[tid]? = some final)
    (success : TSO64.step before.state (.issue tid af) = .ok (after.state, observation))
    (selected : ∀ event, ownEvent tid observation = some event → event.cell = target) :
    forId (label (after, observation)).2 tid =
      pointEvents tid (ownEvent tid observation).toList ++ returnedEvents tid final := by
  unfold label
  generalize after.state = actualState at finalLive success ⊢
  cases TSO64.step_origin success with
  | ordinary originLive running code caller fetched effect =>
    have same := Option.some.inj (originLive.symm.trans live)
    subst initial
    cases effect with
    | intro supported bounds decoded reads queue stepped finish =>
      cases finish with
      | next =>
        have finalEq := installed_worker originLive finalLive
        subst final
        simp [FetchAddCalls64.targetEvent, FetchAddCalls64.returnValue,
          ownEvent, forId, pointEvents, returnedEvents, running]
      | returned =>
        have finalEq := installed_worker originLive finalLive
        subst final
        simp [FetchAddCalls64.targetEvent, FetchAddCalls64.returnValue,
          ownEvent, forId, pointEvents, returnedEvents, TSO64.install, (List.getElem_of_getElem? originLive).1,
          Linearizability.Event.id]
  | blocked originLive running code caller fetched bounds nonempty =>
    have initialEq := Option.some.inj (originLive.symm.trans live)
    have finalEq := Option.some.inj (finalLive.symm.trans originLive)
    subst initial
    subst final
    simp [FetchAddCalls64.targetEvent, FetchAddCalls64.returnValue,
      ownEvent, forId, pointEvents, returnedEvents, running]
  | @rmw tid af issuing instruction identifier output machine originLive running code caller fetched bounds empty grant effect =>
    have finalEq := installed_worker originLive finalLive
    subst final
    have targetEq := selected output.2 (by simp [ownEvent])
    simp [FetchAddCalls64.targetEvent, targetEq, ownEvent, forId,
      pointEvents, returnedEvents, running, FetchAddCalls64.call, Linearizability.Event.id]

private theorem peer_labels {target cell} {before : FetchAddCalls64.CheckedState target cell}
    {after : FetchAddCalls64.CheckedState target cell} {action : Action} {observation : Observation}
    {tid : Nat} (different : tid ≠ (match action with | .issue thread _ | .drain thread => thread))
    (success : TSO64.step before.state action = .ok (after.state, observation)) :
    forId (label (after, observation)).2 tid = [] := by
  unfold label
  generalize after.state = actualState at success ⊢
  cases TSO64.step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish =>
      cases finish with
      | next => rfl
      | returned =>
        simp [FetchAddCalls64.targetEvent, FetchAddCalls64.returnValue, TSO64.install,
          (List.getElem_of_getElem? live).1, forId, Linearizability.Event.id, Ne.symm different]
  | blocked => rfl
  | @rmw thread af worker instruction identifier output machine live running code caller fetched bounds empty grant effect =>
    by_cases selected : output.2.cell = target
    · simp [FetchAddCalls64.targetEvent, selected, forId, FetchAddCalls64.call,
        Linearizability.Event.id, Ne.symm different]
    · simp only [FetchAddCalls64.targetEvent, selected, ite_false, FetchAddCalls64.returnValue]
      rfl
  | drained => rfl

private theorem point_selected {method : Method} {point : Point} {worker : Worker}
    (located : At method point worker) (target : method.handle.cell = selected)
    {event : Atomics64.FetchAddEvent} (member : event ∈ point.events) : event.cell = selected := by
  cases point with
  | preamble _ _ | rmw _ => cases member
  | ret offset actual =>
    have same : event = actual := List.mem_singleton.mp member
    subst event
    exact located.2.2.2.2.2.2.cell.trans target
  | done actual =>
    have same : event = actual := List.mem_singleton.mp member
    subst event
    exact located.2.2.2.2.2.cell.trans target

/-- Every real successful step advances the method's exact point/RET label
projection. The target and response are obtained from that step, not guessed
from a future complete history. -/
theorem lifecycle_step {target cell} {before : FetchAddCalls64.CheckedState target cell}
    {after : FetchAddCalls64.CheckedState target cell} {method : Method} {tid : Nat}
    {point : Point} {worker : Worker} (current : Current method before.state)
    (live : before.state.workers[tid]? = some worker) (located : At method point worker)
    (targetEq : method.handle.cell = target) {action : Action} {observation : Observation}
    (success : FetchAddCalls64.step before action = .ok (after, observation)) :
    ∃ next final, after.state.workers[tid]? = some final ∧ At method next final ∧
      lifecycle tid point worker ++ forId (label (after, observation)).2 tid = lifecycle tid next final := by
  have actual := FetchAddCalls64.step_underlying success
  cases action with
  | issue thread af =>
    by_cases same : thread = tid
    · subst thread
      obtain ⟨next, final, finalLive, finalAt, _, events, _⟩ :=
        step_preserves current live located actual
      have selected : ∀ event, ownEvent tid observation = some event → event.cell = target := by
        intro event observed
        have member : event ∈ next.events := by
          rw [← events, observed]
          simp
        exact point_selected finalAt targetEq member
      have projected := issue_labels live finalLive actual selected
      obtain ⟨issuing, issuingLive, running, _⟩ := TSO64.issue_effect actual
      have workerEq := Option.some.inj (issuingLive.symm.trans live)
      subst issuing
      have quiet : returnedEvents tid worker = [] := by simp [returnedEvents, running]
      refine ⟨next, final, finalLive, finalAt, ?_⟩
      simp only [lifecycle, quiet, List.append_nil, projected]
      rw [← List.append_assoc]
      simpa only [pointEvents, List.map_append] using
        congrArg (fun list => pointEvents tid list ++ returnedEvents tid final) events
    · have different : tid ≠ thread := Ne.symm same
      have finalLive := (TSO64.step_peer actual different).trans live
      exact ⟨point, worker, finalLive, located, by
        rw [peer_labels different actual, List.append_nil]⟩
  | drain thread =>
    by_cases same : thread = tid
    · subst thread
      simp [TSO64.step, TSO64.drain, live, located.2.1] at actual
    · have different : tid ≠ thread := Ne.symm same
      have finalLive := (TSO64.step_peer actual different).trans live
      exact ⟨point, worker, finalLive, located, by
        rw [peer_labels different actual, List.append_nil]⟩
theorem Generated.lifecycle_projection {target cell} {before after : FetchAddCalls64.CheckedState target cell}
    {actions : List Action} {entries : List Entry} {observations : List Observation} {events : List Event}
    (generated : Generated before actions entries observations after events)
    {method : Method} {tid : Nat} {point : Point} {initial : Worker}
    (current : Current method before.state) (live : before.state.workers[tid]? = some initial)
    (located : At method point initial) (targetEq : method.handle.cell = target) :
    ∃ finalPoint final, after.state.workers[tid]? = some final ∧ At method finalPoint final ∧
      lifecycle tid point initial ++ forId events tid = lifecycle tid finalPoint final := by
  induction generated generalizing point initial with
  | nil => exact ⟨point, initial, live, located, by simp [forId]⟩
  | @cons before middle after action actions observation observations entries events first tail ih =>
    obtain ⟨next, middleWorker, middleLive, middleAt, head⟩ :=
      lifecycle_step current live located targetEq first
    obtain ⟨finalPoint, final, finalLive, finalAt, rest⟩ :=
      ih (current.step (FetchAddCalls64.step_underlying first)) middleLive middleAt
    refine ⟨finalPoint, final, finalLive, finalAt, ?_⟩
    rw [forId, List.filter_append, ← List.append_assoc]
    change (lifecycle tid point initial ++ forId (label (middle, observation)).2 tid) ++
      forId events tid = _
    rw [head]
    exact rest
/-- The generated execution labels for an admitted completed context are
exactly its point and real RET response, in that order. -/
theorem Pre.generated_member {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before after : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    {actions : List Action} {entries : List Entry} {observations : List Observation} {events : List Event}
    (generated : Generated before actions entries observations after events)
    (i : Fin members.length) {final : Worker} (finalLive : after.state.workers[i.val]? = some final)
    (returned : final.phase = .returned) :
    ∃ event, forId events i.val =
      [.point (FetchAddCalls64.call i.val i.val event),
        .respond i.val i.val event.arithmetic.event.before] ∧
      event.arithmetic.delta = members[i].method.entry .rsi ∧ event.cell = target ∧
      final.context.registers .rax = event.arithmetic.event.before ∧
      BodyPost members[i].method final event := by
  obtain ⟨initial, initialLive, initialAt⟩ := pre.entry i
  obtain ⟨point, actualFinal, actualLive, located, labels⟩ :=
    generated.lifecycle_projection (pre.current i) initialLive initialAt members[i].target
  have finalEq := Option.some.inj (actualLive.symm.trans finalLive)
  subst actualFinal
  obtain ⟨event, rfl⟩ := located.returned_done returned
  have post := located.done_post
  have response : final.context.registers .rax = event.arithmetic.event.before := by
    rw [← members[i].source]
    exact post.response
  refine ⟨event, ?_, ?_, post.correct.cell.trans members[i].target, response, post⟩
  · have initialRunning := initialAt.2.2.1
    simpa [lifecycle, Point.events, pointEvents, returnedEvents, initialRunning, returned, response] using labels
  · rw [← members[i].input]
    exact post.correct.input
private theorem step_length {before after : TSO64.State} {action : Action} {observation : Observation}
    (success : TSO64.step before action = .ok (after, observation)) :
    after.workers.length = before.workers.length := by
  cases TSO64.step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish =>
      cases finish <;> simp [TSO64.install]
  | blocked => rfl
  | rmw => simp [TSO64.install]
  | drained => simp [TSO64.install]

private theorem label_closed {target cell} {before after : FetchAddCalls64.CheckedState target cell}
    {action : Action} {observation : Observation}
    (success : FetchAddCalls64.step before action = .ok (after, observation))
    {event : Event} (member : event ∈ (label (after, observation)).2) :
    event.id < before.state.workers.length := by
  have actual := FetchAddCalls64.step_underlying success
  unfold label at member
  generalize after.state = actualState at actual member
  cases TSO64.step_origin actual with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish =>
      cases finish with
      | next => cases member
      | returned =>
        simp only [FetchAddCalls64.targetEvent, FetchAddCalls64.returnValue] at member
        simp [TSO64.install, (List.getElem_of_getElem? live).1] at member
        subst event
        exact (List.getElem_of_getElem? live).1
  | blocked => cases member
  | @rmw thread af worker instruction identifier output machine live running code caller fetched bounds empty grant effect =>
    by_cases selected : output.2.cell = target
    · simp only [FetchAddCalls64.targetEvent, selected, ite_true] at member
      have same := List.mem_singleton.mp member
      subst event
      exact (List.getElem_of_getElem? live).1
    · simp [FetchAddCalls64.targetEvent, selected, FetchAddCalls64.returnValue] at member
  | drained => cases member

theorem Generated.closed {target cell} {before after : FetchAddCalls64.CheckedState target cell}
    {actions : List Action} {entries : List Entry} {observations : List Observation} {events : List Event}
    (generated : Generated before actions entries observations after events) :
    ∀ event ∈ events, event.id < before.state.workers.length := by
  induction generated with
  | nil => simp
  | @cons before middle after action actions observation observations entries events first tail ih =>
    intro event member
    rcases List.mem_append.mp member with head | rest
    · exact label_closed first head
    · rw [← step_length (FetchAddCalls64.step_underlying first)]
      exact ih event rest
/-- External full64 input and actual final context result. Outside the covered
cohort these total lookups return zero; covered indices always have real values. -/
def delta {image target cell} (members : List (Member image target cell)) (tid : Nat) : Word :=
  ((members[tid]?).map fun member => member.method.entry .rsi).getD 0

def response (state : TSO64.State) (tid : Nat) : Word :=
  ((state.workers[tid]?).map fun worker => worker.context.registers .rax).getD 0

def cohortCall {image target cell} (members : List (Member image target cell))
    (state : TSO64.State) (tid : Nat) : Call :=
  ⟨tid, tid, delta members tid, response state tid⟩

def cohort {image target cell} (members : List (Member image target cell))
    (state : TSO64.State) : List Call :=
  (List.range members.length).map (cohortCall members state)

private theorem delta_at {image target cell} (members : List (Member image target cell))
    (i : Fin members.length) : delta members i.val = members[i].method.entry .rsi := by
  simp only [delta, List.getElem?_eq_getElem i.isLt, Option.map_some, Option.getD_some, Fin.getElem_fin]

private theorem unique_filter {ids : List Nat} {tid : Nat}
    (distinct : ids.Nodup) (present : tid ∈ ids) :
    ids.filter (fun id => decide (id = tid)) = [tid] := by
  induction ids with
  | nil => cases present
  | cons head rest ih =>
    obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
    by_cases same : head = tid
    · subst head
      have empty : rest.filter (fun id => decide (id = tid)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro id member equality
        have same := of_decide_eq_true equality
        subst id
        exact absent member
      simp [empty]
    · have inTail : tid ∈ rest := by simpa only [List.mem_cons, Ne.symm same, false_or] using present
      simp [same, ih tailDistinct inTail]

private theorem invocation_projection (ids : List Nat) (input : Nat → Word) (tid : Nat)
    (distinct : ids.Nodup) (present : tid ∈ ids) :
    forId (invocationEvents ids input) tid = [.invoke tid tid (input tid)] := by
  unfold forId invocationEvents
  rw [List.filter_map]
  change (ids.filter (fun id => decide (id = tid))).map _ = _
  rw [unique_filter distinct present]
  rfl

private theorem actions_invocations (ids : List Nat) (input : Nat → Word) (entries : List Entry) :
    CallTrace.actions (invocations ids input ++ entries) = CallTrace.actions entries := by
  induction ids with
  | nil => rfl
  | cons head rest ih => exact ih

/-- Exact complete-batch labels derived from actual scheduling and method
invariants, without assuming Protocol or checkComplete acceptance. -/
theorem Pre.annotated_completed {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) :
    ∃ entries : List Entry, ∃ result : FetchAddCalls64.Result Nat target cell,
      CallTrace.actions entries = actions ∧ result.state.state = actual.1 ∧
      result.observations = actual.2 ∧
      FetchAddABI64.replay image target cell before entries = some result ∧
      result.events.filterMap Linearizability.Event.call? = actual.2.filterMap (selectedCall target) ∧
      (∀ event ∈ result.events, ∃ call ∈ cohort members actual.1, call.id = event.id) ∧
      (∀ call ∈ cohort members actual.1, forId result.events call.id =
        [.invoke call.id call.thread call.input, .point call, .respond call.id call.thread call.output]) := by
  obtain ⟨execution⟩ := schedule_annotation image success
  let ids := List.range members.length
  let entries := invocations ids (delta members) ++ execution.entries
  let result : FetchAddCalls64.Result Nat target cell :=
    ⟨execution.result.state, execution.result.observations,
      invocationEvents ids (delta members) ++ execution.result.events⟩
  have gates : ∀ tid ∈ ids, FetchAddABI64.gate image before tid tid (delta members tid) = true := by
    intro tid member
    have bound := List.mem_range.mp member
    have admitted := pre.abi ⟨tid, bound⟩
    rw [delta_at members ⟨tid, bound⟩]
    exact admitted
  have run := prepend_invocations execution.run ids (delta members) gates
  have replayed := CallTrace.Invocations.Run.replay _ _ run
  refine ⟨entries, result, ?_, execution.state_eq, execution.observations_eq, replayed, ?_, ?_, ?_⟩
  · rw [actions_invocations]
    exact execution.actions_eq
  · change (invocationEvents ids (delta members) ++ execution.result.events).filterMap _ = _
    rw [List.filterMap_append]
    have noPoints : (invocationEvents ids (delta members)).filterMap Linearizability.Event.call? = [] := by
      induction ids with
      | nil => rfl
      | cons head rest ih => exact ih
    rw [noPoints, List.nil_append]
    exact execution.points
  · intro event member
    have bound : event.id < members.length := by
      rcases List.mem_append.mp member with invoke | execute
      · obtain ⟨tid, inIds, same⟩ := List.mem_map.mp invoke
        subst event
        exact List.mem_range.mp inIds
      · have covered := execution.generated.closed event execute
        rwa [pre.length] at covered
    exact ⟨cohortCall members actual.1 event.id,
      List.mem_map.mpr ⟨event.id, List.mem_range.mpr bound, rfl⟩, rfl⟩
  · intro call member
    obtain ⟨tid, inIds, same⟩ := List.mem_map.mp member
    subst call
    have bound := List.mem_range.mp inIds
    obtain ⟨initial, initialLive, initialAt⟩ := pre.entry ⟨tid, bound⟩
    obtain ⟨_, _, final, finalLive, finalAt, _, _, _⟩ :=
      schedule_preserves (pre.current ⟨tid, bound⟩) initialLive initialAt success
    have returned := done final (List.mem_of_getElem? finalLive)
    have finalLiveChecked : execution.result.state.state.workers[tid]? = some final := by
      rw [execution.state_eq]
      exact finalLive
    obtain ⟨event, projected, input, _, responseValue, _⟩ :=
      pre.generated_member execution.generated ⟨tid, bound⟩ finalLiveChecked returned
    have callEq : FetchAddCalls64.call tid tid event = cohortCall members actual.1 tid := by
      simp only [FetchAddCalls64.call, cohortCall, delta_at members ⟨tid, bound⟩,
        response, finalLive, Option.map_some, Option.getD_some, input, responseValue]
    change forId (invocationEvents ids (delta members) ++ execution.result.events) tid = _
    unfold forId
    rw [List.filter_append]
    change forId (invocationEvents ids (delta members)) tid ++ forId execution.result.events tid = _
    rw [invocation_projection ids (delta members) tid (List.nodup_range (n := members.length)) inIds, projected]
    change _ = ([.invoke tid tid (delta members tid), .point (cohortCall members actual.1 tid),
      .respond tid tid (response actual.1 tid)] : List Event)
    rw [callEq]
    simp [response, finalLive, responseValue]
/-- Every completed admitted closed batch has a real independent complete
counter history. Acceptance is derived from machine/body invariants, rather
than an admission oracle. This is not a native/published-TSO refinement. -/
theorem Pre.complete {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual)
    (done : TSO64.Returned actual.1) {prior : Word}
    (initial : FetchAddCalls64.read before.state cell = .ok prior) :
    ∃ entries : List Entry, ∃ result : FetchAddCalls64.Result Nat target cell, ∃ final : Word,
      CallTrace.actions entries = actions ∧ result.state.state = actual.1 ∧
      result.observations = actual.2 ∧
      FetchAddABI64.Complete image before entries prior result final ∧
      result.events.filterMap Linearizability.Event.call? = actual.2.filterMap (selectedCall target) ∧
      (Linearizability.calls result.events).Perm (cohort members actual.1) := by
  obtain ⟨entries, result, erased, sameState, sameObservations, replayed, points, closed, triples⟩ :=
    pre.annotated_completed success done
  have ids : ((cohort members actual.1).map Linearizability.Call.id).Nodup := by
    simpa only [cohort, List.map_map, Function.comp_def, cohortCall, List.map_id'] using
      List.nodup_range (n := members.length)
  have threads : ((cohort members actual.1).map Linearizability.Call.thread).Nodup := by
    simpa only [cohort, List.map_map, Function.comp_def, cohortCall, List.map_id'] using
      List.nodup_range (n := members.length)
  have projections : ∀ call ∈ cohort members actual.1,
      Linearizability.Batch.projection result.events call.id = Linearizability.Batch.events call := by
    simpa only [forId, Linearizability.Batch.projection, Linearizability.Batch.events] using triples
  have protocol := Linearizability.Batch.protocol ids threads closed projections
  have accepted : FetchAddABI64.checkComplete image before entries = true := by
    unfold FetchAddABI64.checkComplete
    rw [replayed]
    exact decide_eq_true protocol
  obtain ⟨checked, final, complete⟩ := FetchAddABI64.checked_complete initial accepted
  have sameResult := Option.some.inj (complete.replayed.symm.trans replayed)
  subst checked
  exact ⟨entries, result, final, erased, sameState, sameObservations, complete, points,
    Linearizability.Batch.calls_perm ids threads closed projections⟩
/-- Real completion retains current authority and enables read-only collection.
Clear DF follows the actual nonarithmetic flag frame and admitted SysV entry. -/
theorem Pre.member_returned {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    (i : Fin members.length) {actions : List Action} {actual : TSO64.State × List Observation}
    (success : TSO64.schedule before.state actions = .ok actual) {final : Worker}
    (live : actual.1.workers[i.val]? = some final) (returned : final.phase = .returned) :
    ∃ event, BodyPost members[i].method final event ∧
      Current members[i].method actual.1 ∧ final.context.flags.getLsbD 10 = false ∧
      TSO64.collect actual.1 i.val = .ok event.arithmetic.event.before := by
  obtain ⟨initial, initialLive, initialAt⟩ := pre.entry i
  obtain ⟨current, event, post, _, _, _, flags⟩ :=
    all_completed_origin (pre.current i) initialLive initialAt success live returned
  obtain ⟨admitted, admittedLive, facts⟩ := FetchAddABI64.gate_sound (pre.abi i)
  have same := Option.some.inj (admittedLive.symm.trans initialLive)
  subst admitted
  have mask : (~~~arithmeticFlagMask).getLsbD 10 = true := by decide +kernel
  have direction := congrArg (fun value : Word => value.getLsbD 10) flags
  simp only [BitVec.getLsbD_and, mask, Bool.and_true] at direction
  have response : final.context.registers .rax = event.arithmetic.event.before := by
    rw [← members[i].source]
    exact post.response
  have collected : TSO64.collect actual.1 i.val = .ok (final.context.registers .rax) := by
    simp [TSO64.collect, live, post.phase, post.empty]
  exact ⟨event, post, current, direction.trans facts.abi.2,
    collected.trans (congrArg Except.ok response)⟩
/-- A bounded completing own-only suffix exists for every present member and
all AF choices. Interleaved whole-batch fairness remains a separate question. -/
theorem Pre.member_completion {image : FetchAddABI64.Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {members : List (Member image target cell)}
    {before : FetchAddCalls64.CheckedState target cell} (pre : Pre members before)
    (i : Fin members.length) (choices : Nat → Bool) :
    ∃ actions actual final event,
      actions.length = members[i].padding.length + 3 ∧
      (∀ action ∈ actions, ∃ af, action = .issue i.val af) ∧
      TSO64.schedule before.state actions = .ok actual ∧ actual.1.workers[i.val]? = some final ∧
      BodyPost members[i].method final event := by
  obtain ⟨initial, live, located⟩ := pre.entry i
  obtain ⟨actions, actual, final, event, count, own, success, found, done⟩ :=
    X86.VCGen.AtomicMethods.complete (pre.current i) live located choices
  exact ⟨actions, actual, final, event, count, own, success, found, done.done_post⟩
end EDSL.OS.FetchAddBatch64

#audit_edsl
