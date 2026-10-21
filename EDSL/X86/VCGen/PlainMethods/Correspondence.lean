/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Batch
import EDSL.X86.VCGen.PlainMethods.AtomicEvents
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

/-!
The production scanner's complete event list is the complete initial cohort's
call list, in actual access order. The proof uses both coverage directions and
original-position uniqueness; no call-list equality is an admission premise.

This adapter covers one admitted invocation per actual initial worker slot.
The writer map and incoming FIFOs retain their existing explicit boundaries.
Interface acquire/release orders remain declared annotations. Event-list
correspondence establishes neither read-from legality nor universal C23
legality, and makes no source/compiler/native preservation claim.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods.Correspondence
open OS OS.TSO64 OS.TSO64.C23Projection Concurrency

private theorem atomic_worker {state : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {position : Nat}
    {writers : PublishedHistory.Writers} {actual : AtomicTrace.Event}
    (origin : AtomicTrace.AtomicStep state action result .sharedCell position writers actual) :
    ∃ worker, state.workers[actual.tid]? = some worker := by
  cases origin with
  | load origin live source => exact ⟨_, live⟩
  | store issued =>
    cases issued with
    | ordinary issuing success live fetched effect intent admission committed => exact ⟨_, live⟩
  | rmw observed origin =>
    cases origin with
    | ordinary live running code caller fetched effect =>
      cases effect with
      | intro supported bounds decoded reads queue executed finish =>
        cases finish <;> cases observed
    | blocked => cases observed
    | drained => cases observed
    | rmw live running code caller fetched bounds empty grant effect =>
      cases observed
      exact ⟨_, live⟩

private theorem strict_nodup {α : Type} {key : α → Nat} {items : List α}
    (ordered : items.Pairwise (fun first second => key first < key second)) : items.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply ordered.imp
  intro first second earlier same
  rw [same] at earlier
  exact Nat.lt_irrefl _ earlier

private theorem strict_key_unique {α : Type} {key : α → Nat} {items : List α}
    (ordered : items.Pairwise (fun first second => key first < key second))
    {first second : α} (firstMem : first ∈ items) (secondMem : second ∈ items)
    (same : key first = key second) : first = second := by
  revert ordered firstMem secondMem same
  induction items generalizing first second with
  | nil => intro _ impossible; cases impossible
  | cons head tail ih =>
    intro ordered firstMem secondMem same
    obtain ⟨before, orderedTail⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp firstMem with rfl | firstTail
    · rcases List.mem_cons.mp secondMem with rfl | secondTail
      · rfl
      · have earlier := before second secondTail
        rw [same] at earlier
        exact False.elim (Nat.lt_irrefl _ earlier)
    · rcases List.mem_cons.mp secondMem with rfl | secondTail
      · have earlier := before first firstTail
        rw [same] at earlier
        exact False.elim (Nat.lt_irrefl _ earlier)
      · exact ih orderedTail firstTail secondTail same

private theorem strict_list_ext {α : Type} {key : α → Nat} {first second : List α}
    (firstOrdered : first.Pairwise (fun left right => key left < key right))
    (secondOrdered : second.Pairwise (fun left right => key left < key right))
    (members : ∀ item, item ∈ first ↔ item ∈ second) : first = second := by
  have perm : first.Perm second :=
    (List.perm_ext_iff_of_nodup (strict_nodup firstOrdered) (strict_nodup secondOrdered)).mpr members
  apply List.Perm.eq_of_pairwise (le := fun left right => key left < key right)
    (fun left right leftMem rightMem forward backward => ?_) firstOrdered secondOrdered perm
  exact False.elim (Nat.lt_asymm forward backward)

variable {initial : OS.TSO64.State} {actions : List Action} {run : AtomicTrace.Result}
  {invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val}
  {offset : Nat} {writers : PublishedHistory.Writers}

/-- An arbitrary scanner event belongs to its actual initial worker slot and
is exactly that completed invocation's event, including full reference, reply,
store occurrence and read-source identity. The method's decoded cutpoints
exclude unexpected own RMWs before dispatch coverage identifies the access.
Neither thread membership nor a future cutpoint is supplied by the caller. -/
theorem event_origin (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run)
    {actual : AtomicTrace.Event} (member : actual ∈ run.events) :
    ∃ (slot : Fin initial.workers.length) (source : AtomicTrace.WriterId),
      actual = AtomicEvents.event (invocations slot).method slot.val
        (offset + (batch.completed slot).performed) (batch.completed slot).reply source := by
  obtain ⟨index, atIndex⟩ := AtomicTrace.scan_sound valid sequenced success member
  obtain ⟨before, action, first, prefixRun, selected, observed, executed, origin⟩ := atIndex.prestate
  obtain ⟨issuing, issuingLive⟩ := atomic_worker origin
  have presentBound : actual.tid < before.workers.length :=
    (List.getElem_of_getElem? issuingLive).1
  have workerLength : before.workers.length = initial.workers.length := ScheduleTrace.workers_length prefixRun
  have initialBound : actual.tid < initial.workers.length := by omega
  let slot : Fin initial.workers.length := ⟨actual.tid, initialBound⟩
  let admitted := invocations slot
  obtain ⟨currentBefore, point, after, prefixEmissions, afterLive, afterAt, remaining,
    replies, prefixTrace⟩ := schedule_preserves admitted.current admitted.live admitted.entry prefixRun
  have plain := AtomicEvents.atomicStep_plain currentBefore afterLive afterAt executed origin
    (show actual.tid = slot.val from rfl)
  have own : OwnAccess slot.val before action := AtomicEvents.plain_dispatched origin plain
  have dispatched : DispatchedAt slot.val initial actions run.execution index :=
    ⟨before, action, first, prefixRun, selected, executed, own⟩
  have sameIndex : index = (batch.completed slot).performed :=
    (batch.completed slot).performed_unique dispatched
  rw [sameIndex] at atIndex
  obtain ⟨source, equal⟩ := AtomicEvents.eventAt_unique valid sequenced
    (batch.completed slot).access atIndex
  exact ⟨slot, source, equal⟩

/-- Every slot contributes its own exact event to the actual scanner, without
requiring stores to publish by RET or initial queues to be empty. -/
theorem slot_coverage (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run)
    (slot : Fin initial.workers.length) :
    ∃ source, AtomicEvents.event (invocations slot).method slot.val
      (offset + (batch.completed slot).performed) (batch.completed slot).reply source ∈ run.events :=
  AtomicEvents.scan_coverage valid sequenced success (batch.completed slot).access

/-- Whole machine-event-list equality, stronger than a membership or source
payload relation. Actual source keys are retained in the selected per-slot
writer map. Existence follows from coverage; deterministic original-position
uniqueness aligns every event, and the independently proved access orders
upgrade membership correspondence to exact list equality. -/
theorem machine_events (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run) :
    ∃ sources : Fin initial.workers.length → AtomicTrace.WriterId,
      run.events = batch.slots.map (fun slot =>
        AtomicEvents.event (invocations slot).method slot.val
          (offset + (batch.completed slot).performed) (batch.completed slot).reply (sources slot)) := by
  classical
  have coverage := slot_coverage batch valid sequenced success
  let sources : Fin initial.workers.length → AtomicTrace.WriterId :=
    fun slot => Classical.choose (coverage slot)
  let selected : Fin initial.workers.length → AtomicTrace.Event := fun slot =>
    AtomicEvents.event (invocations slot).method slot.val
      (offset + (batch.completed slot).performed) (batch.completed slot).reply (sources slot)
  have selectedMem : ∀ slot, selected slot ∈ run.events :=
    fun slot => Classical.choose_spec (coverage slot)
  have scannerOrdered := AtomicTrace.scan_events_ordered valid sequenced success
  have selectedOrdered : (batch.slots.map selected).Pairwise
      (fun first second => first.position < second.position) := by
    apply List.pairwise_map.mpr
    apply batch.slots_ordered.imp
    intro first second earlier
    change offset + (batch.completed first).performed < offset + (batch.completed second).performed
    omega
  refine ⟨sources, ?_⟩
  change run.events = batch.slots.map selected
  apply strict_list_ext scannerOrdered selectedOrdered
  intro actual
  constructor
  · intro member
    obtain ⟨slot, source, actualEq⟩ := event_origin batch valid sequenced success member
    have samePosition : actual.position = (selected slot).position := by rw [actualEq]; rfl
    have equal : actual = selected slot := strict_key_unique scannerOrdered member
      (selectedMem slot) samePosition
    exact List.mem_map.mpr ⟨slot, batch.slot_mem slot, equal.symm⟩
  · intro member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    exact selectedMem slot

private theorem call_event {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {scheduleActions : List Action} {result : OS.TSO64.State × List Observation}
    (completed : CompletedCall method tid state scheduleActions result)
    (occurrence position : Nat) (source : AtomicTrace.WriterId) :
    (AtomicEvents.event method tid position completed.reply source).toSource AtomicEvents.orders =
      (completed.call occurrence).event := by
  rw [AtomicEvents.event_toSource]
  rfl

/-- Exact call/event correspondence retains action positions as well as the
complete independent source event. Drains and blocked actions are not removed
from positions; payload equality never substitutes for a thread or source key.
The offset is the scanner's original position boundary. -/
theorem positioned_events (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run) :
    run.events.map (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) =
      batch.calls.map (fun actual => (offset + actual.performed, actual.event)) := by
  obtain ⟨sources, exactEvents⟩ := machine_events batch valid sequenced success
  rw [exactEvents, BatchResult.calls, List.map_map, List.map_map]
  apply List.map_congr_left
  intro slot member
  apply Prod.ext
  · rfl
  · exact call_event (batch.completed slot) (invocations slot).occurrence _ (sources slot)

/-- The complete production scanner list, after the explicit interface-order
annotation, equals the entire batch call list. This closes the event equality
previously required by `BatchResult.realizes`; no such equality is a premise. -/
theorem source_events (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run) :
    run.events.map (fun actual => actual.toSource AtomicEvents.orders) =
      batch.calls.map AtomicCalls.Call.event := by
  have equal := congrArg (List.map (fun located : Nat × C23Atomic.Event Atomics64.CellId64 Word =>
      located.2))
    (positioned_events batch valid sequenced success)
  simpa only [List.map_map, Function.comp_def] using equal

/-- The scanner's position list is precisely the call list's performed list,
with the declared offset. This is an order-preserving equality, not a set or
permutation statement. -/
theorem positions (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run) :
    run.events.map AtomicTrace.Event.position =
      batch.calls.map (fun actual => offset + actual.performed) := by
  have equal := congrArg (List.map (fun located : Nat × C23Atomic.Event Atomics64.CellId64 Word =>
      located.1))
    (positioned_events batch valid sequenced success)
  simpa only [List.map_map, Function.comp_def] using equal

/-- Every graph built from the actual scanner list has the complete call event
list after its initializer prefix. Publication metadata is separate and plays
no role in this structural equality. -/
theorem graph_source_events (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run)
    (initials : List AtomicTrace.Initials.Entry) (publications : List PublishedHistory.Stamp) :
    AtomicTrace.Graph.sourceEvents ⟨initials, run.events, publications⟩ AtomicEvents.orders =
      initials.map AtomicTrace.Graph.initialEvent ++ batch.calls.map AtomicCalls.Call.event := by
  unfold AtomicTrace.Graph.sourceEvents
  rw [source_events batch valid sequenced success]

/-- Structural realization now requires only the candidate's ordinary binding
to the actual scanner-derived source list. The call-list event equality is
proved by the adapter. No graph verifier, RF fact or Legal premise is used.
Initializer events still retain their independent initialization contract. -/
theorem realizes (batch : BatchResult initial actions run.execution invocations)
    (valid : WellFormed initial .sharedCell) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions .sharedCell offset writers = .ok run)
    {initials : List (C23Atomic.Event Atomics64.CellId64 Word)}
    {candidate : C23Atomic.Candidate Atomics64.CellId64 Word}
    (events : candidate.events =
      initials ++ run.events.map (fun actual => actual.toSource AtomicEvents.orders))
    (initialized : ∀ actual ∈ initials, actual.thread = none ∧
      ∃ value, actual.access = .initialize value) :
    AtomicCalls.Realizes initials batch.calls candidate := by
  apply batch.realizes
  · rw [events, source_events batch valid sequenced success]
  · exact initialized

end EDSL.X86.VCGen.PlainMethods.Correspondence

#audit_edsl
