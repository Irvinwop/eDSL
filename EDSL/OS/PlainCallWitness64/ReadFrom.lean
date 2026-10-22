/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallWitness64.Publication
import EDSL.OS.PlainCallSafety64
import EDSL.OS.TSO64.ExecutionViews.WriteSelf
import EDSL.OS.TSO64.PublishedOrder

/-!
Actual-source consequences of a closed plain64 run with one writing slot.
Publication coverage first identifies every managed write with that slot;
actual thread/occurrence uniqueness identifies the complete stamp. The real
reader then resolves the persistent-cell writer map at its actual access.
No source identity, graph edge, scanner acceptance or equal-value lookup is
supplied by a caller. Inputs and an already constructed publication position
are facts about the original admitted run, rather than additional admission.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS OS.TSO64 OS.TSO64.C23Projection
open OS.TSO64.C23Projection.AtomicTrace OS.TSO64.PublishedHistory

private theorem load_no_publication {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (reading : input.site.kind = .loadAcquire) (stamp : Stamp) :
    ¬ Graph.Publication (outcome.machineEvent source 0) stamp := by
  cases input with
  | loadAcquire image target cell occurrence => exact id
  | storeRelease image target cell value occurrence => cases reading

private theorem store_publication_key {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (writing : input.site.kind = .storeRelease) {stamp : Stamp}
    (matched : Graph.Publication (outcome.machineEvent source 0) stamp) :
    Graph.publicationKey stamp = .store tid outcome.initial.nextStore := by
  cases input with
  | loadAcquire image target cell occurrence => cases writing
  | storeRelease image target cell value occurrence =>
      have cause : stamp.cause =
          .buffered tid outcome.reference value outcome.initial.nextStore := matched.1
      simp only [Graph.publicationKey, cause]

private theorem store_publication_cell {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (writing : input.site.kind = .storeRelease) {stamp : Stamp}
    (matched : Graph.Publication (outcome.machineEvent source 0) stamp) :
    stamp.cause.cell = input.target := by
  cases input with
  | loadAcquire image target cell occurrence => cases writing
  | storeRelease image target cell value occurrence =>
      have cause : stamp.cause =
          .buffered tid outcome.reference value outcome.initial.nextStore := matched.1
      rw [cause]
      exact outcome.target

/-- All actual managed publications belong to the single writing input. The
coverage is over the actual captured write enumeration, including every RMW;
the complete independent machine-event list excludes omitted writes. -/
theorem ClosedPost.only_store_publication {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0)
    (writer : Fin before.workers.length)
    (others : ∀ tid, tid ≠ writer → (inputs tid).site.kind = .loadAcquire)
    {stamp : Stamp} (member : stamp ∈ C23Projection.writes 0 actual.2) :
    Graph.Publication ((post.calls.outcomes writer).machineEvent (post.sources writer) 0)
      stamp := by
  have inRun : stamp ∈ C23Projection.writes 0 post.run.observations := by
    change stamp ∈ C23Projection.writes 0 post.run.execution.2
    rw [post.execution]
    exact member
  obtain ⟨publicationIndex, selected⟩ := List.mem_iff_getElem?.mp inRun
  obtain ⟨bound, same⟩ := List.getElem_of_getElem? selected
  obtain ⟨slot, matched⟩ := post.captured.publication_event ⟨publicationIndex, bound⟩
  have eventBound : slot.val < post.run.events.length := by
    change slot.val < (Graph.runInputs post.initials post.run 0).events.length
    exact slot.isLt
  have eventMember : post.run.events[slot.val] ∈ post.calls.slots.map
      (fun tid => (post.calls.outcomes tid).machineEvent (post.sources tid) 0) := by
    rw [← post.machineEvents]
    exact List.getElem_mem eventBound
  obtain ⟨tid, _present, eventEq⟩ := List.mem_map.mp eventMember
  have actualMatched : Graph.Publication
      ((post.calls.outcomes tid).machineEvent (post.sources tid) 0) stamp := by
    simpa only [Graph.runInputs, same, ← eventEq] using matched
  by_cases chosen : tid = writer
  · cases chosen
    exact actualMatched
  · exact False.elim (load_no_publication (post.calls.outcomes tid) (post.sources tid)
      (others tid chosen) stamp actualMatched)

/-- A real publication of the only writer is the unique complete actual
managed stamp, even if its word equals the initial word or another value. -/
theorem ClosedPost.only_store_stamp {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0)
    (writer : Fin before.workers.length)
    (writing : (inputs writer).site.kind = .storeRelease)
    (others : ∀ tid, tid ≠ writer → (inputs tid).site.kind = .loadAcquire)
    {stamp : Stamp} (member : stamp ∈ C23Projection.writes 0 actual.2)
    (matched : Graph.Publication
      ((post.calls.outcomes writer).machineEvent (post.sources writer) 0) stamp) :
    ∀ other ∈ C23Projection.writes 0 actual.2, other = stamp := by
  intro other otherMember
  have otherMatched := post.only_store_publication writer others otherMember
  obtain ⟨left⟩ := writes_origin post.calls.scheduled otherMember
  obtain ⟨right⟩ := writes_origin post.calls.scheduled member
  apply publicationKey_writeAt_unique post.calls.scheduled post.captured.sequenced left right
  exact (store_publication_key (post.calls.outcomes writer) (post.sources writer)
    writing otherMatched).trans
      (store_publication_key (post.calls.outcomes writer) (post.sources writer)
        writing matched).symm

/-- A unique real publication is the actual persistent-cell map selection at
every later cut. Presence comes from the production write and is transported
monotonically; any replacement would be another enumerated actual write. -/
theorem ClosedPost.unique_stamp_selected {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0) {stamp : Stamp}
    (member : stamp ∈ C23Projection.writes 0 actual.2)
    (unique : ∀ other ∈ C23Projection.writes 0 actual.2, other = stamp)
    {cut : Nat} (earlier : stamp.position < cut) :
    PublishedHistory.after 0 (actual.2.take cut) PublishedHistory.empty stamp.cause.cell =
      some stamp := by
  obtain ⟨publication⟩ := writes_origin post.calls.scheduled member
  have position : stamp.position = publication.index := by
    simpa only [Nat.zero_add] using publication.position
  have selected := publication.published_at_succ PublishedHistory.empty
  obtain ⟨latest, found, _order⟩ := PublishedOrder.prefix_order
    (PublishedOrder.prior_empty 0) (by omega : publication.index + 1 ≤ cut) selected
  obtain ⟨_middle, prefixRun, _suffixRun⟩ := ScheduleTrace.cut post.calls.scheduled cut
  obtain ⟨short, _cell, _noLater⟩ := PublishedHistory.newest_write_at prefixRun found
  obtain ⟨whole⟩ := short.lift_prefix post.calls.scheduled
  have equal := unique latest (writeAt_mem_writes whole)
  simpa only [equal] using found

/-- The observation interval after a unique real publication has no later
managed write to its persistent cell. This is derived from actual observations,
not assumed from an intended read-from edge. -/
theorem ClosedPost.no_writes_after_unique {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (_post : ClosedPost before inputs actions actual 0) {stamp : Stamp}
    (_member : stamp ∈ C23Projection.writes 0 actual.2)
    (unique : ∀ other ∈ C23Projection.writes 0 actual.2, other = stamp)
    (cut : Nat) :
    NoWrites ((actual.2.take cut).drop (stamp.position + 1)) stamp.cause.cell := by
  intro observation inside cause written _sameCell
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp inside
  have takeSelected : (actual.2.take cut)[stamp.position + 1 + index]? =
      some observation := by
    simpa only [List.getElem?_drop] using selected
  have insideCut : stamp.position + 1 + index < cut := by
    have bound := (List.getElem_of_getElem? takeSelected).1
    have length := List.length_take_le cut actual.2
    omega
  have original : actual.2[stamp.position + 1 + index]? = some observation := by
    simpa only [List.getElem?_take_of_lt insideCut] using takeSelected
  have otherMember : (⟨stamp.position + 1 + index, cause⟩ : Stamp) ∈
      C23Projection.writes 0 actual.2 :=
    (mem_writes_iff 0 actual.2 _).mpr ⟨_, observation, original, written, by simp only [Nat.zero_add]⟩
  have equal := congrArg Stamp.position (unique _ otherMember)
  change stamp.position + 1 + index = stamp.position at equal
  omega

/-- A load input has an empty real FIFO at every successful prefix of an
initially quiet admitted run. The static methods and independent prefix-safety
bridge establish this without a future cutpoint or queue-selection oracle. -/
theorem load_prefix_empty {catalog : Catalog}
    (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : ClosedPre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result)
    (reader : Fin before.workers.length)
    (reading : (inputs reader).site.kind = .loadAcquire)
    {worker : Worker} (live : result.1.workers[reader.val]? = some worker) :
    worker.pending = [] := by
  let admitted := PlainCallAdmission64.admission static pre.1 reader
  obtain ⟨current, _reference, currentLive, _resources, _valid, _descriptor, _target,
    _originalSelection, _selection, progress, _flags, _saved, _code, _caller⟩ :=
    (PlainCallSafety64.safe_prefix static pre.1 success).frames reader
      admitted.invocation.initial admitted.invocation.live
  have same : current = worker := Option.some.inj (currentLive.symm.trans live)
  obtain ⟨allocated, onlyStore, frame⟩ := progress
  have unallocated := onlyStore reading
  obtain ⟨drained, suffix⟩ := frame.suffix
  have oldEmpty := pre.2 admitted.invocation.initial
    (List.mem_of_getElem? admitted.invocation.live)
  simp only [same, unallocated, Bool.false_eq_true, ite_false, List.append_nil, oldEmpty] at suffix
  have length := congrArg List.length suffix
  have pendingLength : worker.pending.length = 0 := by
    simp only [List.length_nil, List.length_append] at length
    omega
  exact List.eq_nil_of_length_eq_zero pendingLength

private theorem load_machine_access {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (reading : input.site.kind = .loadAcquire) :
    ∃ value, (outcome.machineEvent source 0).access = .load outcome.reference value source := by
  cases input with
  | loadAcquire image target cell occurrence => exact ⟨outcome.reply, rfl⟩
  | storeRelease image target cell value occurrence => cases reading

private theorem event_load_source {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation}
    {event : AtomicTrace.Event} {index : Nat} {reference : Queue.ManagedRef}
    {value : Word} {source : WriterId}
    (origin : EventAt .sharedCell event index before actions actual 0 PublishedHistory.empty)
    (loaded : event.access = .load reference value source)
    (empty : ∀ prior worker,
      schedule before (actions.take index) .sharedCell = .ok (prior, actual.2.take index) →
      prior.workers[event.tid]? = some worker → worker.pending = []) :
    source = publishedSource
      (PublishedHistory.after 0 (actual.2.take index) PublishedHistory.empty)
      reference.handle.cell := by
  obtain ⟨prior, action, first, prefixRun, _actionAt, _observed, _stepped, access⟩ :=
    origin.prestate
  cases access with
  | @load tid worker actualReference _actualValue actualSource _origin live read =>
      have references : actualReference = reference := (Access.load.inj loaded).1
      have sources : actualSource = source := (Access.load.inj loaded).2.2
      have noPending := empty prior worker prefixRun live
      have key := read.key
      have actualKey : some (publishedSource
          (PublishedHistory.after 0 (actual.2.take index) PublishedHistory.empty)
          actualReference.handle.cell) = some actualSource := by
        simpa only [readKey, noPending, payload, Queue.payload, List.map_nil,
          StoreBuffer.Mixed.newestQWord] using key
      calc
        source = actualSource := sources.symm
        _ = publishedSource
            (PublishedHistory.after 0 (actual.2.take index) PublishedHistory.empty)
            actualReference.handle.cell := (Option.some.inj actualKey).symm
        _ = publishedSource
            (PublishedHistory.after 0 (actual.2.take index) PublishedHistory.empty)
            reference.handle.cell := by rw [references]
  | store => cases loaded
  | rmw => cases loaded

/-- A later actual load selects the sole writer's actual machine occurrence.
The stamp and its access bound may be supplied from an already constructed
run; the scanner's source is derived from the empty real FIFO and actual map. -/
theorem ClosedPost.published_load_source {catalog : Catalog}
    (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : ClosedPre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0)
    (writer reader : Fin before.workers.length)
    (writing : (inputs writer).site.kind = .storeRelease)
    (reading : (inputs reader).site.kind = .loadAcquire)
    (others : ∀ tid, tid ≠ writer → (inputs tid).site.kind = .loadAcquire)
    (sameCell : (inputs writer).target = (inputs reader).target)
    {stamp : Stamp} (member : stamp ∈ C23Projection.writes 0 actual.2)
    (matched : Graph.Publication
      ((post.calls.outcomes writer).machineEvent (post.sources writer) 0) stamp)
    (earlier : stamp.position < (post.calls.outcomes reader).performed) :
    post.sources reader = .store writer.val (post.calls.outcomes writer).initial.nextStore := by
  have actualEvent := post.outcome_event_origin reader
  obtain ⟨value, loaded⟩ := load_machine_access (post.calls.outcomes reader) (post.sources reader) reading
  have selected := post.unique_stamp_selected member
    (post.only_store_stamp writer writing others member matched) earlier
  have target : stamp.cause.cell = (post.calls.outcomes reader).reference.handle.cell :=
    (store_publication_cell (post.calls.outcomes writer) (post.sources writer) writing matched).trans
      (sameCell.trans (post.calls.outcomes reader).target.symm)
  rw [target] at selected
  have sourceToMap := event_load_source actualEvent loaded (by
    intro prior worker prefixRun live
    exact load_prefix_empty static pre prefixRun reader reading live)
  have actualSource : post.sources reader = Graph.publicationKey stamp := by
    rw [sourceToMap]
    simp only [publishedSource, selected, Graph.publicationKey]
    cases stamp.cause <;> rfl
  exact actualSource.trans
    (store_publication_key (post.calls.outcomes writer) (post.sources writer) writing matched)

private theorem store_machine_writer {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (writing : input.site.kind = .storeRelease) :
    (outcome.machineEvent source 0).writer = some (.store tid outcome.initial.nextStore) := by
  cases input with
  | loadAcquire image target cell occurrence => cases writing
  | storeRelease image target cell value occurrence => rfl

private theorem load_machine_source {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (reading : input.site.kind = .loadAcquire) :
    (outcome.machineEvent source 0).source = some source := by
  cases input with
  | loadAcquire image target cell occurrence => rfl
  | storeRelease image target cell value occurrence => cases reading

/-- Two original workers ordered by their actual accesses occupy the exact
first and second retained machine-event slots. The proof uses complete slot
coverage and strict actual access order, rather than thread numbers as rows. -/
theorem ClosedPost.slots_pair {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0)
    (population : before.workers.length = 2)
    (writer reader : Fin before.workers.length)
    (writerZero : writer.val = 0) (readerOne : reader.val = 1)
    (earlier : (post.calls.outcomes writer).performed <
      (post.calls.outcomes reader).performed) :
    post.calls.slots = [writer, reader] := by
  have different : writer ≠ reader := by
    intro same
    have values := congrArg Fin.val same
    omega
  have cover : ∀ tid : Fin before.workers.length, tid = writer ∨ tid = reader := by
    intro tid
    have bound := tid.isLt
    by_cases zero : tid.val = 0
    · exact .inl (Fin.ext (by omega))
    · exact .inr (Fin.ext (by omega))
  have slotsNodup : post.calls.slots.Nodup :=
    post.calls.permutation.symm.nodup (List.nodup_finRange _)
  have pairNodup : ([writer, reader] : List (Fin before.workers.length)).Nodup := by
    simp [different]
  have perm : post.calls.slots.Perm [writer, reader] := by
    apply (List.perm_ext_iff_of_nodup slotsNodup pairNodup).mpr
    intro tid
    constructor
    · intro _member
      rcases cover tid with same | same
      · exact List.mem_cons.mpr (.inl same)
      · exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr same))
    · intro _member
      exact post.calls.permutation.mem_iff.mpr (List.mem_finRange tid)
  have pairOrdered : ([writer, reader] : List (Fin before.workers.length)).Pairwise
      (fun left right => (post.calls.outcomes left).performed <
        (post.calls.outcomes right).performed) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro tid member
    have same := List.mem_singleton.mp member
    cases same
    exact earlier
  apply List.Perm.eq_of_pairwise
    (le := fun left right => (post.calls.outcomes left).performed <
      (post.calls.outcomes right).performed)
    (fun _left _right _leftMember _rightMember forward backward =>
      False.elim (Nat.lt_asymm forward backward))
    post.calls.ordered pairOrdered perm

/-- Exact RF rows from the actual slot list. Slot positions are plain list
facts about this Post, not graph-index or writer-source admission. All initial
manifest rows are retained, so a row is never replaced by a thread identifier. -/
theorem ClosedPost.readsFrom_published_before {catalog : Catalog}
    (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : ClosedPre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0)
    (writer reader : Fin before.workers.length)
    (writing : (inputs writer).site.kind = .storeRelease)
    (reading : (inputs reader).site.kind = .loadAcquire)
    (others : ∀ tid, tid ≠ writer → (inputs tid).site.kind = .loadAcquire)
    (sameCell : (inputs writer).target = (inputs reader).target)
    {stamp : Stamp} (member : stamp ∈ C23Projection.writes 0 actual.2)
    (matched : Graph.Publication
      ((post.calls.outcomes writer).machineEvent (post.sources writer) 0) stamp)
    (earlier : stamp.position < (post.calls.outcomes reader).performed)
    {writerIndex readerIndex : Nat}
    (writerAt : post.calls.slots[writerIndex]? = some writer)
    (readerAt : post.calls.slots[readerIndex]? = some reader) :
    Concurrency.C23Atomic.ReadsFrom post.table.toCandidate
      (post.initials.length + readerIndex) (post.initials.length + writerIndex) := by
  have source := post.published_load_source static pre writer reader writing reading
    others sameCell member matched earlier
  let key : WriterId := .store writer.val (post.calls.outcomes writer).initial.nextStore
  have writerSelected :
      (Graph.writerIds (Graph.runInputs post.initials post.run 0))[post.initials.length + writerIndex]? = some (some key) := by
    unfold Graph.writerIds Graph.runInputs
    rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
    simp only [List.length_map]
    have aligned : post.initials.length + writerIndex - post.initials.length = writerIndex := by
      omega
    rw [aligned, post.machineEvents]
    simp only [List.getElem?_map, writerAt, Option.map_some]
    exact congrArg some
      (store_machine_writer (post.calls.outcomes writer) (post.sources writer) writing)
  have readerSelected : post.run.events[readerIndex]? =
      some ((post.calls.outcomes reader).machineEvent (post.sources reader) 0) := by
    rw [post.machineEvents]
    simp only [List.getElem?_map, readerAt, Option.map_some]
  obtain ⟨readerBound, readerEvent⟩ := List.getElem_of_getElem? readerSelected
  let readerSlot : Fin (Graph.runInputs post.initials post.run 0).events.length :=
    ⟨readerIndex, readerBound⟩
  have requested : (Graph.runInputs post.initials post.run 0).events[readerSlot.val].source =
      some key := by
    change post.run.events[readerIndex].source = some key
    rw [readerEvent, load_machine_source (post.calls.outcomes reader) (post.sources reader) reading,
      source]
  obtain ⟨writerRow, selected, edge⟩ := post.correspondence.readsFrom readerSlot requested
  have writerBound := (List.getElem_of_getElem? writerSelected).1
  have rowEq : writerRow.val = post.initials.length + writerIndex :=
    (selected.2 ⟨post.initials.length + writerIndex, writerBound⟩ writerSelected).symm
  simpa only [Graph.runInputs, readerSlot, rowEq] using edge

private theorem store_publication_after {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : WriterId)
    (writing : input.site.kind = .storeRelease) {stamp : Stamp}
    (matched : Graph.Publication (outcome.machineEvent source 0) stamp) :
    outcome.performed < stamp.position := by
  cases input with
  | loadAcquire image target cell occurrence => cases writing
  | storeRelease image target cell value occurrence =>
      simpa only [Outcome.machineEvent, Nat.zero_add] using matched.2

/-- In the original writer-0/reader-1 population, publication before the load
forces the exact final graph edge from row `initials.length + 0` to the load at
row `initials.length + 1`. Both row positions are conclusions of actual order. -/
theorem ClosedPost.readsFrom_two_workers {catalog : Catalog}
    (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : ClosedPre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0)
    (population : before.workers.length = 2)
    (writer reader : Fin before.workers.length)
    (writerZero : writer.val = 0) (readerOne : reader.val = 1)
    (writing : (inputs writer).site.kind = .storeRelease)
    (reading : (inputs reader).site.kind = .loadAcquire)
    (sameCell : (inputs writer).target = (inputs reader).target)
    {stamp : Stamp} (member : stamp ∈ C23Projection.writes 0 actual.2)
    (matched : Graph.Publication
      ((post.calls.outcomes writer).machineEvent (post.sources writer) 0) stamp)
    (earlier : stamp.position < (post.calls.outcomes reader).performed) :
    Concurrency.C23Atomic.ReadsFrom post.table.toCandidate
      (post.initials.length + 1) (post.initials.length + 0) := by
  have accessOrder := Nat.lt_trans (store_publication_after (post.calls.outcomes writer)
    (post.sources writer) writing matched) earlier
  have slots := post.slots_pair population writer reader writerZero readerOne accessOrder
  have others : ∀ tid, tid ≠ writer → (inputs tid).site.kind = .loadAcquire := by
    intro tid different
    have bound := tid.isLt
    have nonzero : tid.val ≠ 0 := by
      intro zero
      exact different (Fin.ext (zero.trans writerZero.symm))
    have same : tid = reader := Fin.ext (by omega)
    simpa only [same] using reading
  exact post.readsFrom_published_before static pre writer reader writing reading
    others sameCell member matched earlier
    (by rw [slots]; rfl : post.calls.slots[0]? = some writer)
    (by rw [slots]; rfl : post.calls.slots[1]? = some reader)

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
