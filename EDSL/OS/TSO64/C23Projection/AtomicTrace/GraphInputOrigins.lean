/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphPublicationEvents
import EDSL.OS.TSO64.C23Projection.AtomicTrace.WriterRanks
import EDSL.OS.TSO64.StoreHistory.PendingPublication
import EDSL.OS.TSO64.WordProjection.Locations

/-!
Writer identities and exact read values before graph construction. Persistent
store counters identify actual issues; original action positions identify RMWs.
Published reads retain their actual latest modification word, while forwarded
reads retain the exact tagged queue entry and its future actual publication.
Initial reads retain the real initialized registry descriptor and RAM word.

The construction boundary has empty initial queues and a quiescent final state.
Initial store counters may be nonzero, and scan offsets and interface orders
are arbitrary. No graph table, builder result, legality or classification
oracle supplies these facts. This is a finite modeled-execution result, with
no native, runtime, full C23, fairness or corpus claim.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86 PublishedHistory StoreHistory

/-- The exact word of a source identity, authenticated by initial RAM or a
complete actual publication. A rank alone cannot construct this predicate. -/
inductive WriterValueOrigin (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset : Nat)
    (target : Atomics64.CellId64) : WriterId → Word → Prop where
  | initial {cell : Atomics64.Cell} {value : Word}
      (registered : initial.world.cells target = some cell)
      (loaded : loadQWord (published initial.world) cell.address = .ok value) :
      WriterValueOrigin initial actions result profile offset target (.initial target) value
  | publication {stamp : Stamp}
      (actual : WriteAt initial actions result profile offset stamp)
      (cell : stamp.cause.cell = target) :
      WriterValueOrigin initial actions result profile offset target
        (Graph.publicationKey stamp) stamp.cause.value

/-- Resolve a real prefix RAM read using the last actual managed modification,
or the actual initial RAM read when the prefix has no modification of the cell.
The offset includes all actions, including silent actions and other cells. -/
theorem publishedSource_prefix_value {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {cut offset : Nat}
    {target : Atomics64.CellId64} {cell : Atomics64.Cell} {value : Word}
    (valid : WellFormed initial profile)
    (success : schedule initial actions profile = .ok result)
    (prefixRun : schedule initial (actions.take cut) profile =
      .ok (before, result.2.take cut))
    (registered : before.world.cells target = some cell)
    (loaded : loadQWord (published before.world) cell.address = .ok value) :
    WriterValueOrigin initial actions result profile offset target
      (publishedSource (after offset (result.2.take cut) empty) target) value := by
  have initialCell : initial.world.cells target = some cell :=
    (congrFun (ScheduleTrace.cells prefixRun) target).symm.trans registered
  obtain ⟨boundary, initialRead⟩ := (valid.1.cells target cell initialCell).2.1.load_exists
  rcases published_read_origin (offset := offset) valid prefixRun target cell
      initialCell boundary value initialRead loaded with boundarySource | modified
  · obtain ⟨absent, sameValue⟩ := boundarySource
    have origin : WriterValueOrigin initial actions result profile offset target
        (.initial target) value :=
      .initial initialCell (by simpa only [published, sameValue] using initialRead)
    simpa only [publishedSource, absent] using origin
  · obtain ⟨stamp, latest, sameValue, actual, sameCell, _noLater⟩ := modified
    obtain ⟨full⟩ := actual.lift_prefix success
    have selected : publishedSource (after offset (result.2.take cut) empty) target =
        Graph.publicationKey stamp := by
      simp only [publishedSource, latest, Graph.publicationKey]
      cases stamp.cause <;> rfl
    rw [selected]
    simpa only [sameValue] using (WriterValueOrigin.publication full sameCell)

/-- A forwarded word comes from the exact selected managed entry. Final
quiescence forces that entry's actual future publication; physical aliasing is
resolved by current cell authority, independently of the stored bits. -/
theorem LoadSource.value_origin {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {cut tid offset : Nat} {worker : Worker} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (prefixRun : schedule initial (actions.take cut) profile =
      .ok (before, result.2.take cut))
    (live : before.workers[tid]? = some worker)
    (current : Queue.Current before.world worker.resources target)
    (read : LoadSource before worker tid target value
      (after offset (result.2.take cut) empty) source) :
    WriterValueOrigin initial actions result profile offset target.handle.cell source value := by
  cases read with
  | published _absent loaded =>
      exact publishedSource_prefix_value (offset := offset)
        execution.valid execution.success prefixRun current.cell loaded
  | forwarded selector writer occurrence _newest entry _payload address writerCurrent _below =>
      have sameCell := WordProjection.address_injective
        (schedule_wellFormed execution.valid prefixRun).1 writerCurrent.cell current.cell address
      obtain ⟨publication⟩ := pending_managed_publication execution.success execution.sequenced
        prefixRun execution.quiescent ⟨worker, live, List.mem_of_getElem? entry⟩
      obtain ⟨actual⟩ := publication.writeAt offset
      simpa only [PendingPublication.stamp, Graph.publicationKey, WriteCause.value]
        using (WriterValueOrigin.publication actual sameCell)

private theorem rmw_input_value {state : State} {action : Action}
    {first : State × Observation} {profile : Profile} {tid : Nat}
    {changed : Atomics64.FetchAddEvent}
    (origin : EDSL.OS.TSO64.Origin state action first profile)
    (observed : first.2 = .rmw tid changed) :
    ∃ cell, state.world.cells changed.cell = some cell ∧
      loadQWord (published state.world) cell.address = .ok changed.arithmetic.event.before := by
  cases origin with
  | ordinary _live _running _code _caller _fetched effect =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish =>
          cases finish <;> cases observed
  | blocked => cases observed
  | rmw _live _running _code _caller _fetched _bounds _empty _grant effect =>
      cases observed
      obtain ⟨handle, cell, _found, _actor, linked, _valid, identity, address⟩ :=
        Atomics64.fetchAdd_context _ _ _ _ _ effect.checked
      refine ⟨cell, ?_, ?_⟩
      · simpa only [identity] using linked
      · have loaded := Atomics64.fetchAdd_old _ _ _ _ _ effect.checked
        simpa only [published, address] using loaded
  | drained => cases observed

/-- Both actual read forms retain the selected source identity and the exact
loaded word. Stores have no read side. Source existence is established before
choosing any source-graph index or interface order. -/
theorem EventAt.read_value_origin {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {key : WriterId} {value : Word} {orders : Orders}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (requested : event.source = some key)
    (loaded : (event.toSource orders).access.readValue = some value) :
    WriterValueOrigin initial actions result profile offset event.object key value := by
  obtain ⟨before, action, first, prefixRun, _actionAt, _observed, _stepped, access⟩ :=
    actual.prestate
  cases access with
  | @load tid worker reference word source origin live read =>
      have sameSource : source = key := Option.some.inj requested
      have sameValue : word = value := Option.some.inj loaded
      cases origin with
      | intro _issuing originLive _fetched _effect _shared _ordinaryAbsent _selected
          current _operand _read =>
          have workers := Option.some.inj (originLive.symm.trans live)
          rw [workers] at current
          simpa only [Event.object, sameSource, sameValue] using
            (read.value_origin execution prefixRun live current)
  | store => cases requested
  | @rmw tid changed observed origin =>
      have sameSource : publishedSource (after offset (result.2.take index) empty)
          changed.cell = key := Option.some.inj requested
      have sameValue : changed.arithmetic.event.before = value := Option.some.inj loaded
      obtain ⟨cell, registered, read⟩ := rmw_input_value origin observed
      simpa only [Event.object, sameSource, sameValue] using
        (publishedSource_prefix_value (offset := offset)
          execution.valid execution.success prefixRun registered read)

namespace Graph

/-- Equal nonempty writer keys force equal actual instruction positions.
The store branch uses the production nextStore increment, without assuming
that any worker's initial occurrence counter starts at zero. -/
private theorem actual_writer_position {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {first second : Event}
    {firstIndex secondIndex offset : Nat} {incoming : Writers}
    (left : EventAt profile first firstIndex initial actions result offset incoming)
    (right : EventAt profile second secondIndex initial actions result offset incoming)
    (same : first.writer = second.writer) (writing : first.writer.isSome = true) :
    first.position = second.position := by
  cases firstAccess : first.access with
  | load reference value source => simp [Event.writer, firstAccess] at writing
  | store firstReference firstValue firstOccurrence =>
      cases secondAccess : second.access with
      | load reference value source => simp [Event.writer, firstAccess, secondAccess] at same
      | rmw changed source => simp [Event.writer, firstAccess, secondAccess] at same
      | store secondReference secondValue secondOccurrence =>
          have identity : WriterId.store first.tid firstOccurrence =
              .store second.tid secondOccurrence :=
            Option.some.inj (by simpa only [Event.writer, firstAccess, secondAccess] using same)
          obtain ⟨threadEq, occurrenceEq⟩ := WriterId.store.inj identity
          have firstIssue := store_issued_at left firstAccess
          have secondIssue := store_issued_at right secondAccess
          rw [← threadEq, ← occurrenceEq] at secondIssue
          have indices := firstIssue.occurrence_index_unique secondIssue
          rw [left.position, right.position, indices]
  | rmw changed source =>
      cases secondAccess : second.access with
      | load reference value source => simp [Event.writer, firstAccess, secondAccess] at same
      | store reference value occurrence => simp [Event.writer, firstAccess, secondAccess] at same
      | rmw changed source =>
          have identity : WriterId.rmw first.position = .rmw second.position :=
            Option.some.inj (by simpa only [Event.writer, firstAccess, secondAccess] using same)
          exact WriterId.rmw.inj identity

private theorem input_key_index {keys : List (Option WriterId)}
    (unique : (keys.filterMap id).Nodup) {key : WriterId} {firstIndex secondIndex : Nat}
    (first : keys[firstIndex]? = some (some key))
    (second : keys[secondIndex]? = some (some key)) : firstIndex = secondIndex := by
  obtain ⟨firstBound, firstValue⟩ := List.getElem_of_getElem? first
  obtain ⟨secondBound, secondValue⟩ := List.getElem_of_getElem? second
  have separated : keys.Pairwise (fun a b =>
      ∀ x, a = some x → ∀ y, b = some y → x ≠ y) :=
    List.pairwise_filterMap.mp unique
  by_cases before : firstIndex < secondIndex
  · have different := List.Pairwise.rel_getElem_of_lt firstBound secondBound
      separated before key firstValue key secondValue
    exact False.elim (different rfl)
  · by_cases after : secondIndex < firstIndex
    · have different := List.Pairwise.rel_getElem_of_lt secondBound firstBound
        separated after key secondValue key firstValue
      exact False.elim (different rfl)
    · omega

private theorem input_initial_writer (inputs : Inputs) (slot : Fin inputs.initials.length) :
    (writerIds inputs)[slot.val]? =
      some (some (.initial inputs.initials[slot.val].identifier)) := by
  unfold writerIds
  rw [List.getElem?_append_left (by simpa only [List.length_map] using slot.isLt)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem input_event_writer (inputs : Inputs) (slot : Fin inputs.events.length) :
    (writerIds inputs)[inputs.initials.length + slot.val]? =
      some (inputs.events[slot.val].writer) := by
  unfold writerIds
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : inputs.initials.length + slot.val - inputs.initials.length = slot.val := by omega
  simp only [List.length_map, aligned, List.getElem?_map,
    List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem input_initial_source (inputs : Inputs) (orders : Orders)
    (slot : Fin inputs.initials.length) :
    (sourceEvents inputs orders)[slot.val]? = some (initialEvent inputs.initials[slot.val]) := by
  unfold sourceEvents
  rw [List.getElem?_append_left (by simpa only [List.length_map] using slot.isLt)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem input_event_source (inputs : Inputs) (orders : Orders)
    (slot : Fin inputs.events.length) :
    (sourceEvents inputs orders)[inputs.initials.length + slot.val]? =
      some (inputs.events[slot.val].toSource orders) := by
  unfold sourceEvents
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : inputs.initials.length + slot.val - inputs.initials.length = slot.val := by omega
  simp only [List.length_map, aligned, List.getElem?_map,
    List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem initial_writer_witness {inputs : Inputs} (orders : Orders)
    (keys : ((writerIds inputs).filterMap id).Nodup) (slot : Fin inputs.initials.length) :
    ∃ writer : Fin (sourceEvents inputs orders).length,
      WriterAt inputs (.initial inputs.initials[slot.val].identifier) writer.val ∧
      (sourceEvents inputs orders)[writer.val].object = inputs.initials[slot.val].identifier ∧
      (sourceEvents inputs orders)[writer.val].access.writeValue =
        some inputs.initials[slot.val].value := by
  obtain ⟨bound, node⟩ := List.getElem_of_getElem? (input_initial_source inputs orders slot)
  have selected := input_initial_writer inputs slot
  refine ⟨⟨slot.val, bound⟩, ⟨selected, ?_⟩, ?_, ?_⟩
  · intro other chosen
    exact input_key_index keys chosen selected
  · rw [node]
    rfl
  · rw [node]
    rfl

private theorem event_writer_witness {inputs : Inputs} {orders : Orders}
    {key : WriterId} {target : Atomics64.CellId64} {value : Word}
    (keys : ((writerIds inputs).filterMap id).Nodup) (slot : Fin inputs.events.length)
    (writing : inputs.events[slot.val].writer = some key)
    (object : inputs.events[slot.val].object = target)
    (stored : (inputs.events[slot.val].toSource orders).access.writeValue = some value) :
    ∃ writer : Fin (sourceEvents inputs orders).length,
      WriterAt inputs key writer.val ∧
      (sourceEvents inputs orders)[writer.val].object = target ∧
      (sourceEvents inputs orders)[writer.val].access.writeValue = some value := by
  obtain ⟨bound, node⟩ := List.getElem_of_getElem? (input_event_source inputs orders slot)
  have selected := input_event_writer inputs slot
  rw [writing] at selected
  refine ⟨⟨inputs.initials.length + slot.val, bound⟩, ⟨selected, ?_⟩, ?_, ?_⟩
  · intro other chosen
    exact input_key_index keys chosen selected
  · rw [node]
    exact object
  · rw [node]
    exact stored

private theorem publication_values {event : Event} {stamp : Stamp} (orders : Orders)
    (matched : Publication event stamp) :
    event.writer = some (publicationKey stamp) ∧ event.object = stamp.cause.cell ∧
      (event.toSource orders).access.writeValue = some stamp.cause.value := by
  cases access : event.access with
  | load reference value source => simp only [Publication, access] at matched
  | store reference value occurrence =>
      have parts : stamp.cause = .buffered event.tid reference value occurrence ∧
          event.position < stamp.position := by
        simpa only [Publication, access] using matched
      simp only [Event.writer, Event.object, Event.toSource, access, parts.1,
        publicationKey, WriteCause.cell, WriteCause.value,
        Concurrency.C23Atomic.Access.writeValue, and_self]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [Event.writer, Event.object, Event.toSource, access, parts.1, parts.2,
        publicationKey, WriteCause.cell, WriteCause.value,
        Concurrency.C23Atomic.Access.writeValue, and_self]

namespace Captured
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}

/-- Raw scan writers are unique, including duplicate payloads and nonzero
initial issue counters. Initial identities are disjoint from both instruction
writer constructors and come from the actual complete manifest enumeration. -/
theorem writer_keys (captured : Captured initial actions profile offset run initials) :
    ((writerIds (runInputs initials run offset)).filterMap id).Nodup := by
  apply List.pairwise_filterMap.mpr
  unfold writerIds runInputs
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_map.mpr
    have distinct := List.pairwise_map.mp
      (List.nodup_iff_pairwise_ne.mp captured.manifest_unique)
    refine distinct.imp ?_
    intro first second different key selected other selectedOther same
    have identity : WriterId.initial first.identifier = .initial second.identifier :=
      (Option.some.inj selected).trans (same.trans (Option.some.inj selectedOther).symm)
    exact different (WriterId.initial.inj identity)
  · apply List.pairwise_map.mpr
    refine captured.certificate.ordered.imp_of_mem ?_
    intro first second firstMember secondMember before key selected other selectedOther same
    obtain ⟨firstIndex, left⟩ := (captured.certificate.events first).mp firstMember
    obtain ⟨secondIndex, right⟩ := (captured.certificate.events second).mp secondMember
    have keys : first.writer = second.writer :=
      selected.trans ((congrArg some same).trans selectedOther.symm)
    have writing : first.writer.isSome = true := by
      change first.writer = some key at selected
      rw [selected]
      rfl
    have positions := actual_writer_position left right keys writing
    omega
  · intro first firstMember second secondMember key selected other selectedOther same
    obtain ⟨entry, _member, equal⟩ := List.mem_map.mp firstMember
    subst first
    obtain ⟨event, _member, equal⟩ := List.mem_map.mp secondMember
    subst second
    cases selected
    cases same
    cases access : event.access <;> simp [Event.writer, access] at selectedOther

/-- Equal publication keys recover the entire actual stamp, including its
reference and word. Strict complete-write order then excludes duplicates. -/
theorem publication_keys (captured : Captured initial actions profile offset run initials) :
    ((runInputs initials run offset).writes.map publicationKey).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  refine (writes_ordered offset run.observations).imp_of_mem ?_
  intro first second firstMember secondMember before same
  obtain ⟨left⟩ := captured.publication_origin firstMember
  obtain ⟨right⟩ := captured.publication_origin secondMember
  have stamps := publicationKey_writeAt_unique captured.certificate.scheduled
    captured.sequenced left right same
  rw [stamps] at before
  exact Nat.lt_irrefl _ before

/-- Exact raw input read-source adequacy for arbitrary declared orders. The
full source-list index retains the original writer key, actual object and
actual loaded word. Equal words and equal ranks never select a writer. -/
theorem read_source (captured : Captured initial actions profile offset run initials)
    (orders : Orders) (slot : Fin (runInputs initials run offset).events.length)
    (key : WriterId) (value : Word)
    (requested : (runInputs initials run offset).events[slot.val].source = some key)
    (loaded : ((runInputs initials run offset).events[slot.val].toSource orders).access.readValue =
      some value) :
    ∃ writer : Fin (sourceEvents (runInputs initials run offset) orders).length,
      WriterAt (runInputs initials run offset) key writer.val ∧
      (sourceEvents (runInputs initials run offset) orders)[writer.val].object =
        (runInputs initials run offset).events[slot.val].object ∧
      (sourceEvents (runInputs initials run offset) orders)[writer.val].access.writeValue =
        some value := by
  obtain ⟨index, actual⟩ := captured.event_origin slot
  have origin := actual.read_value_origin (orders := orders) captured.execution requested loaded
  cases origin with
  | initial registered read =>
      have member := Initials.enumerate_complete captured.valid.1 captured.enumerated registered read
      obtain ⟨initialIndex, selected⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨bound, entry⟩ := List.getElem_of_getElem? selected
      simpa only [runInputs, entry] using
        (initial_writer_witness orders captured.writer_keys ⟨initialIndex, bound⟩)
  | @publication stamp published cell =>
      obtain ⟨event, writerIndex, writerActual, matched, _instruction⟩ :=
        captured.publication_instruction_event published
      have member := (captured.certificate.events event).mpr ⟨writerIndex, writerActual⟩
      obtain ⟨eventIndex, selected⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨bound, sameEvent⟩ := List.getElem_of_getElem? selected
      obtain ⟨writerKey, object, stored⟩ := publication_values orders matched
      refine event_writer_witness captured.writer_keys ⟨eventIndex, bound⟩ ?_ ?_ ?_
      · simpa only [runInputs, sameEvent] using writerKey
      · simpa only [runInputs, sameEvent] using object.trans cell
      · simpa only [runInputs, sameEvent] using stored

end Captured
end Graph
end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
