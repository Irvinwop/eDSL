/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphAccess
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadTransfer

/-!
Original action clocks for every row of a structurally mapped actual scan.
Initializers have clock zero and no thread. Actual events have clock one plus
their original action position, including silent actions and drains. Both
sequencing and reads-from strictly increase this computed clock. RMW read
sides and own forwarded stores retain their exact source identities.

The execution context supplies the actual scan, complete publication list,
well-formedness, numerical sequencing and quiescent endpoint. Incoming mixed
queues may be nonempty; no instruction origin is invented for an incoming
managed entry. Interface orders remain arbitrary and initialization-manifest
provenance remains separate. These facts assume no graph legality, coherence
or happens-before property and establish no full C23, native, fairness or
graph-construction-totality claim.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86 PublishedHistory

/-- Initializers precede all actual actions. Every event clock is computed
from its actual original position, never from its publication rank. -/
def actionClock (initials : List Initials.Entry) (run : Result) (index : Nat) : Nat :=
  if index < initials.length then 0 else
    (((run.events[index - initials.length]?).map (fun event => event.position + 1)).getD 0)

private theorem writer_at_event (inputs : Inputs) (slot : Fin inputs.events.length) :
    (writerIds inputs)[inputs.initials.length + slot.val]? =
      some (inputs.events[slot.val].writer) := by
  unfold writerIds
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : inputs.initials.length + slot.val - inputs.initials.length = slot.val := by
    omega
  simp only [List.length_map, aligned, List.getElem?_map,
    List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem publication_writer {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) :
    event.writer = some (publicationKey stamp) := by
  cases access : event.access with
  | load reference value source => simp only [Publication, access] at matched
  | store reference value occurrence =>
      have parts : stamp.cause = .buffered event.tid reference value occurrence ∧
          event.position < stamp.position := by
        simpa only [Publication, access] using matched
      simp only [Event.writer, access, publicationKey, parts.1]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [Event.writer, access, publicationKey, parts.1, parts.2]

private theorem read_key_of_value {event : Event} {orders : Orders} {value : Word}
    (read : (event.toSource orders).access.readValue = some value) :
    ∃ source, ReadAccess event source := by
  cases access : event.access with
  | load target word source => exact ⟨source, .load access⟩
  | store target word occurrence =>
      simp only [Event.toSource, access, Concurrency.C23Atomic.Access.readValue] at read
      cases read
  | rmw changed source => exact ⟨source, .rmw access⟩

namespace Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Table}

/-- Every supplied manifest row has action clock zero. This is a row
classification, not authentication of the manifest's initial value. -/
theorem initial_clock
    (_executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin initials.length) : actionClock initials run slot.val = 0 := by
  simp only [actionClock, ite_eq_left slot.isLt]

/-- An actual graph row has exactly its event's original action clock. -/
theorem event_clock
    (_executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin run.events.length) :
    actionClock initials run (initials.length + slot.val) =
      run.events[slot.val].position + 1 := by
  have outside : ¬ initials.length + slot.val < initials.length := by omega
  have aligned : initials.length + slot.val - initials.length = slot.val := by omega
  simp only [actionClock, ite_eq_right outside, aligned,
    List.getElem?_eq_getElem slot.isLt, Option.map_some, Option.getD_some]

/-- A real scan witness identifies the clock with its original action index
at the supplied stream offset. -/
theorem event_action_clock
    (executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin run.events.length) {index : Nat}
    (actual : EventAt profile run.events[slot.val] index initial actions run.execution
      offset empty) :
    actionClock initials run (initials.length + slot.val) = offset + index + 1 := by
  rw [executed.event_clock slot, actual.position]

/-- A shared thread identifies actual event rows; an initializer cannot be
an endpoint because its source event has no thread. -/
theorem same_thread_events
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Nat}
    (same : Concurrency.C23Atomic.SameThread table.toCandidate first second) :
    ∃ left right : Fin run.events.length,
      first = initials.length + left.val ∧ second = initials.length + right.val ∧
      run.events[left.val].tid = run.events[right.val].tid := by
  obtain ⟨firstNode, secondNode, thread, firstLive, secondLive, firstThread, secondThread⟩ := same
  rcases executed.row_cases firstLive with boundary | actual
  · obtain ⟨_slot, _index, node⟩ := boundary
    rw [node] at firstThread
    cases firstThread
  · obtain ⟨left, leftIndex, leftNode⟩ := actual
    rcases executed.row_cases secondLive with boundary | actual
    · obtain ⟨_slot, _index, node⟩ := boundary
      rw [node] at secondThread
      cases secondThread
    · obtain ⟨right, rightIndex, rightNode⟩ := actual
      rw [leftNode] at firstThread
      rw [rightNode] at secondThread
      change some run.events[left.val].tid = some thread at firstThread
      change some run.events[right.val].tid = some thread at secondThread
      exact ⟨left, right, leftIndex, rightIndex,
        (Option.some.inj firstThread).trans (Option.some.inj secondThread).symm⟩

/-- Semantic RF selects the exact source key of an actual read side and the
same unique full graph writer row selected by structural correspondence.
Object/value agreement never supplies the writer identity. -/
theorem rf_source
    (executed : Executed initial actions profile offset run initials orders table)
    {reader writer : Nat}
    (edge : Concurrency.C23Atomic.ReadsFrom table.toCandidate reader writer) :
    ∃ (slot : Fin run.events.length) (index : Nat) (source : WriterId),
      reader = initials.length + slot.val ∧
      EventAt profile run.events[slot.val] index initial actions run.execution offset empty ∧
      ReadAccess run.events[slot.val] source ∧
      WriterAt (runInputs initials run offset) source writer := by
  obtain ⟨_location, _value, read, _written⟩ := edge.2
  obtain ⟨slot, aligned, _object, loaded⟩ := executed.reads_event read
  obtain ⟨source, access⟩ := read_key_of_value loaded
  obtain ⟨index, actual⟩ := executed.event_origin slot
  obtain ⟨selected, keyed, mappedEdge⟩ := executed.mapped.readsFrom slot access.source
  have actualEdge : Concurrency.C23Atomic.ReadsFrom table.toCandidate
      (initials.length + slot.val) writer := by
    simpa only [aligned] using edge
  have same := Concurrency.C23Atomic.readsFrom_unique actualEdge mappedEdge
  refine ⟨slot, index, source, aligned, actual, access, ?_⟩
  rw [same]
  exact keyed

/-- Every sequenced-before edge strictly increases the computed action clock,
independently of the declared interface orders. -/
theorem seq_clock_lt
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Nat}
    (before : Concurrency.C23Atomic.SeqBefore table.toCandidate first second) :
    actionClock initials run first < actionClock initials run second := by
  obtain ⟨left, right, leftIndex, rightIndex, _sameThread⟩ :=
    executed.same_thread_events before.2
  obtain ⟨firstAction, firstActual⟩ := executed.event_origin left
  obtain ⟨secondAction, secondActual⟩ := executed.event_origin right
  have ordered := executed.action_order left right (by have indices := before.1; omega)
    firstActual secondActual
  rw [leftIndex, rightIndex, executed.event_clock left, executed.event_clock right]
  have firstPosition := firstActual.position
  have secondPosition := secondActual.position
  omega

/-- Every semantic reads-from edge strictly increases the actual action clock.
This covers initial sources, forwarded own stores and actual RMW read sides.
A real writer row supplies both its actual instruction and complete matching
publication; exact keys then permit the operational read-order theorem. -/
theorem rf_clock_lt
    (executed : Executed initial actions profile offset run initials orders table)
    {reader writer : Nat}
    (edge : Concurrency.C23Atomic.ReadsFrom table.toCandidate reader writer) :
    actionClock initials run writer < actionClock initials run reader := by
  obtain ⟨readSlot, readIndex, source, readerIndex, actualRead, readAccess, selected⟩ :=
    executed.rf_source edge
  obtain ⟨_location, _value, _read, written⟩ := edge.2
  rcases executed.writes_cases written with boundary | actual
  · obtain ⟨slot, aligned, _object, _valueEq, _rank⟩ := boundary
    rw [aligned, executed.initial_clock slot, readerIndex, executed.event_clock readSlot]
    exact Nat.zero_lt_succ _
  · obtain ⟨writeSlot, writerIndex, _object, stored⟩ := actual
    obtain ⟨writeIndex, stamp, actualWrite, matched, ⟨instruction⟩, _rank⟩ :=
      executed.write_rank writeSlot stored
    have selectedAt : WriterAt (runInputs initials run offset) source
        (initials.length + writeSlot.val) := by
      simpa only [writerIndex] using selected
    have keyAt := writer_at_event (runInputs initials run offset) writeSlot
    change (writerIds (runInputs initials run offset))[initials.length + writeSlot.val]? =
      some run.events[writeSlot.val].writer at keyAt
    rw [selectedAt.1, publication_writer matched] at keyAt
    have readFrom : source = publicationKey stamp :=
      Option.some.inj (Option.some.inj keyAt)
    have ordered := actualRead.read_write_order executed.execution readAccess instruction readFrom
    rw [writerIndex, readerIndex, executed.event_clock writeSlot, executed.event_clock readSlot]
    have writePosition := actualWrite.position
    have readPosition := actualRead.position
    omega

end Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
