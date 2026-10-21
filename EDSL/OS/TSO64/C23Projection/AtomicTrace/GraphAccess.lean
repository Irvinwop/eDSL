/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Capture
import EDSL.OS.TSO64.C23Projection.WriteEvents
import EDSL.OS.TSO64.ExecutionViews.Model
import EDSL.OS.TSO64.StoreHistory.WriteOrder

/-!
Access to graph rows built from one actual scan. The context contains only the
execution invariants, successful scan, quiescent endpoint and structural graph
mapping. Event origins and order come from the scan certificate. Publication
origins come from the complete write list of that same actual schedule.

Incoming queues may be nonempty. A buffered instruction writer is recovered
from its actual store event, never invented for an incoming queued entry.
Initialization manifest provenance and declared interface orders remain separate
boundaries. These results establish neither graph legality nor happens-before
coherence, graph construction totality or source/native preservation.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86 PublishedHistory StoreHistory

/-- Exact event and complete publication inputs for the supplied scan result.
The manifest is supplied separately; this definition does not authenticate it. -/
def runInputs (initials : List Initials.Entry) (run : AtomicTrace.Result)
    (offset : Nat) : Inputs :=
  ⟨initials, run.events, writes offset run.observations⟩

/-- An actual scanned execution and its structural finite graph mapping.
There is no initial-empty-queue, initialization-origin or semantic graph
legality premise. Numerical sequencing and endpoint quiescence are explicit. -/
structure Executed (initial : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (run : AtomicTrace.Result) (initials : List Initials.Entry)
    (orders : Orders) (table : Table) : Prop where
  valid : WellFormed initial profile
  sequenced : Sequenced initial
  scanned : scan initial actions profile offset PublishedHistory.empty = .ok run
  quiescent : Quiescent run.state
  mapped : Built (runInputs initials run offset) orders table

/-- Forget the source annotation of a real store event, preserving its exact
original action index, complete entry, actual step and successful suffix. -/
private theorem store_issued {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset occurrence : Nat} {incoming : PublishedHistory.Writers}
    {reference : Queue.ManagedRef} {value : Word}
    (actual : EventAt profile event index initial actions result offset incoming)
    (stored : event.access = .store reference value occurrence) :
    IssuedAt profile event.tid (.managed reference value occurrence)
      index initial actions result := by
  induction actual with
  | head stepped following origin =>
      cases origin with
      | load => cases stored
      | store issued =>
          cases stored
          exact .head stepped following issued
      | rmw => cases stored
  | later stepped following actual ih => exact .later stepped following ih

namespace Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : AtomicTrace.Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Table}

theorem certificate (executed : Executed initial actions profile offset run initials orders table) :
    Certificate initial actions profile offset PublishedHistory.empty run :=
  scan_certificate executed.valid executed.sequenced executed.scanned

theorem execution (executed : Executed initial actions profile offset run initials orders table) :
    ExecutionViews.Execution initial actions run.execution profile :=
  ⟨executed.certificate.scheduled, executed.valid, executed.sequenced, executed.quiescent⟩

/-- A filtered graph event slot names an actual original scheduler action. -/
theorem event_origin (executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin run.events.length) :
    ∃ index, EventAt profile run.events[slot.val] index initial actions run.execution
      offset PublishedHistory.empty :=
  (executed.certificate.events _).mp (List.getElem_mem slot.isLt)

/-- Strict filtered event order implies strict original action order. Silent
actions and drains are still counted by both actual event positions. -/
theorem action_order (executed : Executed initial actions profile offset run initials orders table)
    (first second : Fin run.events.length) (ordered : first.val < second.val)
    {firstIndex secondIndex : Nat}
    (earlier : EventAt profile run.events[first.val] firstIndex initial actions run.execution
      offset PublishedHistory.empty)
    (later : EventAt profile run.events[second.val] secondIndex initial actions run.execution
      offset PublishedHistory.empty) : firstIndex < secondIndex := by
  have positions := List.pairwise_iff_getElem.mp executed.certificate.ordered
    first.val second.val first.isLt second.isLt ordered
  have firstPosition := earlier.position
  have secondPosition := later.position
  omega

/-- Every live table row belongs to the supplied initial manifest or to the
actual scan event list, at its exact full graph index. -/
theorem row_cases (executed : Executed initial actions profile offset run initials orders table)
    {index : Nat} {node : SourceEvent} (live : table.events[index]? = some node) :
    (∃ slot : Fin initials.length,
      index = slot.val ∧ node = initialEvent initials[slot.val]) ∨
    (∃ slot : Fin run.events.length,
      index = initials.length + slot.val ∧ node = run.events[slot.val].toSource orders) := by
  by_cases boundary : index < initials.length
  · exact .inl ⟨⟨index, boundary⟩, rfl,
      Option.some.inj (live.symm.trans (executed.mapped.initial_at ⟨index, boundary⟩))⟩
  · have bound : index < initials.length + run.events.length := by
      have within := (List.getElem_of_getElem? live).1
      simpa only [executed.mapped.events_eq, sourceEvents, runInputs,
        List.length_append, List.length_map] using within
    have eventBound : index - initials.length < run.events.length := by omega
    let slot : Fin run.events.length := ⟨index - initials.length, eventBound⟩
    have aligned : index = initials.length + slot.val := by dsimp [slot]; omega
    have selected := executed.mapped.event_at slot
    change table.events[initials.length + slot.val]? =
      some (run.events[slot.val].toSource orders) at selected
    rw [← aligned] at selected
    exact .inr ⟨slot, aligned, Option.some.inj (live.symm.trans selected)⟩

/-- A complete computed publication list supplies an actual scheduler write
witness, independently of the finite graph mapping. -/
theorem publication_origin
    (executed : Executed initial actions profile offset run initials orders table)
    {stamp : Stamp} (member : stamp ∈ writes offset run.observations) :
    Nonempty (WriteAt initial actions run.execution profile offset stamp) :=
  writes_origin executed.certificate.scheduled member

/-- The actual event supplies the instruction issue, while the full matching
publication supplies its real publication. This bridge itself needs no graph
mapping or execution invariants beyond those witnesses. In the RMW branch,
both actual position equations force the exact same original action index. -/
theorem instruction_of_publication
    (_executed : Executed initial actions profile offset run initials orders table)
    {event : Event} {index : Nat} {stamp : Stamp}
    (actual : EventAt profile event index initial actions run.execution
      offset PublishedHistory.empty)
    (published : WriteAt initial actions run.execution profile offset stamp)
    (matched : Publication event stamp) :
    Nonempty (InstructionWriteAt initial actions run.execution profile offset index stamp) := by
  cases access : event.access with
  | load reference value source => simp only [Publication, access] at matched
  | store reference value occurrence =>
      have parts : stamp.cause = .buffered event.tid reference value occurrence ∧
          event.position < stamp.position := by
        simpa only [Publication, access] using matched
      refine ⟨⟨published, ?_⟩⟩
      simpa only [parts.1] using store_issued actual access
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧
          stamp.position = event.position := by
        simpa only [Publication, access] using matched
      have aligned : index = published.index := by
        have samePosition := parts.2
        have eventPosition := actual.position
        have publicationPosition := published.position
        omega
      refine ⟨⟨published, ?_⟩⟩
      simpa only [parts.1] using aligned

/-- Every actual writing event slot has its real instruction/publication
witness and its publication-derived graph rank. Rank correspondence alone
does not provide a write origin: complete-list membership and the scan's
actual schedule provide the publication witness used here. -/
theorem write_rank (executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin run.events.length) {value : Word}
    (written : (run.events[slot.val].toSource orders).access.writeValue = some value) :
    ∃ actionIndex stamp,
      EventAt profile run.events[slot.val] actionIndex initial actions run.execution
        offset PublishedHistory.empty ∧
      Publication run.events[slot.val] stamp ∧
      Nonempty (InstructionWriteAt initial actions run.execution profile offset actionIndex stamp) ∧
      table.rank (initials.length + slot.val) = stamp.position + 1 := by
  obtain ⟨actionIndex, actual⟩ := executed.event_origin slot
  have rank := (executed.mapped.event slot).2.2
  have retained : ∃ publication : Fin (writes offset run.observations).length,
      Publication run.events[slot.val] (writes offset run.observations)[publication.val] ∧
      table.ranks[initials.length + slot.val]? =
        some ((writes offset run.observations)[publication.val].position + 1) := by
    cases access : run.events[slot.val].access with
    | load reference loaded source =>
        simp only [Event.toSource, access, Concurrency.C23Atomic.Access.writeValue,
          reduceCtorEq] at written
    | store reference stored occurrence =>
        simpa only [RankCorrespondence, runInputs, access] using rank
    | rmw changed source =>
        simpa only [RankCorrespondence, runInputs, access] using rank
  obtain ⟨publication, matched, ranked⟩ := retained
  obtain ⟨published⟩ := executed.publication_origin (List.getElem_mem publication.isLt)
  exact ⟨actionIndex, _, actual, matched,
    executed.instruction_of_publication actual published matched,
    by simp only [Concurrency.C23Atomic.Check.Table.rank, ranked, Option.getD_some]⟩

/-- A semantic read can only belong to an actual scanned event row. -/
theorem reads_event (executed : Executed initial actions profile offset run initials orders table)
    {index : Nat} {location : Atomics64.CellId64} {value : Word}
    (read : Concurrency.C23Atomic.Reads table.toCandidate index location value) :
    ∃ slot : Fin run.events.length,
      index = initials.length + slot.val ∧ run.events[slot.val].object = location ∧
      (run.events[slot.val].toSource orders).access.readValue = some value := by
  obtain ⟨node, live, object, loaded⟩ := read
  rcases executed.row_cases live with boundary | actual
  · obtain ⟨slot, _aligned, same⟩ := boundary
    rw [same] at loaded
    simp only [initialEvent, Concurrency.C23Atomic.Access.readValue, reduceCtorEq] at loaded
  · obtain ⟨slot, aligned, same⟩ := actual
    rw [same] at object loaded
    exact ⟨slot, aligned, object, loaded⟩

/-- A semantic write is either a supplied manifest row of rank zero or an
actual writing event row. The initial branch classifies supplied data only;
it does not authenticate the manifest's RAM value or registry provenance. -/
theorem writes_cases (executed : Executed initial actions profile offset run initials orders table)
    {index : Nat} {location : Atomics64.CellId64} {value : Word}
    (written : Concurrency.C23Atomic.Writes table.toCandidate index location value) :
    (∃ slot : Fin initials.length,
      index = slot.val ∧ initials[slot.val].identifier = location ∧
      initials[slot.val].value = value ∧ table.rank index = 0) ∨
    (∃ slot : Fin run.events.length,
      index = initials.length + slot.val ∧ run.events[slot.val].object = location ∧
      (run.events[slot.val].toSource orders).access.writeValue = some value) := by
  obtain ⟨node, live, object, stored⟩ := written
  rcases executed.row_cases live with boundary | actual
  · obtain ⟨slot, aligned, same⟩ := boundary
    rw [same] at object stored
    have valueEq : initials[slot.val].value = value := by
      simpa only [initialEvent, Concurrency.C23Atomic.Access.writeValue,
        Option.some.injEq] using stored
    have ranked := (executed.mapped.initial slot).2
    refine .inl ⟨slot, aligned, object, valueEq, ?_⟩
    rw [aligned]
    simp only [Concurrency.C23Atomic.Check.Table.rank, ranked, Option.getD_some]
  · obtain ⟨slot, aligned, same⟩ := actual
    rw [same] at object stored
    exact .inr ⟨slot, aligned, object, stored⟩

end Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
