/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadRanks

/-!
Connect actual source-writer ranks to a finite graph's selected writer rows.
The graph's publication list must be the complete list from the same execution.
`Built` supplies identity-based mapping, not semantic legality or execution
origins for arbitrary supplied events. Each access below retains its own actual
execution origin independently of that finite mapping.

A load's own row still has rank zero. The rank equated with its prestate view
belongs to the actual writer row selected by reads-from. Graph construction
totality and universal operational C23 preservation remain separate obligations.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86 PublishedHistory

private theorem writer_at_event (inputs : Graph.Inputs) (index : Fin inputs.events.length) :
    (Graph.writerIds inputs)[inputs.initials.length + index.val]? =
      some (inputs.events[index.val].writer) := by
  unfold Graph.writerIds
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : inputs.initials.length + index.val - inputs.initials.length = index.val := by
    omega
  simp only [List.length_map, aligned, List.getElem?_map,
    List.getElem?_eq_getElem index.isLt, Option.map_some]

private theorem publication_writer {event : Event} {stamp : Stamp}
    (matched : Graph.Publication event stamp) :
    event.writer = some (Graph.publicationKey stamp) := by
  cases access : event.access with
  | load reference value source => simp only [Graph.Publication, access] at matched
  | store reference value occurrence =>
      have parts : stamp.cause = .buffered event.tid reference value occurrence ∧
          event.position < stamp.position := by
        simpa only [Graph.Publication, access] using matched
      simp only [Event.writer, access, Graph.publicationKey, parts.1]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Graph.Publication, access] using matched
      simp only [Event.writer, access, Graph.publicationKey, parts.1, parts.2]

/-- A real writer's rank is the rank of the graph row carrying its exact key.
Every publication must occur in the graph inputs. No desired table rank,
legality premise or equality of stored words selects the row. -/
theorem Graph.Built.writer_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset rank index : Nat}
    {target : Atomics64.CellId64} {key : WriterId}
    {inputs : Graph.Inputs} {orders : Orders} {table : Graph.Table}
    (mapped : Graph.Built inputs orders table)
    (complete : inputs.writes = writes offset result.2)
    (selected : Graph.WriterAt inputs key index)
    (actual : WriterRank initial actions result profile offset target key rank) :
    table.ranks[index]? = some rank := by
  cases actual with
  | initial =>
      by_cases boundary : index < inputs.initials.length
      · exact (mapped.initial ⟨index, boundary⟩).2
      · have bound := (List.getElem_of_getElem? selected.1).1
        have eventBound : index - inputs.initials.length < inputs.events.length := by
          simp only [Graph.writerIds, List.length_append, List.length_map] at bound
          omega
        let eventSlot : Fin inputs.events.length := ⟨index - inputs.initials.length, eventBound⟩
        have aligned : inputs.initials.length + eventSlot.val = index := by dsimp [eventSlot]; omega
        have eventWriter := writer_at_event inputs eventSlot
        rw [aligned, selected.1] at eventWriter
        have impossible : inputs.events[eventSlot.val].writer = some (.initial target) :=
          (Option.some.inj eventWriter).symm
        cases access : inputs.events[eventSlot.val].access <;>
          simp only [Event.writer, access, Option.some.injEq] at impossible <;>
          cases impossible
  | @publication stamp witness _cell =>
      have member : stamp ∈ inputs.writes := by
        rw [complete]
        exact writeAt_mem_writes witness
      obtain ⟨publicationIndex, atStamp⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨publicationBound, stampEq⟩ := List.getElem_of_getElem? atStamp
      let publication : Fin inputs.writes.length := ⟨publicationIndex, publicationBound⟩
      obtain ⟨eventIndex, matched, ranked⟩ := mapped.publication publication
      have actualStamp : inputs.writes[publication.val] = stamp := stampEq
      rw [actualStamp] at matched ranked
      have keyAt := writer_at_event inputs eventIndex
      rw [publication_writer matched] at keyAt
      have inKeys : inputs.initials.length + eventIndex.val < (Graph.writerIds inputs).length := by
        simp only [Graph.writerIds, List.length_append, List.length_map]
        omega
      have same := selected.2 ⟨inputs.initials.length + eventIndex.val, inKeys⟩ keyAt
      rw [← same]
      exact ranked

/-- The actual load view equals the rank of the writer selected by the finite
graph's semantic RF edge. This says nothing about the load's own rank-zero row.
The original action index and the filtered graph event index stay explicit. -/
theorem EventAt.load_graph_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId} {inputs : Graph.Inputs} {orders : Orders}
    {table : Graph.Table}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (loaded : event.access = .load target value source)
    (mapped : Graph.Built inputs orders table)
    (complete : inputs.writes = writes offset result.2)
    (graphIndex : Fin inputs.events.length) (atGraph : inputs.events[graphIndex.val] = event) :
    ∃ writer : table.Index,
      Concurrency.C23Atomic.ReadsFrom table.toCandidate
        (inputs.initials.length + graphIndex.val) writer.val ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid
        target offset empty (table.rank writer.val)) := by
  obtain ⟨rank, view, ranked⟩ := actual.load_view_rank execution loaded
  have requested : inputs.events[graphIndex.val].source = some source := by
    simp only [atGraph, Event.source, loaded]
  obtain ⟨writer, selected, edge⟩ := mapped.readsFrom graphIndex requested
  have stored := mapped.writer_rank complete selected ranked
  have same : table.rank writer.val = rank := by
    simp only [Concurrency.C23Atomic.Check.Table.rank, stored, Option.getD_some]
  exact ⟨writer, edge, by simpa only [same] using view⟩

/-- A checked event lookup supplies its graph bound automatically. This form
lets clients use computed list slots without constructing dependent indices. -/
theorem EventAt.load_graph_rank_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId} {inputs : Graph.Inputs} {orders : Orders}
    {table : Graph.Table}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (loaded : event.access = .load target value source)
    (mapped : Graph.Built inputs orders table)
    (complete : inputs.writes = writes offset result.2)
    (graphIndex : Nat) (atGraph : inputs.events[graphIndex]? = some event) :
    ∃ writer : table.Index,
      Concurrency.C23Atomic.ReadsFrom table.toCandidate
        (inputs.initials.length + graphIndex) writer.val ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid
        target offset empty (table.rank writer.val)) := by
  obtain ⟨bound, selected⟩ := List.getElem_of_getElem? atGraph
  exact actual.load_graph_rank execution loaded mapped complete ⟨graphIndex, bound⟩ selected

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
