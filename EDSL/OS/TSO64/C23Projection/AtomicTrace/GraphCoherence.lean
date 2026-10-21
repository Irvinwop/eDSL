/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.OrderCoherence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphAccess
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadAccess
import EDSL.OS.TSO64.C23Projection.AtomicTrace.RMWPredecessor

/-!
Program-order coherence of all rows in a structurally mapped actual scan.
RMWs participate in both read and write roles. Original action positions supply
operational order, while graph rows include initializers and every atomic access.
The incoming publication map is empty and final queues are quiescent; incoming
sequenced queues may be nonempty when the complete graph mapping admits them.

These constraints do not infer source memory orders, establish synchronization
or its happens-before closure, prove graph-construction totality, or refine
physical CPU/Linux behavior. Initial-manifest provenance remains separate from
structural correspondence. No legality-check success is a premise.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86 PublishedHistory

private theorem read_key_of_value {event : Event} {orders : Orders} {value : Word}
    (read : (event.toSource orders).access.readValue = some value) :
    ∃ source, ReadAccess event source := by
  cases access : event.access with
  | load target word source => exact ⟨source, .load access⟩
  | store target word occurrence =>
      simp only [Event.toSource, access, Concurrency.C23Atomic.Access.readValue] at read
      cases read
  | rmw changed source => exact ⟨source, .rmw access⟩

private theorem read_key_requested {event : Event} {source : WriterId}
    (read : ReadAccess event source) : event.source = some source := by
  cases read with
  | load access => simp only [Event.source, access]
  | rmw access => simp only [Event.source, access]

private theorem publication_tid {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) : stamp.cause.tid = event.tid := by
  cases access : event.access with
  | load target value source => simp only [Publication, access] at matched
  | store target value occurrence =>
      have parts : stamp.cause = .buffered event.tid target value occurrence ∧
          event.position < stamp.position := by simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.tid]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.tid]

private theorem publication_cell {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) : stamp.cause.cell = event.object := by
  cases access : event.access with
  | load target value source => simp only [Publication, access] at matched
  | store target value occurrence =>
      have parts : stamp.cause = .buffered event.tid target value occurrence ∧
          event.position < stamp.position := by simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.cell, Event.object, access]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.cell, Event.object, access]

private theorem same_thread_rows {initial : State} {actions : List Action}
    {profile : Profile} {offset : Nat} {run : Result} {initials : List Initials.Entry}
    {orders : Orders} {table : Table} {first second : Nat}
    (executed : Executed initial actions profile offset run initials orders table)
    (same : Concurrency.C23Atomic.SameThread table.toCandidate first second) :
    ∃ left right : Fin run.events.length,
      first = initials.length + left.val ∧ second = initials.length + right.val ∧
      run.events[left.val].tid = run.events[right.val].tid := by
  obtain ⟨firstNode, secondNode, thread, firstLive, secondLive, firstThread, secondThread⟩ := same
  rcases executed.row_cases firstLive with boundary | actual
  · obtain ⟨slot, _index, node⟩ := boundary
    rw [node] at firstThread
    cases firstThread
  · obtain ⟨left, leftIndex, leftNode⟩ := actual
    rcases executed.row_cases secondLive with boundary | actual
    · obtain ⟨slot, _index, node⟩ := boundary
      rw [node] at secondThread
      cases secondThread
    · obtain ⟨right, rightIndex, rightNode⟩ := actual
      rw [leftNode] at firstThread
      rw [rightNode] at secondThread
      change some run.events[left.val].tid = some thread at firstThread
      change some run.events[right.val].tid = some thread at secondThread
      exact ⟨left, right, leftIndex, rightIndex,
        (Option.some.inj firstThread).trans (Option.some.inj secondThread).symm⟩

private theorem event_read {inputs : Inputs} {orders : Orders} {table : Table}
    {location : Atomics64.CellId64} {value : Word}
    (mapped : Built inputs orders table) (slot : Fin inputs.events.length)
    (read : Concurrency.C23Atomic.Reads table.toCandidate
      (inputs.initials.length + slot.val) location value) :
    inputs.events[slot.val].object = location ∧
      (inputs.events[slot.val].toSource orders).access.readValue = some value := by
  obtain ⟨node, live, object, read⟩ := read
  have same := Option.some.inj (live.symm.trans (mapped.event_at slot))
  subst node
  exact ⟨object, read⟩

private theorem event_write {inputs : Inputs} {orders : Orders} {table : Table}
    {location : Atomics64.CellId64} {value : Word}
    (mapped : Built inputs orders table) (slot : Fin inputs.events.length)
    (written : Concurrency.C23Atomic.Writes table.toCandidate
      (inputs.initials.length + slot.val) location value) :
    inputs.events[slot.val].object = location ∧
      (inputs.events[slot.val].toSource orders).access.writeValue = some value := by
  obtain ⟨node, live, object, written⟩ := written
  have same := Option.some.inj (live.symm.trans (mapped.event_at slot))
  subst node
  exact ⟨object, written⟩

namespace Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Table}

private theorem source_rank (executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin run.events.length) {source : WriterId} {rank observed : Nat}
    (read : ReadAccess run.events[slot.val] source)
    (ranked : WriterRank initial actions run.execution profile offset
      run.events[slot.val].object source rank)
    (edge : Concurrency.C23Atomic.ReadsFrom table.toCandidate
      (initials.length + slot.val) observed) : table.rank observed = rank := by
  obtain ⟨writer, selected, actualEdge⟩ := executed.mapped.readsFrom slot (read_key_requested read)
  have stored := executed.mapped.writer_rank (result := run.execution) rfl selected ranked
  have same := Concurrency.C23Atomic.readsFrom_unique edge actualEdge
  rw [same]
  simp only [Concurrency.C23Atomic.Check.Table.rank, stored, Option.getD_some]

/-- Every pair related by source graph sequencing satisfies all four atomic
coherence constraints. The proof covers every mapped row, not just a supplied
finite set of example pairs, and includes both roles of every actual RMW. -/
theorem sequencedCoherent
    (executed : Executed initial actions profile offset run initials orders table) :
    Concurrency.C23Atomic.SequencedCoherent table.toCandidate := by
  constructor
  · intro first second location a b firstWrite secondWrite before
    change table.rank first < table.rank second
    obtain ⟨left, right, leftIndex, rightIndex, sameThread⟩ := same_thread_rows executed before.2
    subst first
    subst second
    obtain ⟨firstAction, firstStamp, firstActual, firstMatched, ⟨firstWritten⟩, firstRank⟩ :=
      executed.write_rank left (event_write executed.mapped left firstWrite).2
    obtain ⟨secondAction, secondStamp, secondActual, secondMatched, ⟨secondWritten⟩, secondRank⟩ :=
      executed.write_rank right (event_write executed.mapped right secondWrite).2
    have ordered := executed.action_order left right (by have indices := before.1; omega)
      firstActual secondActual
    have writers : firstStamp.cause.tid = secondStamp.cause.tid :=
      (publication_tid firstMatched).trans (sameThread.trans (publication_tid secondMatched).symm)
    have ranked := (firstWritten.rank_order_iff secondWritten
      executed.execution.success executed.sequenced writers).mp ordered
    simpa only [firstRank, secondRank] using ranked
  · intro first second leftWriter rightWriter location a b firstRead secondRead firstEdge secondEdge before
    change table.rank leftWriter ≤ table.rank rightWriter
    obtain ⟨left, right, leftIndex, rightIndex, sameThread⟩ := same_thread_rows executed before.2
    subst first
    subst second
    obtain ⟨firstSource, firstAccess⟩ := read_key_of_value
      (event_read executed.mapped left firstRead).2
    obtain ⟨secondSource, secondAccess⟩ := read_key_of_value
      (event_read executed.mapped right secondRead).2
    obtain ⟨firstAction, firstActual⟩ := executed.event_origin left
    obtain ⟨secondAction, secondActual⟩ := executed.event_origin right
    have ordered := executed.action_order left right (by have indices := before.1; omega)
      firstActual secondActual
    have sameCell := (event_read executed.mapped left firstRead).1.trans
      (event_read executed.mapped right secondRead).1.symm
    obtain ⟨firstRank, secondRank, firstRanked, secondRanked, bound⟩ :=
      firstActual.read_read_source_rank executed.execution firstAccess secondActual secondAccess
        sameThread sameCell (Nat.le_of_lt ordered)
    rw [executed.source_rank left firstAccess firstRanked firstEdge,
      executed.source_rank right secondAccess secondRanked secondEdge]
    exact bound
  · intro reader observed writer location a b read edge write before
    change table.rank observed < table.rank writer
    obtain ⟨left, right, leftIndex, rightIndex, sameThread⟩ := same_thread_rows executed before.2
    subst reader
    subst writer
    obtain ⟨source, readAccess⟩ := read_key_of_value (event_read executed.mapped left read).2
    obtain ⟨readAction, actualRead⟩ := executed.event_origin left
    obtain ⟨writeAction, stamp, actualWrite, matched, ⟨written⟩, ownRank⟩ :=
      executed.write_rank right (event_write executed.mapped right write).2
    have ordered := executed.action_order left right (by have indices := before.1; omega)
      actualRead actualWrite
    obtain ⟨rank, ranked, bound⟩ := actualRead.read_write_source_rank_lt executed.execution
      readAccess written (sameThread.trans (publication_tid matched).symm) ordered
    rw [executed.source_rank left readAccess ranked edge, ownRank]
    exact bound
  · intro writer reader observed location a b write read edge before
    change table.rank writer ≤ table.rank observed
    obtain ⟨left, right, leftIndex, rightIndex, sameThread⟩ := same_thread_rows executed before.2
    subst writer
    subst reader
    obtain ⟨source, readAccess⟩ := read_key_of_value (event_read executed.mapped right read).2
    obtain ⟨writeAction, stamp, actualWrite, matched, ⟨written⟩, ownRank⟩ :=
      executed.write_rank left (event_write executed.mapped left write).2
    obtain ⟨readAction, actualRead⟩ := executed.event_origin right
    have ordered := executed.action_order left right (by have indices := before.1; omega)
      actualWrite actualRead
    have sameCell : stamp.cause.cell = run.events[right.val].object :=
      (publication_cell matched).trans ((event_write executed.mapped left write).1.trans
        (event_read executed.mapped right read).1.symm)
    obtain ⟨rank, ranked, bound⟩ := actualRead.write_read_source_rank executed.execution written
      readAccess (sameThread.symm.trans (publication_tid matched).symm) sameCell ordered
    rw [ownRank, executed.source_rank right readAccess ranked edge]
    exact bound

/-- No actual semantic RF source can be a later event in the same thread.
This remains independent of declared acquire/release labels and does not
assert the corresponding statement for arbitrary happens-before paths. -/
theorem noFutureSequenced
    (executed : Executed initial actions profile offset run initials orders table)
    {reader writer : Nat}
    (source : Concurrency.C23Atomic.ReadsFrom table.toCandidate reader writer) :
    ¬ Concurrency.C23Atomic.SeqBefore table.toCandidate reader writer := by
  intro before
  obtain ⟨location, value, read, write⟩ := source.2
  exact Nat.lt_irrefl (table.rank writer)
    (executed.sequencedCoherent.readWrite read source write before)

private theorem rmw_event
    (executed : Executed initial actions profile offset run initials orders table)
    {index : Nat} (rmw : Concurrency.C23Atomic.IsRMW table.toCandidate index) :
    ∃ (slot : Fin run.events.length) (changed : Atomics64.FetchAddEvent) (source : WriterId),
      index = initials.length + slot.val ∧ run.events[slot.val].access = .rmw changed source := by
  obtain ⟨node, live, isRMW⟩ := rmw
  rcases executed.row_cases live with boundary | actual
  · obtain ⟨slot, _aligned, same⟩ := boundary
    rw [same] at isRMW
    cases isRMW
  · obtain ⟨slot, aligned, same⟩ := actual
    rw [same] at isRMW
    cases access : run.events[slot.val].access with
    | load target word source =>
        simp only [Event.toSource, access, Concurrency.C23Atomic.Access.isRMW,
          Bool.false_eq_true] at isRMW
    | store target word occurrence =>
        simp only [Event.toSource, access, Concurrency.C23Atomic.Access.isRMW,
          Bool.false_eq_true] at isRMW
    | rmw changed source => exact ⟨slot, changed, source, aligned, access⟩

/-- Every graph RMW reads the immediately preceding modification of its
object. The source may be an initializer; all actual intervening graph writes
are ruled out using the complete scan's publication predecessor theorem.
Global action-position ranks need not be consecutive. -/
theorem rmwPredecessor
    (executed : Executed initial actions profile offset run initials orders table)
    {index writer : Nat} (rmw : Concurrency.C23Atomic.IsRMW table.toCandidate index)
    (edge : Concurrency.C23Atomic.ReadsFrom table.toCandidate index writer) :
    Concurrency.C23Atomic.ModBefore table.toCandidate writer index ∧
      ∀ middle, Concurrency.C23Atomic.ModBefore table.toCandidate writer middle →
        ¬ Concurrency.C23Atomic.ModBefore table.toCandidate middle index := by
  obtain ⟨slot, changed, source, indexEq, access⟩ := executed.rmw_event rmw
  subst index
  obtain ⟨actionIndex, actual⟩ := executed.event_origin slot
  obtain ⟨rank, ranked, _ownRanked, sourceBefore, predecessor⟩ :=
    actual.rmw_predecessor executed.execution access
  have rankedObject : WriterRank initial actions run.execution profile offset
      run.events[slot.val].object source rank := by
    simpa only [Event.object, access] using ranked
  have sourceRank := executed.source_rank slot (.rmw access) rankedObject edge
  obtain ⟨publication, _cause, position, stored⟩ := executed.mapped.rmw_rank slot access
  have ownRank : table.rank (initials.length + slot.val) = run.events[slot.val].position + 1 := by
    have storedAt : table.ranks[initials.length + slot.val]? =
        some (run.events[slot.val].position + 1) := by
      simp only [runInputs] at stored position
      rw [position] at stored
      exact stored
    simp only [Concurrency.C23Atomic.Check.Table.rank, storedAt, Option.getD_some]
  have read : Concurrency.C23Atomic.Reads table.toCandidate (initials.length + slot.val)
      changed.cell changed.arithmetic.event.before := by
    refine ⟨run.events[slot.val].toSource orders, executed.mapped.event_at slot, ?_, ?_⟩
    · simp only [Event.toSource, Event.object, access]
    · simp only [Event.toSource, access, Concurrency.C23Atomic.Access.readValue]
  have written : Concurrency.C23Atomic.Writes table.toCandidate (initials.length + slot.val)
      changed.cell changed.arithmetic.event.after := by
    refine ⟨run.events[slot.val].toSource orders, executed.mapped.event_at slot, ?_, ?_⟩
    · simp only [Event.toSource, Event.object, access]
    · simp only [Event.toSource, access, Concurrency.C23Atomic.Access.writeValue]
  refine ⟨⟨changed.cell, _, _, edge.source read, written, ?_⟩, ?_⟩
  · change table.rank writer < table.rank (initials.length + slot.val)
    rw [sourceRank, ownRank]
    exact sourceBefore
  · intro middle above below
    obtain ⟨_location, _before, _after, _sourceWritten, _middleWritten, aboveRank⟩ := above
    obtain ⟨location, before, after, middleWritten, ownWritten, belowRank⟩ := below
    have sameCell := (Concurrency.C23Atomic.Writes.unique ownWritten written).1
    subst location
    change table.rank writer < table.rank middle at aboveRank
    change table.rank middle < table.rank (initials.length + slot.val) at belowRank
    rcases executed.writes_cases middleWritten with boundary | actualWrite
    · obtain ⟨_initialSlot, _index, _object, _value, zero⟩ := boundary
      omega
    · obtain ⟨middleSlot, middleIndex, middleCell, middleValue⟩ := actualWrite
      obtain ⟨_action, stamp, _actual, matched, ⟨middleInstruction⟩, middleRank⟩ :=
        executed.write_rank middleSlot middleValue
      have earlier : stamp.position < run.events[slot.val].position := by
        rw [middleIndex, middleRank, ownRank] at belowRank
        omega
      have cell : stamp.cause.cell = changed.cell := (publication_cell matched).trans middleCell
      have bounded := predecessor stamp middleInstruction.publication cell earlier
      rw [middleIndex, middleRank, sourceRank] at aboveRank
      omega

end Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
