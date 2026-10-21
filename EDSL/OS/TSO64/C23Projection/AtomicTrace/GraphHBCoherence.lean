/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphViewTransfer
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphCoherence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphWellFormed

/-!
All four happens-before coherence obligations for a structurally mapped actual
finite scan, with arbitrary explicitly declared atomic interface orders. Exact
source-writer ranks and write postviews are transported along the actual HB
path. RMWs participate in both read and write roles. Structural same-object
rank uniqueness, HB acyclicity and no-future RF make the required bounds strict.

The actual execution is initially well formed and sequenced, ends quiescent,
and has empty incoming publication metadata. Incoming ordinary FIFO entries
may be nonempty. The complete structural mapping excludes incoming managed
entries rather than inventing instruction origins for them. Supplied
initial-manifest provenance remains separate.

Legality here is the modeled finite relaxed/acquire/release atomic fragment.
No HB, coherence, legality or checker-success premise is supplied. This does
not establish full C23 semantics, source/compiler/native/kernel preservation,
fairness, graph-construction totality or a corpus claim.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86 PublishedHistory

private theorem readAccess_of_readValue {event : Event} {orders : Orders} {value : Word}
    (read : (event.toSource orders).access.readValue = some value) :
    ∃ source, ReadAccess event source := by
  cases access : event.access with
  | load target word source => exact ⟨source, .load access⟩
  | store target word occurrence =>
      simp only [Event.toSource, access, Concurrency.C23Atomic.Access.readValue] at read
      cases read
  | rmw changed source => exact ⟨source, .rmw access⟩

private theorem event_read_role {inputs : Inputs} {orders : Orders} {table : Table}
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

private theorem event_write_role {inputs : Inputs} {orders : Orders} {table : Table}
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

private theorem matched_tid {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) : stamp.cause.tid = event.tid := by
  cases access : event.access with
  | load target value source => simp only [Publication, access] at matched
  | store target value occurrence =>
      have parts : stamp.cause = .buffered event.tid target value occurrence ∧
          event.position < stamp.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.tid]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.tid]

private theorem matched_cell {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) : stamp.cause.cell = event.object := by
  cases access : event.access with
  | load target value source => simp only [Publication, access] at matched
  | store target value occurrence =>
      have parts : stamp.cause = .buffered event.tid target value occurrence ∧
          event.position < stamp.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.cell, Event.object, access]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.cell, Event.object, access]

private theorem access_target_address {event : Event} {first second : Queue.ManagedRef}
    (left : AccessTarget event first) (right : AccessTarget event second) :
    first.cell.address = second.cell.address := by
  cases event with
  | mk position tid access =>
      cases access with
      | load reference value source =>
          exact congrArg (fun target : Queue.ManagedRef => target.cell.address)
            (left.2.trans right.2.symm)
      | store reference value occurrence =>
          exact congrArg (fun target : Queue.ManagedRef => target.cell.address)
            (left.2.trans right.2.symm)
      | rmw changed source => exact left.2.2.trans right.2.2.symm

namespace Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Table}

/-- Authenticate the read-view target using the actual access's complete
initial authority. The access's two target witnesses agree by its recorded
address and persistent cell; no authority is fabricated for the rank witness. -/
private theorem read_rank_at
    (executed : Executed initial actions profile offset run initials orders table)
    {event : Event} {index : Nat} {source : WriterId}
    (actual : EventAt profile event index initial actions run.execution offset empty)
    (read : ReadAccess event source) :
    ∃ (target : Queue.ManagedRef) (resources : Resources) (rank : Nat),
      Queue.Current initial.world resources target ∧
      target.handle.cell = event.object ∧
      Nonempty (ExecutionViews.At initial actions run.execution profile index event.tid
        target offset empty rank) ∧
      WriterRank initial actions run.execution profile offset event.object source rank := by
  obtain ⟨original, target, _live, current, related⟩ := actual.initial_authority
  obtain ⟨readTarget, rank, readRelated, ⟨view⟩, ranked⟩ :=
    actual.read_view_rank executed.execution read
  exact ⟨target, original.resources, rank, current, related.1,
    ⟨view.retarget (access_target_address readRelated related)
      (readRelated.1.trans related.1.symm)⟩, ranked⟩

/-- Express the actual writer's exact own postview using its graph event's
thread and object. Authority comes from the instruction issue or guarded RMW. -/
private theorem write_rank_at
    (executed : Executed initial actions profile offset run initials orders table)
    {event : Event} {index : Nat} {stamp : Stamp}
    (matched : Publication event stamp)
    (written : InstructionWriteAt initial actions run.execution profile offset index stamp) :
    ∃ (target : Queue.ManagedRef) (resources : Resources),
      Queue.Current initial.world resources target ∧
      target.handle.cell = event.object ∧
      Nonempty (ExecutionViews.At initial actions run.execution profile (index + 1)
        event.tid target offset empty (stamp.position + 1)) := by
  obtain ⟨original, target, _live, current, cell, ⟨view⟩⟩ :=
    written.self_view executed.execution empty
  refine ⟨target, original.resources, current, cell.trans (matched_cell matched), ?_⟩
  exact ⟨by simpa only [matched_tid matched] using view⟩

/-- Semantic RF uniqueness connects the exact operational source key to the
selected full graph row. Equal stored words never identify source writers. -/
private theorem rf_rank
    (executed : Executed initial actions profile offset run initials orders table)
    (slot : Fin run.events.length) {source : WriterId} {rank observed : Nat}
    (read : ReadAccess run.events[slot.val] source)
    (ranked : WriterRank initial actions run.execution profile offset
      run.events[slot.val].object source rank)
    (edge : Concurrency.C23Atomic.ReadsFrom table.toCandidate
      (initials.length + slot.val) observed) : table.rank observed = rank := by
  obtain ⟨writer, selected, actualEdge⟩ := executed.mapped.readsFrom slot read.source
  have stored := executed.mapped.writer_rank (result := run.execution) rfl selected ranked
  have same := Concurrency.C23Atomic.readsFrom_unique edge actualEdge
  rw [same]
  simp only [Concurrency.C23Atomic.Check.Table.rank, stored, Option.getD_some]

/-- Use the fixed post-to-pre HB transport between genuine endpoint views.
Within each endpoint, ordinary view monotonicity permits a preview at the first
event and a postview at the second. Actual endpoint origins supply both live
worker slots; current authority authenticates the common alias target. -/
private theorem views_le
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Fin run.events.length}
    {firstIndex secondIndex firstCut secondCut earlierRank laterRank : Nat}
    {firstTarget secondTarget : Queue.ManagedRef}
    {firstResources secondResources : Resources}
    (path : Concurrency.C23Atomic.HappensBefore table.toCandidate
      (initials.length + first.val) (initials.length + second.val))
    (firstActual : EventAt profile run.events[first.val] firstIndex initial actions
      run.execution offset empty)
    (secondActual : EventAt profile run.events[second.val] secondIndex initial actions
      run.execution offset empty)
    (firstCurrent : Queue.Current initial.world firstResources firstTarget)
    (secondCurrent : Queue.Current initial.world secondResources secondTarget)
    (sameCell : firstTarget.handle.cell = secondTarget.handle.cell)
    (earlier : ExecutionViews.At initial actions run.execution profile firstCut
      run.events[first.val].tid firstTarget offset empty earlierRank)
    (later : ExecutionViews.At initial actions run.execution profile secondCut
      run.events[second.val].tid secondTarget offset empty laterRank)
    (firstCutBefore : firstCut ≤ firstIndex + 1)
    (secondCutAfter : secondIndex ≤ secondCut) : earlierRank ≤ laterRank := by
  obtain ⟨_firstWorker, _firstAccessTarget, firstLive, _firstAuthority, _firstRelated⟩ :=
    firstActual.initial_authority
  obtain ⟨_secondWorker, _secondAccessTarget, secondLive, _secondAuthority, _secondRelated⟩ :=
    secondActual.initial_authority
  obtain ⟨postRank, ⟨post⟩⟩ := ExecutionViews.exists_at executed.execution firstLive
    (firstIndex + 1) secondCurrent offset empty
  obtain ⟨preRank, ⟨pre⟩⟩ := ExecutionViews.exists_at executed.execution secondLive
    secondIndex secondCurrent offset empty
  have aliasView := earlier.retarget_current firstCurrent secondCurrent sameCell
  have before := aliasView.monotone executed.execution (PublishedOrder.prior_empty offset)
    firstCutBefore post
  have across := executed.hb_transfers_view (first := first) (second := second)
    path firstActual secondActual secondCurrent post pre
  have after := pre.monotone executed.execution (PublishedOrder.prior_empty offset)
    secondCutAfter later
  exact Nat.le_trans before (Nat.le_trans across after)

/-- Every actual mapped run satisfies all four happens-before coherence
conditions for arbitrary declared orders. Initializers cannot be HB endpoints;
all actual load and RMW read sides retain their exact selected source writers. -/
theorem hbCoherent
    (executed : Executed initial actions profile offset run initials orders table) :
    Concurrency.C23Atomic.Coherent table.toCandidate := by
  constructor
  · intro first second location a b firstWrite secondWrite path
    change table.rank first < table.rank second
    have bound : table.rank first ≤ table.rank second := by
      obtain ⟨left, right, leftIndex, rightIndex⟩ := executed.hb_event_rows path
      subst first
      subst second
      obtain ⟨firstObject, firstValue⟩ := event_write_role executed.mapped left firstWrite
      obtain ⟨secondObject, secondValue⟩ := event_write_role executed.mapped right secondWrite
      obtain ⟨firstAction, firstStamp, firstActual, firstMatched, ⟨firstWritten⟩, firstRank⟩ :=
        executed.write_rank left firstValue
      obtain ⟨secondAction, secondStamp, secondActual, secondMatched, ⟨secondWritten⟩, secondRank⟩ :=
        executed.write_rank right secondValue
      obtain ⟨firstTarget, _firstResources, firstCurrent, firstCell, ⟨firstView⟩⟩ :=
        executed.write_rank_at firstMatched firstWritten
      obtain ⟨secondTarget, _secondResources, secondCurrent, secondCell, ⟨secondView⟩⟩ :=
        executed.write_rank_at secondMatched secondWritten
      rw [firstRank, secondRank]
      exact executed.views_le (first := left) (second := right)
        path firstActual secondActual firstCurrent secondCurrent
        (firstCell.trans (firstObject.trans (secondObject.symm.trans secondCell.symm)))
        firstView secondView (Nat.le_refl _) (Nat.le_succ _)
    have different : table.rank first ≠ table.rank second := by
      intro equal
      have same := executed.mapped.wellFormed.rankUnique first second location a b
        firstWrite secondWrite equal
      subst second
      exact executed.hb_acyclic first path
    omega
  · intro first second leftWriter rightWriter location a b firstRead secondRead firstEdge secondEdge path
    change table.rank leftWriter ≤ table.rank rightWriter
    obtain ⟨left, right, leftIndex, rightIndex⟩ := executed.hb_event_rows path
    subst first
    subst second
    obtain ⟨firstObject, firstValue⟩ := event_read_role executed.mapped left firstRead
    obtain ⟨secondObject, secondValue⟩ := event_read_role executed.mapped right secondRead
    obtain ⟨firstSource, firstAccess⟩ := readAccess_of_readValue firstValue
    obtain ⟨secondSource, secondAccess⟩ := readAccess_of_readValue secondValue
    obtain ⟨firstAction, firstActual⟩ := executed.event_origin left
    obtain ⟨secondAction, secondActual⟩ := executed.event_origin right
    obtain ⟨firstTarget, _firstResources, firstRank, firstCurrent, firstCell, ⟨firstView⟩, firstRanked⟩ :=
      executed.read_rank_at firstActual firstAccess
    obtain ⟨secondTarget, _secondResources, secondRank, secondCurrent, secondCell, ⟨secondView⟩, secondRanked⟩ :=
      executed.read_rank_at secondActual secondAccess
    rw [executed.rf_rank left firstAccess firstRanked firstEdge,
      executed.rf_rank right secondAccess secondRanked secondEdge]
    exact executed.views_le (first := left) (second := right)
      path firstActual secondActual firstCurrent secondCurrent
      (firstCell.trans (firstObject.trans (secondObject.symm.trans secondCell.symm)))
      firstView secondView (Nat.le_succ _) (Nat.le_refl _)
  · intro reader observed writer location a b read edge write path
    change table.rank observed < table.rank writer
    have bound : table.rank observed ≤ table.rank writer := by
      obtain ⟨left, right, leftIndex, rightIndex⟩ := executed.hb_event_rows path
      subst reader
      subst writer
      obtain ⟨readObject, readValue⟩ := event_read_role executed.mapped left read
      obtain ⟨writeObject, writeValue⟩ := event_write_role executed.mapped right write
      obtain ⟨source, access⟩ := readAccess_of_readValue readValue
      obtain ⟨readAction, actualRead⟩ := executed.event_origin left
      obtain ⟨writeAction, stamp, actualWrite, matched, ⟨written⟩, ownRank⟩ :=
        executed.write_rank right writeValue
      obtain ⟨readTarget, _readResources, rank, readCurrent, readCell, ⟨readView⟩, ranked⟩ :=
        executed.read_rank_at actualRead access
      obtain ⟨writeTarget, _writeResources, writeCurrent, writeCell, ⟨writeView⟩⟩ :=
        executed.write_rank_at matched written
      rw [executed.rf_rank left access ranked edge, ownRank]
      exact executed.views_le (first := left) (second := right)
        path actualRead actualWrite readCurrent writeCurrent
        (readCell.trans (readObject.trans (writeObject.symm.trans writeCell.symm)))
        readView writeView (Nat.le_succ _) (Nat.le_succ _)
    have different : table.rank observed ≠ table.rank writer := by
      intro equal
      have same := executed.mapped.wellFormed.rankUnique observed writer location a b
        (edge.source read) write equal
      subst writer
      exact executed.noFutureHB edge path
    omega
  · intro writer reader observed location a b write read edge path
    change table.rank writer ≤ table.rank observed
    obtain ⟨left, right, leftIndex, rightIndex⟩ := executed.hb_event_rows path
    subst writer
    subst reader
    obtain ⟨writeObject, writeValue⟩ := event_write_role executed.mapped left write
    obtain ⟨readObject, readValue⟩ := event_read_role executed.mapped right read
    obtain ⟨source, access⟩ := readAccess_of_readValue readValue
    obtain ⟨writeAction, stamp, actualWrite, matched, ⟨written⟩, ownRank⟩ :=
      executed.write_rank left writeValue
    obtain ⟨readAction, actualRead⟩ := executed.event_origin right
    obtain ⟨writeTarget, _writeResources, writeCurrent, writeCell, ⟨writeView⟩⟩ :=
      executed.write_rank_at matched written
    obtain ⟨readTarget, _readResources, rank, readCurrent, readCell, ⟨readView⟩, ranked⟩ :=
      executed.read_rank_at actualRead access
    rw [ownRank, executed.rf_rank right access ranked edge]
    exact executed.views_le (first := left) (second := right)
      path actualWrite actualRead writeCurrent readCurrent
      (writeCell.trans (writeObject.trans (readObject.symm.trans readCell.symm)))
      writeView readView (Nat.le_refl _) (Nat.le_refl _)

/-- Universal legality of the modeled finite atomic fragment follows from
actual execution and structural correspondence, with no annotation restriction
or legality-checker oracle. Initial-manifest provenance is a separate contract. -/
theorem legal
    (executed : Executed initial actions profile offset run initials orders table) :
    Concurrency.C23Atomic.Legal table.toCandidate := by
  exact ⟨executed.mapped.wellFormed, executed.hbCoherent, executed.hb_acyclic,
    (fun edge => executed.noFutureHB edge), (fun rmw edge => executed.rmwPredecessor rmw edge)⟩

end Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
