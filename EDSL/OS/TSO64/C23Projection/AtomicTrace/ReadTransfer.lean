/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadAccess
import EDSL.OS.TSO64.ExecutionViews.Transfer

/-!
Instruction order and view transfer through the exact source of an actual read
side. Loads retain own forwarding; an RMW reads an actual published-prefix
source and therefore follows its publication even when it belongs to the same
worker. Source identities authenticate complete real publications independently
of their words, targets and desired numerical ranks.

The execution is finite, successful, initially well formed/sequenced and finally
quiescent. Incoming publication metadata starts empty, while incoming mixed
FIFOs may be nonempty and receive no invented instruction origins. These are
operational observation-position facts; they establish no source-order
classification, synchronizes-with, happens-before, full C23 legality, fairness
or native refinement.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- Every actual read-side witness retains the event's precise source key. -/
theorem ReadAccess.source {event : Event} {source : WriterId}
    (read : ReadAccess event source) : event.source = some source := by
  cases read with
  | load loaded => simp only [Event.source, loaded]
  | rmw changed => simp only [Event.source, changed]

/-- Reading an independently witnessed instruction writer follows that real
instruction. Peer sources have already published. RMW reads also follow their
own sources' publications, whereas a load may forward an own buffered store.
No source-cell, rank or numerical ordering oracle is a premise. -/
theorem EventAt.read_write_order {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {readIndex writeIndex offset : Nat} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event readIndex initial actions result offset empty)
    (read : ReadAccess event source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp) :
    writeIndex < readIndex ∧
      (stamp.cause.tid ≠ event.tid → written.publication.index < readIndex) := by
  cases read with
  | load loaded => exact actual.load_write_order execution loaded written readFrom
  | @rmw changed rmw =>
      obtain ⟨_target, sourceRank, _related, _view, ranked, _ownRanked, sourceBefore⟩ :=
        actual.rmw_view_rank execution rmw
      have sourceCell : stamp.cause.cell = changed.cell := by
        cases ranked with
        | initial =>
            cases stamp with
            | mk position cause => cases cause <;> cases readFrom
        | @publication sourceStamp sourceActual cell =>
            have sameStamp := publicationKey_writeAt_unique execution.success execution.sequenced
              sourceActual written.publication readFrom
            simpa only [sameStamp] using cell
      have actualRanked : WriterRank initial actions result profile offset changed.cell
          source (stamp.position + 1) := by
        rw [readFrom]
        exact .publication written.publication sourceCell
      have sameRank := WriterRank.unique execution.success execution.sequenced ranked actualRanked
      have eventPosition := actual.position
      have publicationPosition := written.publication.position
      have publishedBefore : written.publication.index < readIndex := by omega
      exact ⟨Nat.lt_of_le_of_lt (written.index_le_publication execution.sequenced)
        publishedBefore, fun _different => publishedBefore⟩

/-- Every actual target view after the source writer's instruction transfers to
the reader's prestate view, including RMW read sides and own forwarding loads.
The viewed target may be a different cell from the read and source write. -/
theorem EventAt.read_transfers_view {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {accessIndex writeIndex offset earlierRank laterRank : Nat}
    {target : Queue.ManagedRef} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (read : ReadAccess event source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp)
    (earlier : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid target offset empty earlierRank)
    (later : ExecutionViews.At initial actions result profile accessIndex event.tid
      target offset empty laterRank) : earlierRank ≤ laterRank := by
  have order := actual.read_write_order execution read written readFrom
  have cuts : writeIndex + 1 ≤ accessIndex := by omega
  by_cases own : stamp.cause.tid = event.tid
  · have ownEarlier : ExecutionViews.At initial actions result profile (writeIndex + 1)
        event.tid target offset empty earlierRank := by
      simpa only [own] using earlier
    exact ownEarlier.monotone execution (PublishedOrder.prior_empty offset) cuts later
  · have publishedBefore := order.2 own
    have covered := written.covers_after execution (PublishedOrder.prior_empty offset) earlier
    have position := written.publication.position
    have visible : earlierRank ≤ offset + accessIndex := by omega
    exact earlier.le_of_rank_before_cut later (PublishedOrder.prior_empty offset) cuts visible rfl

/-- Transfer between distinct authorized aliases of the same persistent viewed
cell. Current authorization derives their descriptor/address agreement; no
payload, address or handle-equality oracle identifies that cell. -/
theorem EventAt.read_transfers_view_alias {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {accessIndex writeIndex offset earlierRank laterRank : Nat}
    {writerTarget readerTarget : Queue.ManagedRef}
    {writerResources readerResources : Resources}
    {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (read : ReadAccess event source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp)
    (earlier : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid writerTarget offset empty earlierRank)
    (later : ExecutionViews.At initial actions result profile accessIndex event.tid
      readerTarget offset empty laterRank)
    (writerCurrent : Queue.Current initial.world writerResources writerTarget)
    (readerCurrent : Queue.Current initial.world readerResources readerTarget)
    (sameCell : writerTarget.handle.cell = readerTarget.handle.cell) : earlierRank ≤ laterRank :=
  actual.read_transfers_view execution read written readFrom
    (earlier.retarget_current writerCurrent readerCurrent sameCell) later

/-- A real target access by the writer authenticates the viewed domain, and
the actual read authenticates the reader slot. Construct both actual views and
their transfer without caller-supplied authority, view, rank or ordering
witnesses. The target access supplies its domain, not a transferred value. -/
theorem EventAt.read_transfers_access_views {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event targetEvent : Event}
    {accessIndex writeIndex targetIndex offset : Nat} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (read : ReadAccess event source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp)
    (targetActual : EventAt profile targetEvent targetIndex initial actions result offset empty)
    (targetThread : targetEvent.tid = stamp.cause.tid) :
    ∃ target earlierRank laterRank, AccessTarget targetEvent target ∧
      Nonempty (ExecutionViews.At initial actions result profile (writeIndex + 1)
        stamp.cause.tid target offset empty earlierRank) ∧
      Nonempty (ExecutionViews.At initial actions result profile accessIndex event.tid
        target offset empty laterRank) ∧ earlierRank ≤ laterRank := by
  obtain ⟨_writer, target, writerLive, current, related⟩ := targetActual.initial_authority
  obtain ⟨_reader, _readTarget, readerLive, _readCurrent, _readRelated⟩ := actual.initial_authority
  obtain ⟨earlierRank, ⟨writerView⟩⟩ :=
    ExecutionViews.exists_at execution writerLive (writeIndex + 1) current offset empty
  obtain ⟨laterRank, ⟨readerView⟩⟩ :=
    ExecutionViews.exists_at execution readerLive accessIndex current offset empty
  have actualWriterView : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid target offset empty earlierRank := by
    simpa only [targetThread] using writerView
  exact ⟨target, earlierRank, laterRank, related, ⟨actualWriterView⟩, ⟨readerView⟩,
    actual.read_transfers_view execution read written readFrom actualWriterView readerView⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
