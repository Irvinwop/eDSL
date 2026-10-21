/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadOrder
import EDSL.OS.TSO64.ExecutionViews.Transfer

/-!
Transfer of actual views through the exact writer read by an actual load.
Another thread's source has already published; publication coverage therefore
puts the writer's other-cell views into the reader's published past. Own
forwarding instead uses the actual instruction order and same-worker view
monotonicity, without pretending that the buffered source has published.

These are numerical observation-position facts for one resource-checked finite
execution. They infer no source memory orders from machine bytes and establish
no synchronizes-with graph, happens-before relation, C23 legality, fairness or
native refinement. Incoming publication metadata starts empty; sequenced initial
mixed FIFOs may be nonempty, with no invented instruction origins.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- Reading a real instruction writer transfers every actual target view from
that writer's successor cut to the load's prestate view. The viewed target can
be a different cell from the loaded/written cell. Both published peer sources
and own forwarding are included, and their actual order is derived from the
load's exact writer identity rather than supplied as a numerical premise. -/
theorem EventAt.transfers_view {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {accessIndex writeIndex offset earlierRank laterRank : Nat}
    {readTarget target : Queue.ManagedRef} {word : X86.Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (loaded : event.access = .load readTarget word source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp)
    (earlier : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid target offset empty earlierRank)
    (later : ExecutionViews.At initial actions result profile accessIndex event.tid
      target offset empty laterRank) : earlierRank ≤ laterRank := by
  have order := actual.load_write_order execution loaded written readFrom
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

/-- Distinct current handles to the same persistent cell may be used for the
writer and reader views. Actual authorization supplies their shared descriptor;
there is no address, payload or handle-equality oracle in this adapter. -/
theorem EventAt.transfers_view_alias {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {accessIndex writeIndex offset earlierRank laterRank : Nat}
    {readTarget writerTarget readerTarget : Queue.ManagedRef}
    {writerResources readerResources : Resources}
    {word : X86.Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (loaded : event.access = .load readTarget word source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp)
    (earlier : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid writerTarget offset empty earlierRank)
    (later : ExecutionViews.At initial actions result profile accessIndex event.tid
      readerTarget offset empty laterRank)
    (writerCurrent : Queue.Current initial.world writerResources writerTarget)
    (readerCurrent : Queue.Current initial.world readerResources readerTarget)
    (sameCell : writerTarget.handle.cell = readerTarget.handle.cell) : earlierRank ≤ laterRank :=
  actual.transfers_view execution loaded written readFrom
    (earlier.retarget_current writerCurrent readerCurrent sameCell) later

/-- An actual access by the writer authenticates the target domain, and the
load authenticates the reader slot. Construct both views and their transfer
without a caller-supplied authority, view, rank or ordering witness. The target
access supplies only a domain; its own value is not a transferred assertion. -/
theorem EventAt.transfers_access_views {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event targetEvent : Event}
    {accessIndex writeIndex targetIndex offset : Nat} {readTarget : Queue.ManagedRef}
    {word : X86.Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (loaded : event.access = .load readTarget word source)
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
    actual.transfers_view execution loaded written readFrom actualWriterView readerView⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
