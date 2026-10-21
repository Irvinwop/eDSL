/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Coherence

/-!
Uniform source-rank constraints for the read side of actual loads and RMWs.
The access supplies its complete source identity and authenticated target;
the successful execution supplies the exact publication rank and views.

All three program-order constraints include the read side of RMWs. Incoming
queues may be nonempty, and the incoming publication map is empty. These
operational finite-run facts do not classify source memory orders or establish
happens-before, full C23 legality, fairness, or native execution refinement.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- An actual read side, retaining its precise source writer. RMWs are both
reads and writes; a pure store has no witness of this predicate. -/
inductive ReadAccess (event : Event) (source : WriterId) : Prop where
  | load {target : Queue.ManagedRef} {value : X86.Word}
      (access : event.access = .load target value source)
  | rmw {changed : Atomics64.FetchAddEvent}
      (access : event.access = .rmw changed source)

/-- Actual read sides have an exact source-rank view at their instruction
prestate. No source rank, intended view, or target authority is a premise. -/
theorem EventAt.read_view_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (read : ReadAccess event source) :
    ∃ target rank, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid
        target offset empty rank) ∧
      WriterRank initial actions result profile offset event.object source rank := by
  cases read with
  | @load target value loaded =>
      obtain ⟨rank, view, ranked⟩ := actual.load_view_rank execution loaded
      refine ⟨target, rank, ?_, view, ?_⟩
      · simp only [AccessTarget, Event.object, loaded, and_self]
      · simpa only [Event.object, loaded] using ranked
  | rmw changed =>
      obtain ⟨target, rank, related, view, ranked, _ownRanked, _bound⟩ :=
        actual.rmw_view_rank execution changed
      exact ⟨target, rank, related, view, by
        simpa only [Event.object, changed] using ranked⟩

private theorem target_address_eq {event : Event} {first second : Queue.ManagedRef}
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

/-- Retain the actual initial authority while selecting the read-side rank.
Different target witnesses agree in address from the access annotation, so
this transport does not assume a fabricated authority for a view target. -/
private theorem EventAt.read_current_view_rank
    {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (read : ReadAccess event source) :
    ∃ original target rank, initial.workers[event.tid]? = some original ∧
      Queue.Current initial.world original.resources target ∧ AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid
        target offset empty rank) ∧
      WriterRank initial actions result profile offset event.object source rank := by
  obtain ⟨original, target, live, current, related⟩ := actual.initial_authority
  obtain ⟨readTarget, rank, readRelated, ⟨view⟩, ranked⟩ :=
    actual.read_view_rank execution read
  exact ⟨original, target, rank, live, current, related,
    ⟨view.retarget (target_address_eq readRelated related)
      (readRelated.1.trans related.1.symm)⟩, ranked⟩

/-- A same-thread write before a same-cell read side has a publication rank
at most the exact source rank. Both plain loads and RMW reads are covered. -/
theorem EventAt.write_read_source_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {readIndex writeIndex offset : Nat} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (actual : EventAt profile event readIndex initial actions result offset empty)
    (read : ReadAccess event source)
    (sameThread : event.tid = stamp.cause.tid)
    (sameCell : stamp.cause.cell = event.object) (ordered : writeIndex < readIndex) :
    ∃ rank, WriterRank initial actions result profile offset event.object source rank ∧
      stamp.position + 1 ≤ rank := by
  obtain ⟨_original, writerTarget, _writerLive, writerCurrent, writerCell, ⟨writerView⟩⟩ :=
    written.self_view execution empty
  obtain ⟨_reader, target, rank, _readerLive, readerCurrent, related, ⟨readView⟩, ranked⟩ :=
    actual.read_current_view_rank execution read
  have aliasView := writerView.retarget_current writerCurrent readerCurrent
    (writerCell.trans (sameCell.trans related.1.symm))
  have ownView : ExecutionViews.At initial actions result profile (writeIndex + 1)
      event.tid target offset empty (stamp.position + 1) := by
    simpa only [sameThread] using aliasView
  have cuts : writeIndex + 1 ≤ readIndex := by omega
  exact ⟨rank, ranked,
    ownView.monotone execution (PublishedOrder.prior_empty offset) cuts readView⟩

/-- Read sides of one thread from one persistent cell cannot move backward
in their exact source publication ranks. RMWs may occur on either side. -/
theorem EventAt.read_read_source_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {first second : Event}
    {firstIndex secondIndex offset : Nat} {firstSource secondSource : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (earlier : EventAt profile first firstIndex initial actions result offset empty)
    (firstRead : ReadAccess first firstSource)
    (later : EventAt profile second secondIndex initial actions result offset empty)
    (secondRead : ReadAccess second secondSource)
    (sameThread : first.tid = second.tid) (sameCell : first.object = second.object)
    (ordered : firstIndex ≤ secondIndex) :
    ∃ firstRank secondRank,
      WriterRank initial actions result profile offset first.object firstSource firstRank ∧
      WriterRank initial actions result profile offset second.object secondSource secondRank ∧
      firstRank ≤ secondRank := by
  obtain ⟨_first, firstTarget, firstRank, _firstLive, firstCurrent,
    firstRelated, ⟨firstView⟩, firstRanked⟩ :=
    earlier.read_current_view_rank execution firstRead
  obtain ⟨_second, secondTarget, secondRank, _secondLive, secondCurrent,
    secondRelated, ⟨secondView⟩, secondRanked⟩ :=
    later.read_current_view_rank execution secondRead
  have retargeted := firstView.retarget_current firstCurrent secondCurrent
    (firstRelated.1.trans (sameCell.trans secondRelated.1.symm))
  have sameWorker : ExecutionViews.At initial actions result profile firstIndex second.tid
      secondTarget offset empty firstRank := by
    simpa only [sameThread] using retargeted
  exact ⟨firstRank, secondRank, firstRanked, secondRanked,
    sameWorker.monotone execution (PublishedOrder.prior_empty offset) ordered secondView⟩

/-- The source of an earlier read side strictly precedes every later
same-thread instruction write in publication rank, even across cells. An RMW
source is already before its own real action; the later write cannot publish
before its actual instruction. A load uses its exact source's recovered issue
order, including store-buffer forwarding. -/
theorem EventAt.read_write_source_rank_lt {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {readIndex writeIndex offset : Nat} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event readIndex initial actions result offset empty)
    (read : ReadAccess event source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (sameThread : event.tid = stamp.cause.tid) (ordered : readIndex < writeIndex) :
    ∃ rank, WriterRank initial actions result profile offset event.object source rank ∧
      rank < stamp.position + 1 := by
  cases read with
  | load loaded =>
      obtain ⟨rank, ranked, bound⟩ := actual.read_write_rank_lt execution loaded written
        sameThread (Nat.le_of_lt ordered)
      exact ⟨rank, by simpa only [Event.object, loaded] using ranked, bound⟩
  | rmw changed =>
      obtain ⟨_target, rank, _related, _view, ranked, _ownRanked, before⟩ :=
        actual.rmw_view_rank execution changed
      have eventPosition := actual.position
      have writtenPosition := written.publication.position
      have publicationAfter := written.index_le_publication execution.sequenced
      refine ⟨rank, ?_, by omega⟩
      simpa only [Event.object, changed] using ranked

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
