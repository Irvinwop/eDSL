/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.WriteSelf
import EDSL.OS.TSO64.ExecutionViews.Transfer
import EDSL.OS.TSO64.C23Projection.AtomicTrace.PublicationViews
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadOrder

/-!
Operational publication-rank constraints from actual program order. A write
followed by a same-cell read cannot read an older writer; two same-cell reads
cannot move backward in writer rank. A read's source publication strictly
precedes any later same-thread instruction write, even to another cell.

Targets and writer identities come from actual access/admission witnesses.
These finite successful-run facts are ingredients for graph coherence, not a
complete source-memory-order, happens-before, C23 legality or native theorem.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedHistory

/-- One original observation position has one complete publication stamp.
No word, cell, issue identity or queue-boundary comparison is needed. -/
theorem WriteAt.position_unique {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    {firstStamp secondStamp : Stamp}
    (first : WriteAt initial actions result profile offset firstStamp)
    (second : WriteAt initial actions result profile offset secondStamp)
    (samePosition : firstStamp.position = secondStamp.position) : firstStamp = secondStamp := by
  have firstPositionEq := first.position
  have secondPositionEq := second.position
  have sameIndex : first.index = second.index := by omega
  have observed : result.2[first.index]? = some second.observation := by
    simpa only [sameIndex] using second.observed
  have observationEq := Option.some.inj (first.observed.symm.trans observed)
  have secondWritten : writeOf first.observation = some secondStamp.cause := by
    simpa only [observationEq] using second.written
  have causeEq := Option.some.inj (first.written.symm.trans secondWritten)
  cases firstStamp with
  | mk firstPosition firstCause =>
    cases secondStamp with
    | mk secondPosition secondCause =>
      change firstPosition = secondPosition at samePosition
      change firstCause = secondCause at causeEq
      cases samePosition
      cases causeEq
      rfl

end EDSL.OS.TSO64.PublishedHistory

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- Equality with a real publication rank identifies the source writer key.
An initialized boundary is rank zero and cannot satisfy this equality. -/
theorem WriterRank.key_of_rank_eq {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset rank : Nat}
    {target : Atomics64.CellId64} {source : WriterId} {stamp : Stamp}
    (ranked : WriterRank initial actions result profile offset target source rank)
    (written : WriteAt initial actions result profile offset stamp)
    (same : rank = stamp.position + 1) : source = Graph.publicationKey stamp := by
  cases ranked with
  | initial => omega
  | @publication sourceStamp actual _cell =>
    have positions : sourceStamp.position = stamp.position := by omega
    exact congrArg Graph.publicationKey (actual.position_unique written positions)

private theorem load_initial_current {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {target : Queue.ManagedRef} {word : X86.Word} {source : WriterId}
    (actual : EventAt profile event index initial actions result offset empty)
    (loaded : event.access = .load target word source) :
    ∃ worker, initial.workers[event.tid]? = some worker ∧
      Queue.Current initial.world worker.resources target := by
  obtain ⟨worker, actualTarget, live, current, related⟩ := actual.initial_authority
  have targetEq : actualTarget = target := by
    simpa only [AccessTarget, loaded] using related.2
  subst actualTarget
  exact ⟨worker, live, current⟩

/-- A real same-thread write before a same-cell load is no later than the
load's exact source writer in publication rank. Initial and forwarded sources
are included; current target aliases are authenticated by the actual accesses. -/
theorem EventAt.write_read_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {readIndex writeIndex offset : Nat} {target : Queue.ManagedRef}
    {word : X86.Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (actual : EventAt profile event readIndex initial actions result offset empty)
    (loaded : event.access = .load target word source)
    (sameThread : event.tid = stamp.cause.tid)
    (sameCell : stamp.cause.cell = target.handle.cell) (ordered : writeIndex < readIndex) :
    ∃ rank, WriterRank initial actions result profile offset target.handle.cell source rank ∧
      stamp.position + 1 ≤ rank := by
  obtain ⟨_original, writerTarget, _writerLive, writerCurrent, writerCell, ⟨writerView⟩⟩ :=
    written.self_view execution empty
  obtain ⟨_reader, _readerLive, readerCurrent⟩ := load_initial_current actual loaded
  obtain ⟨rank, ⟨readView⟩, ranked⟩ := actual.load_view_rank execution loaded
  have aliasView := writerView.retarget_current writerCurrent readerCurrent (writerCell.trans sameCell)
  have ownView : ExecutionViews.At initial actions result profile (writeIndex + 1)
      event.tid target offset empty (stamp.position + 1) := by
    simpa only [sameThread] using aliasView
  have cuts : writeIndex + 1 ≤ readIndex := by omega
  exact ⟨rank, ranked, ownView.monotone execution (PublishedOrder.prior_empty offset) cuts readView⟩

/-- Ordered reads by one thread from the same persistent cell have
nondecreasing exact source ranks, including forwarding and current aliases. -/
theorem EventAt.read_read_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {first second : Event}
    {firstIndex secondIndex offset : Nat} {firstTarget secondTarget : Queue.ManagedRef}
    {firstWord secondWord : X86.Word} {firstSource secondSource : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (earlier : EventAt profile first firstIndex initial actions result offset empty)
    (firstLoad : first.access = .load firstTarget firstWord firstSource)
    (later : EventAt profile second secondIndex initial actions result offset empty)
    (secondLoad : second.access = .load secondTarget secondWord secondSource)
    (sameThread : first.tid = second.tid)
    (sameCell : firstTarget.handle.cell = secondTarget.handle.cell)
    (ordered : firstIndex ≤ secondIndex) :
    ∃ firstRank secondRank,
      WriterRank initial actions result profile offset firstTarget.handle.cell firstSource firstRank ∧
      WriterRank initial actions result profile offset secondTarget.handle.cell secondSource secondRank ∧
      firstRank ≤ secondRank := by
  obtain ⟨_first, _firstLive, firstCurrent⟩ := load_initial_current earlier firstLoad
  obtain ⟨_second, _secondLive, secondCurrent⟩ := load_initial_current later secondLoad
  obtain ⟨firstRank, ⟨firstView⟩, firstRanked⟩ := earlier.load_view_rank execution firstLoad
  obtain ⟨secondRank, ⟨secondView⟩, secondRanked⟩ := later.load_view_rank execution secondLoad
  have retargeted := firstView.retarget_current firstCurrent secondCurrent sameCell
  have sameWorker : ExecutionViews.At initial actions result profile firstIndex second.tid
      secondTarget offset empty firstRank := by
    simpa only [sameThread] using retargeted
  exact ⟨firstRank, secondRank, firstRanked, secondRanked,
    sameWorker.monotone execution (PublishedOrder.prior_empty offset) ordered secondView⟩

/-- The exact source of a read strictly precedes a later same-thread
instruction write in publication rank. The two cells may differ. Equality
would identify that later write as the actual source, contradicting the
execution-derived instruction-before-load order for a real source writer. -/
theorem EventAt.read_write_rank_lt {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {readIndex writeIndex offset : Nat} {target : Queue.ManagedRef}
    {word : X86.Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event readIndex initial actions result offset empty)
    (loaded : event.access = .load target word source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (sameThread : event.tid = stamp.cause.tid) (ordered : readIndex ≤ writeIndex) :
    ∃ rank, WriterRank initial actions result profile offset target.handle.cell source rank ∧
      rank < stamp.position + 1 := by
  obtain ⟨rank, ranked, bound⟩ :=
    actual.load_source_le_write execution loaded written sameThread ordered
  have different : rank ≠ stamp.position + 1 := by
    intro same
    have key := ranked.key_of_rank_eq written.publication same
    have before := actual.load_write_order execution loaded written key
    omega
  exact ⟨rank, ranked, by omega⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
