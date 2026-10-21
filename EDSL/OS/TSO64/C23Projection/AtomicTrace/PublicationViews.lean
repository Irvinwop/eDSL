/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.PublicationCovers
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadRanks

/-!
Publication bounds for domains authenticated by actual accesses. A write covers
all earlier views of its worker, including views of other managed cells. Actual
access authority supplies the domain and worker; no view or numerical rank is
provided as a caller's intended answer.

The load corollary retains its exact source writer and bounds that writer's rank
by a later same-thread write's actual publication. These finite successful-run
results are numerical order facts, not an inference of source-language memory
orders or a complete release/acquire, happens-before or C23 legality theorem.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- Any actual access authenticates its target domain at every earlier cut.
The writing worker's view there is covered by the real write publication, even
when the accessed cell differs from the cell written by that instruction. -/
theorem EventAt.covered_by_write {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {accessIndex writeIndex offset cut : Nat} {incoming : Writers} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset incoming)
    (prior : PublishedOrder.Prior offset incoming)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (sameThread : event.tid = stamp.cause.tid) (ordered : cut ≤ writeIndex + 1) :
    ∃ target value, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile cut event.tid
        target offset incoming value) ∧ value ≤ stamp.position + 1 := by
  obtain ⟨_original, target, live, current, related⟩ := actual.initial_authority
  obtain ⟨value, ⟨view⟩⟩ :=
    ExecutionViews.exists_at execution live cut current offset incoming
  obtain ⟨postValue, ⟨postView⟩⟩ :=
    ExecutionViews.exists_at execution live (writeIndex + 1) current offset incoming
  have monotone := view.monotone execution prior ordered postView
  have ownPost : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid target offset incoming postValue := by
    simpa only [sameThread] using postView
  have bound := written.covers_after execution prior ownPost
  exact ⟨target, value, related, ⟨view⟩, Nat.le_trans monotone bound⟩

/-- The exact source writer read by an actual load is no later in publication
rank than a later instruction write by that same worker. Source and written
cells may differ. Empty incoming metadata is retained by the source-rank API;
initial queues need not be empty and receive no invented earlier issues. -/
theorem EventAt.load_source_le_write {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {accessIndex writeIndex offset : Nat} {stamp : Stamp} {target : Queue.ManagedRef}
    {value : X86.Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (loaded : event.access = .load target value source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (sameThread : event.tid = stamp.cause.tid) (ordered : accessIndex ≤ writeIndex) :
    ∃ rank, WriterRank initial actions result profile offset target.handle.cell source rank ∧
      rank ≤ stamp.position + 1 := by
  obtain ⟨rank, ⟨sourceView⟩, ranked⟩ := actual.load_view_rank execution loaded
  obtain ⟨actualTarget, boundValue, related, ⟨boundView⟩, bounded⟩ :=
    actual.covered_by_write execution (PublishedOrder.prior_empty offset) written sameThread
      (Nat.le_trans ordered (Nat.le_succ writeIndex))
  have targetEq : actualTarget = target := by
    simpa only [AccessTarget, loaded] using related.2
  subst actualTarget
  have same := sourceView.unique boundView
  exact ⟨rank, ranked, by omega⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
