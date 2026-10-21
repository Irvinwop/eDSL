/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadRanks

/-!
The exact source of an actual RMW is its same-cell publication predecessor.
Ranks retain original global action positions, including silent observations
and publications to other cells, so predecessor does not mean adjacent ranks.
Equal-valued writes and zero-delta RMWs retain their complete writer identities.

The execution is finite, successful, initially well formed/sequenced and finally
quiescent. Incoming queues may be nonempty; the incoming publication map is
empty. An initial source has rank zero and permits no earlier same-cell write
in this run. No instruction issue is invented for an incoming queued entry.
These results do not establish full C23 legality, source memory orders,
happens-before, native refinement, fairness or corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedHistory

/-- Every actual publication before a cut is bounded by that prefix's
published view. Restrict the original observation witness to the prefix;
the latest-writer domination also covers an initially absent map. No complete-run
success or prior-position premise is needed for arbitrary incoming metadata. -/
theorem WriteAt.before_cut_view {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset cut : Nat}
    {incoming : Writers} {stamp : Stamp}
    (witness : WriteAt initial actions result profile offset stamp)
    (earlier : stamp.position < offset + cut) :
    stamp.position + 1 ≤
      PublishedOrder.view (after offset (result.2.take cut) incoming) stamp.cause.cell := by
  have inside : witness.index < cut := by
    have position := witness.position
    omega
  have selected : (result.2.take cut)[witness.index]? = some witness.observation := by
    simpa only [List.getElem?_take_of_lt inside] using witness.observed
  have bound := ExecutionViews.publication_view_bound
    (offset := offset) (incoming := incoming) selected witness.written
  simpa only [witness.position] using bound

end EDSL.OS.TSO64.PublishedHistory

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open PublishedHistory

/-- The exact source and own writer of an actual RMW, together with the
universal same-cell predecessor bound over all publications in the complete
run. Every earlier same-cell publication is at or before the source rank.
No graph mapping, legality certificate or no-intervening oracle is a premise. -/
theorem EventAt.rmw_predecessor {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {changed : Atomics64.FetchAddEvent}
    {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (rmw : event.access = .rmw changed source) :
    ∃ sourceRank,
      WriterRank initial actions result profile offset changed.cell source sourceRank ∧
      WriterRank initial actions result profile offset changed.cell
        (.rmw event.position) (event.position + 1) ∧
      sourceRank < event.position + 1 ∧
      ∀ stamp, WriteAt initial actions result profile offset stamp →
        stamp.cause.cell = changed.cell → stamp.position < event.position →
        stamp.position + 1 ≤ sourceRank := by
  obtain ⟨_target, sourceRank, _authority, _view, sourceRanked, ownRanked, sourceBefore⟩ :=
    EventAt.rmw_view_rank execution actual rmw
  have prefixRanked : WriterRank initial actions result profile offset changed.cell source
      (PublishedOrder.view (after offset (result.2.take index) empty) changed.cell) := by
    obtain ⟨_before, _action, _first, prefixRun, _actionAt, _observed, _stepped, access⟩ :=
      actual.prestate
    cases access with
    | load => cases rmw
    | store => cases rmw
    | rmw =>
        cases rmw
        exact publishedSource_prefix_rank execution.success prefixRun changed.cell
  have sameRank := WriterRank.unique execution.success execution.sequenced
    sourceRanked prefixRanked
  refine ⟨sourceRank, sourceRanked, ownRanked, sourceBefore, ?_⟩
  intro stamp written cell earlier
  have beforeCut : stamp.position < offset + index := by
    simpa only [actual.position] using earlier
  have bound := written.before_cut_view (incoming := empty) beforeCut
  simpa only [cell, ← sameRank] using bound

/-- Reading the initial boundary excludes every actual earlier publication to
the RMW's cell. Rank zero is not treated as a fictitious pre-run write. -/
theorem EventAt.rmw_initial_no_prior_write {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {changed : Atomics64.FetchAddEvent}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (rmw : event.access = .rmw changed (.initial changed.cell)) :
    ∀ stamp, WriteAt initial actions result profile offset stamp →
      stamp.cause.cell = changed.cell → ¬ stamp.position < event.position := by
  obtain ⟨sourceRank, ranked, _ownRanked, _sourceBefore, prior⟩ :=
    EventAt.rmw_predecessor execution actual rmw
  have zero : sourceRank = 0 :=
    WriterRank.unique execution.success execution.sequenced ranked .initial
  intro stamp written cell earlier
  have bound := prior stamp written cell earlier
  omega

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
