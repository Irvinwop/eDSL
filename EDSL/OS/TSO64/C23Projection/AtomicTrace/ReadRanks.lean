/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.WriterRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.AccessDomain
import EDSL.OS.TSO64.ExecutionViews.Monotone

/-!
Exact source-writer publication ranks for actual managed reads. A view is the
rank of the writer read by an access, rather than the graph row of the access.
Forwarded sources keep their full selected tag and actual future publication;
published sources keep the actual prefix's latest writer or initial boundary.

The complete finite execution is successful, initially well formed/sequenced
and finally quiescent. The incoming publication map is empty: a numerical
prior-position condition alone does not authenticate arbitrary incoming writers.
These results establish no source-order preservation, universal C23 legality,
native x86/Linux refinement, scheduler fairness or lifecycle guarantee.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86 PublishedHistory StoreHistory Queue.SelectionOrder

/-- The exact source of a real local load has the view's actual writer rank.
The pending case is derived from the selected full tag and eventual real drain,
without a rank, publication position or view witness supplied by the caller. -/
theorem LoadSource.view_rank {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {cut tid offset : Nat} {worker : Worker} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (prefixRun : schedule initial (actions.take cut) profile =
      .ok (before, result.2.take cut))
    (live : before.workers[tid]? = some worker)
    (current : Queue.Current before.world worker.resources target)
    (read : LoadSource before worker tid target value
      (after offset (result.2.take cut) empty) source) :
    ∃ rank, Nonempty (ExecutionViews.At initial actions result profile cut tid
      target offset empty rank) ∧
      WriterRank initial actions result profile offset target.handle.cell source rank := by
  let snapshot : ExecutionViews.Cut initial actions result profile cut tid :=
    ⟨before, worker, prefixRun, live⟩
  cases read with
  | published absent _loaded =>
      exact ⟨_, ⟨snapshot, .published absent⟩,
        publishedSource_prefix_rank execution.success prefixRun target.handle.cell⟩
  | forwarded selector writer occurrence newest entry payload address writerCurrent _below =>
      subst value
      let selection : ManagedSelection worker.storeCursor target.cell.address selector :=
        ⟨writer, occurrence, entry, address, newest⟩
      obtain ⟨publication⟩ := PendingViews.selected_publication execution.success
        execution.sequenced prefixRun execution.quiescent live selection
      have cell := selection.cell (schedule_wellFormed execution.valid prefixRun).1
        writerCurrent current rfl
      obtain ⟨written⟩ := publication.writeAt offset
      have ranked := WriterRank.publication written cell
      refine ⟨publication.rank offset,
        ⟨snapshot, ExecutionViews.Source.pending (snapshot := snapshot)
          (target := target) (offset := offset) (incoming := empty) selection publication cell⟩, ?_⟩
      simpa only [PendingPublication.stamp, PendingPublication.rank, Graph.publicationKey]
        using ranked

/-- An actual annotated load supplies its own authority and prestate; callers
do not supply a view-domain or source-rank oracle. The event's original action
index remains distinct from its index in a filtered atomic-event list. -/
theorem EventAt.load_view_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (loaded : event.access = .load target value source) :
    ∃ rank, Nonempty (ExecutionViews.At initial actions result profile index event.tid
      target offset empty rank) ∧
      WriterRank initial actions result profile offset target.handle.cell source rank := by
  obtain ⟨before, action, first, prefixRun, _actionAt, _observed, _stepped, access⟩ :=
    actual.prestate
  cases access with
  | load origin live read =>
      cases loaded
      cases origin with
      | intro _issuing originLive _fetched _effect _shared _ordinaryAbsent _selected current _operand _loaded =>
          have workers := Option.some.inj (originLive.symm.trans live)
          rw [workers] at current
          exact read.view_rank execution prefixRun live current
  | store => cases loaded
  | rmw => cases loaded

/-- The production LOCK gate leaves no own pending store at a successful RMW.
This is extracted from actual execution, independently of writer metadata. -/
private theorem actual_rmw_empty {state next : State} {action : Action}
    {profile : Profile} {tid : Nat}
    {changed : Atomics64.FetchAddEvent}
    (stepped : step state action profile = .ok (next, .rmw tid changed)) :
    ∃ worker, state.workers[tid]? = some worker ∧ worker.pending = [] := by
  cases step_origin stepped with
  | ordinary _live _running _code _caller _fetched effect =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | rmw live _running _code _caller _fetched _bounds empty _grant _effect =>
      exact ⟨_, live, empty⟩

/-- An actual RMW reads the exact published-prefix writer and publishes its
own modification at its original action position. Its source rank is strictly
smaller than its own rank; silent actions and other-cell publications may leave
gaps, so this is not adjacency of action numbers. -/
theorem EventAt.rmw_view_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {changed : Atomics64.FetchAddEvent}
    {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset empty)
    (rmw : event.access = .rmw changed source) :
    ∃ target rank, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid
        target offset empty rank) ∧
      WriterRank initial actions result profile offset changed.cell source rank ∧
      WriterRank initial actions result profile offset changed.cell
        (.rmw event.position) (event.position + 1) ∧
      rank < event.position + 1 := by
  obtain ⟨before, action, first, prefixRun, actionAt, observedAt, stepped, access⟩ :=
    actual.prestate
  cases access with
  | load => cases rmw
  | store => cases rmw
  | @rmw tid _changed observed origin =>
      cases rmw
      obtain ⟨worker, target, live, current, targetAt⟩ :=
        (AtomicStep.rmw (position := offset + index)
          (writers := after offset (result.2.take index) empty) observed origin).authority
      have rmwStep : step before action profile = .ok (first.1, .rmw tid changed) := by
        simpa only [← observed] using stepped
      obtain ⟨own, ownLive, pendingEmpty⟩ := actual_rmw_empty rmwStep
      have workers : own = worker := Option.some.inj (ownLive.symm.trans live)
      subst own
      have absent : StoreBuffer.Mixed.newestQWord (Queue.payload worker.pending)
          target.cell.address = none := by
        simp only [pendingEmpty, Queue.payload, List.map_nil, StoreBuffer.Mixed.newestQWord]
      let snapshot : ExecutionViews.Cut initial actions result profile index tid :=
        ⟨before, worker, prefixRun, live⟩
      have cell : target.handle.cell = changed.cell := targetAt.1
      have sourceRank := publishedSource_prefix_rank (offset := offset)
        execution.success prefixRun changed.cell
      let written : WriteAt initial actions result profile offset
          ⟨offset + index, .rmw tid changed⟩ :=
        ⟨index, first.2, before, action, first.1, rfl, observedAt,
          prefixRun, actionAt, stepped, by simp only [observed, writeOf]⟩
      have ownRank := WriterRank.publication (target := changed.cell) written rfl
      have prior := PublishedOrder.prior_after (observations := result.2.take index)
        (PublishedOrder.prior_empty offset)
      have sourceBefore : PublishedOrder.view
          (after offset (result.2.take index) empty) changed.cell < offset + index + 1 := by
        cases found : after offset (result.2.take index) empty changed.cell with
        | none => simp only [PublishedOrder.view, found]; omega
        | some stamp =>
            have bound := prior changed.cell stamp found
            have length := List.length_take_le index result.2
            simp only [PublishedOrder.view, found]
            omega
      refine ⟨target, _, targetAt, ?_, sourceRank, ?_, sourceBefore⟩
      · refine ⟨snapshot, ?_⟩
        simpa only [cell] using
          (ExecutionViews.Source.published (offset := offset) (incoming := empty)
            (snapshot := snapshot) (target := target) absent)
      · simpa only [Graph.publicationKey] using ownRank

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
