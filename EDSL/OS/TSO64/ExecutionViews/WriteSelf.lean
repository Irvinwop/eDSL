/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.PublicationCovers
import EDSL.OS.TSO64.ExecutionViews.Transfer
import EDSL.OS.TSO64.C23Projection.AtomicTrace.AccessDomain

/-!
Exact publication ranks in a writing worker's immediate postview. A buffered
instruction selects its freshly appended managed entry, including its actual
occurrence and unique publication. An RMW has an empty own FIFO and is the last
observation of its actual successor prefix. Both constructions recover current
target authority from the real instruction and transport its complete resource
record back through the actual prefix.

The execution may start with nonempty mixed FIFOs and arbitrary incoming writer
metadata. The own write determines this postview without a prior-position
boundary on that metadata. Initial pending entries receive no instruction
origins. Equal words do not identify writers, and there is no bound on the
number of accesses in the finite execution.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

/-- Recover the actual managed enqueue and allocated occurrence from the
committed finish of an instruction issue. Both next-instruction and return
finishes install the complete appended FIFO and incremented counter. -/
theorem Issued.managed_postcursor {state : State} {action : Action}
    {result : State × Observation} {profile : Profile} {tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word} {current : Worker}
    (issued : Issued state action result profile tid (.managed reference value occurrence))
    (currentLive : result.1.workers[tid]? = some current) :
    ∃ prior, state.workers[tid]? = some prior ∧ occurrence = prior.nextStore ∧
      current.storeCursor = prior.storeCursor.enqueueManaged reference value := by
  cases issued with
  | ordinary _issuing _success live _fetched _effect _intent admission committed =>
      have allocated := admission.managed_occurrence rfl
      refine ⟨_, live, allocated, ?_⟩
      rw [allocated] at committed
      cases committed <;>
        exact congrArg Worker.storeCursor (Option.some.inj
          (currentLive.symm.trans (List.getElem?_set_self (List.getElem_of_getElem? live).1)))

/-- An actual indexed managed issue supplies its exact initial current
reference under its own worker's unchanged complete resource record. -/
theorem IssuedAt.initial_current {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      index initial actions result) :
    ∃ original, initial.workers[tid]? = some original ∧
      Queue.Current initial.world original.resources reference := by
  obtain ⟨_before, _action, _first, prefixRun, _actionAt, _stepped, actual⟩ := issued.prestate
  cases actual with
  | ordinary _issuing _success live _fetched _effect _intent admission _committed =>
      obtain ⟨original, originalLive, resources⟩ :=
        ExecutionViews.schedule_worker_origin prefixRun live
      have current := admission.valid.2
      rw [resources] at current
      exact ⟨original, originalLive,
        (ExecutionViews.schedule_current_iff prefixRun original.resources reference).mp current⟩

end EDSL.OS.TSO64.StoreHistory

namespace EDSL.OS.TSO64.PublishedHistory
open X86 StoreHistory C23Projection.AtomicTrace

/-- Every actual publication is the exact last writer for its cell at its
immediate successor prefix, independently of all incoming writer metadata. -/
theorem WriteAt.published_at_succ {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat} {stamp : Stamp}
    (publication : WriteAt initial actions result profile offset stamp) (incoming : Writers) :
    after offset (result.2.take (publication.index + 1)) incoming stamp.cause.cell = some stamp := by
  have bound : publication.index ≤ result.2.length :=
    Nat.le_of_lt (List.getElem_of_getElem? publication.observed).1
  have prefixLength : (result.2.take publication.index).length = publication.index := by
    simp only [List.length_take, Nat.min_eq_left bound]
  have split : result.2.take (publication.index + 1) =
      result.2.take publication.index ++ [publication.observation] := by
    rw [List.take_add]
    simp only [List.take_one, List.head?_drop, publication.observed, Option.toList]
  rw [split, after_append, prefixLength]
  change update (after offset (result.2.take publication.index) incoming)
    (offset + publication.index) publication.observation stamp.cause.cell = some stamp
  simpa only [← publication.position] using
    (update_written (writers := after offset (result.2.take publication.index) incoming)
      (position := offset + publication.index) publication.written)

/-- The full actual RMW observation also identifies its real successful step. -/
theorem WriteAt.rmw_stepped {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid : Nat}
    {event : Atomics64.FetchAddEvent}
    (publication : WriteAt initial actions result profile offset ⟨position, .rmw tid event⟩) :
    step publication.before publication.action profile =
      .ok (publication.next, .rmw tid event) := by
  have observed : publication.observation = .rmw tid event :=
    Option.some.inj (publication.observed.symm.trans publication.rmw_observed)
  simpa only [observed] using publication.stepped

/-- Actual guarded RMW authority recovers a complete current target and the
original worker that owns its unchanged resource record. No target, address or
rank is supplied as a premise. -/
theorem WriteAt.rmw_initial_current {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid : Nat}
    {event : Atomics64.FetchAddEvent}
    (publication : WriteAt initial actions result profile offset ⟨position, .rmw tid event⟩) :
    ∃ original target, initial.workers[tid]? = some original ∧
      Queue.Current initial.world original.resources target ∧ target.handle.cell = event.cell := by
  have access : AtomicStep publication.before publication.action
      (publication.next, .rmw tid event) profile position empty
      ⟨position, tid, .rmw event (publishedSource empty event.cell)⟩ :=
    .rmw rfl (step_origin publication.rmw_stepped)
  obtain ⟨_worker, target, live, current, related⟩ := access.authority
  obtain ⟨original, originalLive, resources⟩ :=
    ExecutionViews.schedule_worker_origin publication.prefixRun live
  rw [resources] at current
  exact ⟨original, target, originalLive,
    (ExecutionViews.schedule_current_iff publication.prefixRun original.resources target).mp current,
    related.1⟩

private theorem buffered_post_view_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset index position tid occurrence rank : Nat}
    {reference : Queue.ManagedRef} {value : Word} {incoming : Writers}
    (issued : IssuedAt profile tid (.managed reference value occurrence) index initial actions result)
    (publication : WriteAt initial actions result profile offset
      ⟨position, .buffered tid reference value occurrence⟩)
    (view : ExecutionViews.At initial actions result profile (index + 1)
      tid reference offset incoming rank) : rank = position + 1 := by
  rcases view with ⟨snapshot, source⟩
  obtain ⟨_before, _action, first, prefixRun, actionAt, stepped, actual⟩ := issued.prestate
  have stateEq := snapshot.state_after_step prefixRun actionAt stepped
  have currentLive : first.1.workers[tid]? = some snapshot.worker := by
    rw [← stateEq]
    exact snapshot.live
  obtain ⟨prior, _priorLive, allocated, cursor⟩ := actual.managed_postcursor currentLive
  have newest : StoreBuffer.Mixed.newestQWord (Queue.payload snapshot.worker.pending)
      reference.cell.address = some ⟨prior.pending.length, value⟩ := by
    change StoreBuffer.Mixed.newestQWord (Queue.payload snapshot.worker.storeCursor.pending)
      reference.cell.address = some ⟨prior.pending.length, value⟩
    rw [cursor]
    exact (Queue.SelectionOrder.fresh prior.storeCursor reference value).newest
  have selected : snapshot.worker.pending[prior.pending.length]? =
      some (.managed reference value occurrence) := by
    change snapshot.worker.storeCursor.pending[prior.pending.length]? = _
    rw [cursor, allocated]
    exact (Queue.SelectionOrder.fresh prior.storeCursor reference value).selected
  cases source with
  | published absent =>
      change StoreBuffer.Mixed.newestQWord (Queue.payload snapshot.worker.pending)
        reference.cell.address = none at absent
      rw [absent] at newest
      cases newest
  | @pending origin selection pendingPublication _cell =>
      have sameOrigin : origin = ⟨prior.pending.length, value⟩ :=
        Option.some.inj (selection.newest.symm.trans newest)
      subst origin
      have entries := Option.some.inj (selection.selected.symm.trans selected)
      have sameOccurrence : selection.occurrence = occurrence := (Queue.Entry.managed.inj entries).2.2
      have observed : result.2[publication.index]? =
          some (.drained tid (.managed reference value selection.occurrence)) := by
        simpa only [sameOccurrence] using publication.buffered_observed
      have sameIndex := (pendingPublication.unique publication.index reference value observed).1
      change offset + pendingPublication.index + 1 = position + 1
      rw [← sameIndex, ← publication.position]

/-- An instruction's own immediate postview is its exact actual publication
rank. Initial worker existence and complete current target authority are
derived from the actual issue or guarded RMW, rather than supplied by a caller.
Incoming writer metadata is arbitrary, including positions beyond this run. -/
theorem InstructionWriteAt.self_view {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset writeIndex : Nat} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (incoming : Writers) :
    ∃ original target, initial.workers[stamp.cause.tid]? = some original ∧
      Queue.Current initial.world original.resources target ∧
      target.handle.cell = stamp.cause.cell ∧
      Nonempty (ExecutionViews.At initial actions result profile (writeIndex + 1)
        stamp.cause.tid target offset incoming (stamp.position + 1)) := by
  cases stamp with
  | mk position cause =>
      cases cause with
      | buffered tid reference value occurrence =>
          obtain ⟨original, live, current⟩ := actual.actual.initial_current
          obtain ⟨rank, ⟨view⟩⟩ :=
            ExecutionViews.exists_at execution live (writeIndex + 1) current offset incoming
          have same := buffered_post_view_rank actual.actual actual.publication view
          subst rank
          exact ⟨original, reference, live, current, rfl, ⟨view⟩⟩
      | rmw tid event =>
          obtain ⟨original, target, live, current, cell⟩ := actual.publication.rmw_initial_current
          obtain ⟨_rank, ⟨view⟩⟩ :=
            ExecutionViews.exists_at execution live (writeIndex + 1) current offset incoming
          have sameIndex : writeIndex = actual.publication.index := actual.actual
          have prefixRun : schedule initial (actions.take writeIndex) profile =
              .ok (actual.publication.before, result.2.take writeIndex) := by
            simpa only [← sameIndex] using actual.publication.prefixRun
          have actionAt : actions[writeIndex]? = some actual.publication.action := by
            simpa only [← sameIndex] using actual.publication.actionAt
          have emptyQueue := view.snapshot.pending_empty_of_rmw prefixRun actionAt
            actual.publication.rmw_stepped
          have selected : after offset (result.2.take (writeIndex + 1)) incoming target.handle.cell =
              some ⟨position, .rmw tid event⟩ := by
            rw [cell, sameIndex]
            exact actual.publication.published_at_succ incoming
          have absent : StoreBuffer.Mixed.newestQWord (Queue.payload view.snapshot.worker.pending)
              target.cell.address = none := by
            rw [emptyQueue]
            rfl
          have self : ExecutionViews.At initial actions result profile (writeIndex + 1)
              tid target offset incoming (position + 1) := by
            refine ⟨view.snapshot, ?_⟩
            have source := ExecutionViews.Source.published (snapshot := view.snapshot)
              (target := target) (offset := offset) (incoming := incoming) absent
            simpa only [PublishedOrder.view, selected] using source
          exact ⟨original, target, live, current, cell, ⟨self⟩⟩

/-- Every actual postview through a current alias of the written cell has the
same exact rank. Current authority authenticates the alias's address; a
same-cell `At` witness alone would not establish that bridge. -/
theorem InstructionWriteAt.post_view_rank {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset writeIndex rank : Nat} {stamp : Stamp}
    {target : Queue.ManagedRef} {resources : Resources} {incoming : Writers}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (current : Queue.Current initial.world resources target)
    (cell : target.handle.cell = stamp.cause.cell)
    (view : ExecutionViews.At initial actions result profile (writeIndex + 1)
      stamp.cause.tid target offset incoming rank) : rank = stamp.position + 1 := by
  obtain ⟨_original, _writtenTarget, _live, writtenCurrent, writtenCell, ⟨self⟩⟩ :=
    InstructionWriteAt.self_view execution actual incoming
  exact view.unique (self.retarget_current writtenCurrent current (writtenCell.trans cell.symm))

end EDSL.OS.TSO64.PublishedHistory

#audit_edsl
