/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.PendingViews
import tests.TSO64SharedCells
import EDSL.Audit

/-!
A successful mixed-FIFO execution with repeated same-worker stores. An ordinary
store consumes occurrence zero, two equal managed stores remain distinct, and
a peer publishes before and between their drains. All states below are checked
outputs of the production scheduler; no final state or desired publication is
supplied to it. The tests exercise issue/publication separation, exact newest
pending identity, actual future drain positions and agreement across real cuts.

The imported sharedCell, scalar RAM, long-mode, CET-off and resource assumptions
remain in force. These finite-trace clients establish no C23 legality, fairness,
compiler correspondence or native execution result.
-/

set_option autoImplicit false

namespace EDSL.Tests.PendingPublicationViews
open X86 OS.TSO64 StoreHistory

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private def found {α : Type} (value : Option α) (present : value.isSome = true) : α :=
  value.get present

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (found value present) := by
  cases value with
  | none => cases present
  | some value => rfl

/-- MOV [RDX],RAX; MOV [RDI],RSI; MOV [RDI],RSI; RET. The peer starts
at the first managed store. Shared payload zero differs from initial RAM nine. -/
def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x8948378948028948 0x000000000000c337 9 0 0 0 3

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel

def initial : OS.TSO64.State := checked initialAttempt initial_succeeds

/-- Actual own and peer issues, a peer publication, RET with own stores queued,
then mixed drains and another peer publication between the two own drains. -/
def actions : List Action :=
  [.issue 0 false, .issue 0 true, .issue 1 false, .issue 0 false,
    .drain 1, .issue 0 false, .drain 0, .drain 0,
    .issue 1 true, .drain 1, .drain 0, .issue 1 false]

def attempt : Except Fault (OS.TSO64.State × List Observation) :=
  schedule initial actions .sharedCell

theorem execution_succeeds : attempt.toOption.isSome = true := by decide +kernel

def result : OS.TSO64.State × List Observation := checked attempt execution_succeeds

theorem scheduled : schedule initial actions .sharedCell = .ok result :=
  checked_ok attempt execution_succeeds

-- Prefix extraction follows successful execution for every index, including
-- indices past the end. It does not add an assumed successful intermediate run.
private theorem prefix_succeeds (cut : Nat) :
    (schedule initial (actions.take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut scheduled cut
  rw [success]
  rfl

def atCut (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule initial (actions.take cut) .sharedCell) (prefix_succeeds cut)

theorem prefix_scheduled (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell = .ok (atCut cut) :=
  checked_ok _ _

theorem prefix_exact (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell =
      .ok ((atCut cut).1, result.2.take cut) := by
  have same := (ScheduleTrace.suffix scheduled (prefix_scheduled cut)).1
  rw [← same]
  exact prefix_scheduled cut

private theorem quiescent_of_empty_pending {state : OS.TSO64.State}
    (empty : state.workers.map Worker.pending = [[], []]) : Quiescent state := by
  intro worker member
  have mapped : worker.pending ∈ state.workers.map Worker.pending :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  rw [empty] at mapped
  simpa using mapped

theorem initial_quiescent : Quiescent initial :=
  quiescent_of_empty_pending (by decide +kernel)

theorem initial_sequenced : Sequenced initial := by
  intro worker member
  have empty := initial_quiescent worker member
  simp [Worker.storeCursor, Queue.Cursor.Ordered, empty]

theorem final_quiescent : Quiescent result.1 :=
  quiescent_of_empty_pending (by decide +kernel)

def publisher : Worker := found ((atCut 4).1.workers[0]?) (by decide +kernel)

theorem publisher_live : (atCut 4).1.workers[0]? = some publisher := found_ok _ _

private def managedReference (entry : Pending) : Option Queue.ManagedRef :=
  match entry with
  | .ordinary _ _ => none
  | .managed reference _ _ => some reference

/-- Retain the actual descriptor produced by admission, rather than recover a
writer from its zero payload or construct a handle from an address. -/
def ownReference : Queue.ManagedRef :=
  found (publisher.pending[1]?.bind managedReference) (by decide +kernel)

theorem first_pending : publisher.pending[1]? = some (.managed ownReference 0 1) := by
  decide +kernel

theorem newest_pending : publisher.pending[2]? = some (.managed ownReference 0 2) := by
  decide +kernel

theorem own_address : ownReference.cell.address = 65536 := by decide +kernel

theorem first_queued : Queued (atCut 4).1 0 (.managed ownReference 0 1) :=
  ⟨publisher, publisher_live, List.mem_of_getElem? first_pending⟩

theorem newest_queued : Queued (atCut 4).1 0 (.managed ownReference 0 2) :=
  ⟨publisher, publisher_live, List.mem_of_getElem? newest_pending⟩

theorem publisher_ordered : publisher.storeCursor.Ordered :=
  schedule_sequenced initial_sequenced (prefix_scheduled 4) publisher
    (List.mem_of_getElem? publisher_live)

/-- The production selector distinguishes equal payloads by the actual newest
snapshot entry and persistent occurrence, despite the earlier ordinary store. -/
private def managedSelection (worker : Worker) (reference : Queue.ManagedRef)
    (occurrence : Nat) (address : Word) (origin : StoreBuffer.Mixed.QWordOrigin)
    (selected : worker.pending[origin.index]? = some (.managed reference origin.value occurrence))
    (sameAddress : reference.cell.address = address)
    (newest : StoreBuffer.Mixed.newestQWord (Queue.payload worker.pending) address = some origin) :
    Queue.SelectionOrder.ManagedSelection worker.storeCursor address origin :=
  ⟨reference, occurrence, selected, sameAddress, newest⟩

def ownSelection : Queue.SelectionOrder.ManagedSelection publisher.storeCursor 65536 ⟨2, 0⟩ :=
  managedSelection publisher ownReference 2 65536 ⟨2, 0⟩ newest_pending own_address (by decide +kernel)

private theorem worker_dominates {worker : Worker} {address : Word}
    {origin : StoreBuffer.Mixed.QWordOrigin}
    (selection : Queue.SelectionOrder.ManagedSelection worker.storeCursor address origin)
    (ordered : worker.storeCursor.Ordered) {index occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (selected : worker.pending[index]? = some (.managed reference value occurrence))
    (sameAddress : reference.cell.address = address) :
    index ≤ origin.index ∧ occurrence ≤ selection.occurrence ∧
      (index < origin.index → occurrence < selection.occurrence) :=
  selection.dominates ordered selected sameAddress

/-- Any actual same-address pending writer is below the production-selected
one. This client quantifies over entries instead of assuming which old writer
will be selected or imposing a one-access-per-worker shape. -/
theorem every_pending_writer_below_newest {index occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (selected : publisher.pending[index]? = some (.managed reference value occurrence))
    (sameAddress : reference.cell.address = 65536) :
    index ≤ 2 ∧ occurrence ≤ 2 ∧ (index < 2 → occurrence < 2) := by
  simpa only [ownSelection, managedSelection] using
    worker_dominates ownSelection publisher_ordered selected sameAddress

/-- Removing the actual ordinary head retains the newest full descriptor and
persistent occurrence, while changing only its queue snapshot position. -/
theorem head_removal_retains_newest :
    ∃ index, 2 = index + 1 ∧
      StoreBuffer.Mixed.newestQWord (Queue.payload publisher.storeCursor.dropHead.pending) 65536 =
        some ⟨index, 0⟩ ∧
      publisher.storeCursor.dropHead.pending[index]? = some (.managed ownReference 0 2) := by
  rcases ownSelection.dropHead.2 with removed | retained
  · have impossible : 2 = 0 := removed.1
    omega
  · simpa only [ownSelection, managedSelection] using retained

/-- RAM changes only at publication. The local newest entry remains pending
across the peer's first publication, RET and the ordinary drain. The neighboring
shared word and the peer's disjoint owned allocation remain framed. -/
theorem issue_and_publication_are_separate :
    ((atCut 4).1.workers[0]?.map (fun worker => (Queue.occurrences worker.pending, worker.nextStore))) =
        some ([1, 2], 3) ∧
      (loadQWord (published (atCut 4).1.world) 65536).toOption = some 9 ∧
      (loadQWord (published (atCut 7).1.world) 65536).toOption = some 0 ∧
      (loadQWord (published (atCut 7).1.world) 131072).toOption = some 5 ∧
      (loadQWord (published result.1.world) 196608).toOption = some 0 ∧
      (loadQWord (published result.1.world) 65544).toOption = some 0xabcdef0123456789 := by
  decide +kernel

/-- The same exact newer writer is still present at a later real execution
cut, after the ordinary head and a peer's publication have taken effect. -/
theorem newest_queued_later : Queued (atCut 7).1 0 (.managed ownReference 0 2) := by
  let worker : Worker := found ((atCut 7).1.workers[0]?) (by decide +kernel)
  refine ⟨worker, found_ok _ _, ?_⟩
  have atIndex : worker.pending[1]? = some (.managed ownReference 0 2) := by decide +kernel
  exact List.mem_of_getElem? atIndex

/-- A literal independently specified publication trajectory catches a
mistaken issue-time stamp, a lost equal-value write or wrong-thread drain. -/
theorem actual_managed_publication_positions :
    result.2[4]?.map (fun observation => match observation with
      | .drained tid (.managed _ value occurrence) => some (tid, occurrence, value)
      | _ => none) = some (some (1, 0, 0)) ∧
      result.2[7]? = some (.drained 0 (.managed ownReference 0 1)) ∧
      result.2[10]? = some (.drained 0 (.managed ownReference 0 2)) := by
  decide +kernel

/-- The general pending-publication construction supplies real future drains,
strict FIFO publication order and graph-input stamps for both equal-valued own
writers. The same writer at a later cut has exactly the same publication.
Nothing here accepts desired ranks or publications as an execution premise. -/
theorem pending_writers_have_actual_ordered_future_publications :
    ∃ first : PendingPublication initial actions result .sharedCell 4 0 ownReference 0 1,
    ∃ latest : PendingPublication initial actions result .sharedCell 4 0 ownReference 0 2,
    ∃ later : PendingPublication initial actions result .sharedCell 7 0 ownReference 0 2,
      first.index = 7 ∧ latest.index = 10 ∧ later.index = latest.index ∧
      37 + 4 < first.rank 37 ∧ 37 + 7 < later.rank 37 ∧
      first.rank 37 < latest.rank 37 ∧
      first.stamp 37 ∈ C23Projection.writes 37 result.2 ∧
      latest.stamp 37 ∈ C23Projection.writes 37 result.2 ∧
      (∀ index, index < 4 →
        result.2[index]? ≠ some (.drained 0 (.managed ownReference 0 2))) := by
  obtain ⟨first⟩ := pending_managed_publication scheduled initial_sequenced
    (prefix_exact 4) final_quiescent first_queued
  obtain ⟨latest⟩ := pending_managed_publication scheduled initial_sequenced
    (prefix_exact 4) final_quiescent newest_queued
  obtain ⟨later⟩ := pending_managed_publication scheduled initial_sequenced
    (prefix_exact 7) final_quiescent newest_queued_later
  have firstAt := actual_managed_publication_positions.2.1
  have latestAt := actual_managed_publication_positions.2.2
  have firstIndex : first.index = 7 := (first.unique 7 ownReference 0 firstAt).1.symm
  have latestIndex : latest.index = 10 := (latest.unique 10 ownReference 0 latestAt).1.symm
  have ordered := managed_drain_index_lt scheduled initial_sequenced
    first.observed latest.observed (by decide : 1 < 2)
  have ranks : first.rank 37 < latest.rank 37 := by
    simp only [PendingPublication.rank, PendingPublication.stamp]
    omega
  exact ⟨first, latest, later, firstIndex, latestIndex,
    (latest.same_occurrence later).1, first.rank_after_cut 37, later.rank_after_cut 37,
    ranks, first.stamp_mem_writes 37, latest.stamp_mem_writes 37,
    fun index earlier => latest.no_past_drain earlier ownReference 0⟩

/-- The integration API derives an actual selected publication, places all
already-published views below it, and bounds every real same-address pending
writer. No selected publication position is provided to this construction. -/
theorem selected_rank_bounds :
    ∃ latest : PendingPublication initial actions result .sharedCell 4 0
      ownSelection.reference 0 ownSelection.occurrence,
      (∀ cell, PublishedOrder.view
        (PublishedHistory.after 37 (result.2.take 4) PublishedHistory.empty) cell < latest.rank 37) ∧
      (∀ index occurrence reference value,
        publisher.pending[index]? = some (.managed reference value occurrence) →
        reference.cell.address = 65536 →
        ∃ other : PendingPublication initial actions result .sharedCell 4 0 reference value occurrence,
          other.rank 37 ≤ latest.rank 37 ∧ (index < 2 → other.rank 37 < latest.rank 37)) := by
  obtain ⟨latest⟩ := PendingViews.selected_publication scheduled initial_sequenced
    (prefix_exact 4) final_quiescent publisher_live ownSelection
  refine ⟨latest, fun cell => latest.published_view_lt_rank (PublishedOrder.prior_empty 37) cell, ?_⟩
  intro index occurrence reference value selected sameAddress
  exact PendingViews.selected_rank_dominates initial_sequenced (prefix_exact 4)
    final_quiescent publisher_live ownSelection latest selected sameAddress 37

/-- At the later cut a peer's real publication has advanced the shared view
to 42. The retained own writer still has a strictly greater actual future rank,
despite holding the same word as the published peer. -/
theorem nonzero_peer_view_below_retained_writer :
    ∃ latest : PendingPublication initial actions result .sharedCell 7 0 ownReference 0 2,
      PublishedOrder.view
        (PublishedHistory.after 37 (result.2.take 7) PublishedHistory.empty)
        ownReference.handle.cell = 42 ∧ 42 < latest.rank 37 := by
  obtain ⟨latest⟩ := pending_managed_publication scheduled initial_sequenced
    (prefix_exact 7) final_quiescent newest_queued_later
  have view : PublishedOrder.view
      (PublishedHistory.after 37 (result.2.take 7) PublishedHistory.empty)
      ownReference.handle.cell = 42 := by decide +kernel
  refine ⟨latest, view, ?_⟩
  have bound := latest.published_view_lt_rank (PublishedOrder.prior_empty 37) ownReference.handle.cell
  simpa only [view] using bound

/-- A cut past the final action is the completed boundary, with no manufactured
suffix action or observation. The result uses the same successful execution. -/
theorem past_end_cut_has_empty_suffix :
    schedule (atCut 99).1 (actions.drop 99) .sharedCell = .ok (result.1, []) := by
  have suffix := (ScheduleTrace.suffix scheduled (prefix_exact 99)).2
  have empty : result.2.drop 99 = [] := by
    apply List.drop_eq_nil_iff.mpr
    have length := ScheduleTrace.length scheduled
    rw [length]
    decide
  exact suffix.trans (congrArg (fun observations => Except.ok (result.1, observations)) empty)

end EDSL.Tests.PendingPublicationViews

#print axioms EDSL.Tests.PendingPublicationViews.scheduled
#print axioms EDSL.Tests.PendingPublicationViews.every_pending_writer_below_newest
#print axioms EDSL.Tests.PendingPublicationViews.issue_and_publication_are_separate
#print axioms EDSL.Tests.PendingPublicationViews.pending_writers_have_actual_ordered_future_publications
#print axioms EDSL.Tests.PendingPublicationViews.selected_rank_bounds
#print axioms EDSL.Tests.PendingPublicationViews.nonzero_peer_view_below_retained_writer
#print axioms EDSL.Tests.PendingPublicationViews.past_end_cut_has_empty_suffix
#audit_edsl
