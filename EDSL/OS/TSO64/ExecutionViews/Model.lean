/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.PendingViews

/-!
Views of one actual finite execution. A pending-own view retains the production
newest-qword selection and its exact eventual publication; otherwise the view
is the actual published-prefix position. These are offline ghost ranks, not
predictions that an arbitrary scheduler will finish. Resource authority supplies
the address/cell bridge and is kept separate from numerical queue integrity.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.ExecutionViews
open X86 PublishedHistory StoreHistory Queue.SelectionOrder

/-- A fixed successful finite execution with the invariants needed to recover
actual pending writers and their publications. No view, rank, graph or semantic
legality certificate is supplied by a caller. Incoming pending queues may be
nonempty provided their occurrences are sequenced. -/
structure Execution (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) : Prop where
  success : schedule initial actions profile = .ok result
  valid : WellFormed initial profile
  sequenced : Sequenced initial
  quiescent : Quiescent result.1

/-- The actual worker and state at a prefix of the fixed execution. -/
structure Cut (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (index tid : Nat) where
  state : State
  worker : Worker
  scheduled : schedule initial (actions.take index) profile = .ok (state, result.2.take index)
  live : state.workers[tid]? = some worker

/-- Current authority is preserved by the actual run, with the original full
reference and original resource record. It need not belong to the viewed worker. -/
theorem schedule_current {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {resources : Resources} {reference : Queue.ManagedRef}
    (success : schedule initial actions profile = .ok result)
    (current : Queue.Current initial.world resources reference) :
    Queue.Current result.1.world resources reference := by
  induction actions generalizing initial result with
  | nil =>
    have same : (initial, []) = result := Except.ok.inj success
    subst result
    exact current
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact ih (result := tail) following (((step_stable stepped).current resources reference).mpr current)

namespace Cut
variable {initial : State} {actions : List Action} {result : State × List Observation}
  {profile : Profile} {index tid : Nat}

theorem valid (execution : Execution initial actions result profile)
    (snapshot : Cut initial actions result profile index tid) :
    WellFormed snapshot.state profile :=
  schedule_wellFormed execution.valid snapshot.scheduled

theorem ordered (execution : Execution initial actions result profile)
    (snapshot : Cut initial actions result profile index tid) : snapshot.worker.storeCursor.Ordered :=
  schedule_sequenced execution.sequenced snapshot.scheduled snapshot.worker
    (List.mem_of_getElem? snapshot.live)

/-- Two successful descriptions of the same prefix expose the same state and
worker; endpoint values are never used to choose an intermediate execution. -/
theorem same (first second : Cut initial actions result profile index tid) :
    first.state = second.state ∧ first.worker = second.worker := by
  have states := congrArg Prod.fst (Except.ok.inj (first.scheduled.symm.trans second.scheduled))
  change first.state = second.state at states
  have worker : first.worker = second.worker := by
    have live := first.live
    rw [states] at live
    exact Option.some.inj (live.symm.trans second.live)
  exact ⟨states, worker⟩

end Cut

/-- The source of a prefix view. The pending branch preserves the complete
selected writer and its actual unique publication. Persistent cell identity is
explicit; it is derived from current authority by `exists_at` below. -/
inductive Source {initial : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} {index tid : Nat}
    (snapshot : Cut initial actions result profile index tid)
    (target : Queue.ManagedRef) (offset : Nat) (incoming : Writers) : Nat → Type where
  | published
      (absent : StoreBuffer.Mixed.newestQWord (payload snapshot.worker.pending)
        target.cell.address = none) :
      Source snapshot target offset incoming
        (PublishedOrder.view (after offset (result.2.take index) incoming) target.handle.cell)
  | pending {origin : StoreBuffer.Mixed.QWordOrigin}
      (selection : ManagedSelection snapshot.worker.storeCursor target.cell.address origin)
      (publication : PendingPublication initial actions result profile index tid
        selection.reference origin.value selection.occurrence)
      (cell : selection.reference.handle.cell = target.handle.cell) :
      Source snapshot target offset incoming (publication.rank offset)

/-- A view of an actual worker at an actual cut, including its full source
witness. Different proof witnesses cannot choose different numerical views. -/
structure At (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (index tid : Nat)
    (target : Queue.ManagedRef) (offset : Nat) (incoming : Writers) (value : Nat) where
  snapshot : Cut initial actions result profile index tid
  source : Source snapshot target offset incoming value

/-- Every existing worker has a view at every cut for a current managed target.
The target authority may come from any original resource record. Later bridges
from actual accesses must derive this domain premise from their real authority;
this theorem does not assume every registered cell has an accessible handle. -/
theorem exists_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    (execution : Execution initial actions result profile)
    {tid : Nat} {worker : Worker} (live : initial.workers[tid]? = some worker)
    (index : Nat) {resources : Resources} {target : Queue.ManagedRef}
    (current : Queue.Current initial.world resources target)
    (offset : Nat) (incoming : Writers) :
    ∃ value, Nonempty (At initial actions result profile index tid target offset incoming value) := by
  obtain ⟨before, prefixRun, _suffix⟩ := ScheduleTrace.cut execution.success index
  obtain ⟨present, presentLive⟩ := schedule_worker_present prefixRun live
  let snapshot : Cut initial actions result profile index tid := ⟨before, present, prefixRun, presentLive⟩
  have valid := snapshot.valid execution
  have targetCurrent := schedule_current prefixRun current
  cases found : StoreBuffer.Mixed.newestQWord (payload present.pending) target.cell.address with
  | none =>
    exact ⟨_, ⟨snapshot, .published found⟩⟩
  | some origin =>
    obtain ⟨selection, selectedCurrent, _below⟩ := of_current valid
      (valid.2 present (List.mem_of_getElem? presentLive)) (snapshot.ordered execution) targetCurrent found
    obtain ⟨publication⟩ := PendingViews.selected_publication execution.success execution.sequenced
      prefixRun execution.quiescent presentLive selection
    have cell := selection.cell valid.1 selectedCurrent targetCurrent rfl
    exact ⟨_, ⟨snapshot, .pending selection publication cell⟩⟩

/-- A fixed snapshot/source has one numerical view. Equal payloads are never
used to equate the selected writer: the actual selector, exact tagged entry and
unique real publication fix the result. -/
theorem Source.unique {initial : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} {index tid offset firstValue secondValue : Nat}
    {snapshot : Cut initial actions result profile index tid} {target : Queue.ManagedRef}
    {incoming : Writers}
    (first : Source snapshot target offset incoming firstValue)
    (second : Source snapshot target offset incoming secondValue) : firstValue = secondValue := by
  cases first with
  | published absent =>
    cases second with
    | published => rfl
    | pending selection _publication _cell =>
      have impossible := selection.newest
      change StoreBuffer.Mixed.newestQWord (payload snapshot.worker.pending)
        target.cell.address = some _ at impossible
      rw [absent] at impossible
      cases impossible
  | @pending origin selection publication _cell =>
    cases second with
    | published absent =>
      have impossible := selection.newest
      change StoreBuffer.Mixed.newestQWord (payload snapshot.worker.pending)
        target.cell.address = some _ at impossible
      rw [absent] at impossible
      cases impossible
    | @pending otherOrigin otherSelection otherPublication _otherCell =>
      have origins : origin = otherOrigin :=
        Option.some.inj (selection.newest.symm.trans otherSelection.newest)
      subst otherOrigin
      have entries := Option.some.inj (selection.selected.symm.trans otherSelection.selected)
      have occurrences : selection.occurrence = otherSelection.occurrence :=
        (Queue.Entry.managed.inj entries).2.2
      have observed : result.2[otherPublication.index]? =
          some (.drained tid (.managed otherSelection.reference origin.value selection.occurrence)) := by
        simpa only [occurrences] using otherPublication.observed
      have position := (publication.unique _ _ _ observed).1
      simp only [PendingPublication.rank, PendingPublication.stamp]
      omega

/-- View equality also holds when prefix/worker witnesses were built
independently. Their states align by deterministic actual scheduling. -/
theorem At.unique {initial : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} {index tid offset firstValue secondValue : Nat}
    {target : Queue.ManagedRef} {incoming : Writers}
    (first : At initial actions result profile index tid target offset incoming firstValue)
    (second : At initial actions result profile index tid target offset incoming secondValue) :
    firstValue = secondValue := by
  rcases first with ⟨⟨firstState, firstWorker, firstRun, firstLive⟩, firstSource⟩
  rcases second with ⟨⟨secondState, secondWorker, secondRun, secondLive⟩, secondSource⟩
  have states : firstState = secondState :=
    congrArg Prod.fst (Except.ok.inj (firstRun.symm.trans secondRun))
  subst secondState
  have workers : firstWorker = secondWorker := Option.some.inj (firstLive.symm.trans secondLive)
  subst secondWorker
  exact firstSource.unique secondSource

end EDSL.OS.TSO64.ExecutionViews

#audit_edsl
