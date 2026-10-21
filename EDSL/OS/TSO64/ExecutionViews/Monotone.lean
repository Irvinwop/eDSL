/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.Model

/-!
General monotonicity of actual own-pending/published views across any two cuts.
Exact-entry conservation over the actual intervening execution avoids assuming
view order or restricting the number of accesses per worker. A retained writer
is dominated by the later newest selection. A writer that has drained is already
covered by the published view, and precedes every still-pending publication.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.ExecutionViews
open X86 PublishedHistory StoreHistory Queue.SelectionOrder

/-- The real successful interval between two independently described cuts.
All observation positions, including silent actions, are retained. -/
theorem Cut.interval {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {first last tid : Nat}
    (earlier : Cut initial actions result profile first tid)
    (later : Cut initial actions result profile last tid) (ordered : first ≤ last) :
    schedule earlier.state ((actions.take last).drop first) profile =
      .ok (later.state, (result.2.take last).drop first) := by
  have prefixRun : schedule initial ((actions.take last).take first) profile =
      .ok (earlier.state, (result.2.take last).take first) := by
    simpa only [List.take_take, Nat.min_eq_left ordered] using earlier.scheduled
  exact (ScheduleTrace.suffix later.scheduled prefixRun).2

/-- A real observation in the interval has an original global position before
its upper cut. No filtered-event index is used as an action position. -/
theorem interval_observation {observations : List Observation} {first last : Nat}
    {observation : Observation} (member : observation ∈ (observations.take last).drop first) :
    ∃ index, index < last ∧ observations[index]? = some observation := by
  obtain ⟨localIndex, selected⟩ := List.mem_iff_getElem?.mp member
  have selectedPrefix : (observations.take last)[first + localIndex]? = some observation := by
    simpa only [List.getElem?_drop] using selected
  have bound := (List.getElem_of_getElem? selectedPrefix).1
  have before : first + localIndex < last := Nat.lt_of_lt_of_le bound (List.length_take_le _ _)
  exact ⟨first + localIndex, before,
    by simpa only [List.getElem?_take_of_lt before] using selectedPrefix⟩

/-- Any actual publication in an observation list is represented by its final
published writer, even after later equal-valued writes. This fact imposes no
condition on incoming metadata because the actual write replaces it. -/
private theorem write_present {offset index : Nat} {observations : List Observation}
    {incoming : Writers} {observation : Observation} {cause : WriteCause}
    (selected : observations[index]? = some observation)
    (written : writeOf observation = some cause) :
    ∃ latest, after offset observations incoming cause.cell = some latest := by
  induction observations generalizing offset index incoming with
  | nil => simp at selected
  | cons head tail ih =>
    cases index with
    | zero =>
      have same : head = observation := Option.some.inj selected
      subst head
      have present : update incoming offset observation cause.cell = some ⟨offset, cause⟩ :=
        update_written written
      exact PublishedOrder.present_after (observations := tail) present
    | succ index =>
      exact ih selected

/-- Actual publication rank is bounded by the later published view. This
includes an initially absent map, real equal-valued writes and silent steps. -/
theorem publication_view_bound {offset index : Nat} {observations : List Observation}
    {incoming : Writers} {observation : Observation} {cause : WriteCause}
    (selected : observations[index]? = some observation)
    (written : writeOf observation = some cause) :
    offset + index + 1 ≤ PublishedOrder.view (after offset observations incoming) cause.cell := by
  obtain ⟨latest, found⟩ := write_present (offset := offset) (incoming := incoming) selected written
  have bound := PublishedOrder.dominates_write found selected written rfl
  simp only [PublishedOrder.view, found]
  omega

/-- Every pending/published view is monotone across arbitrary ordered cuts of
one actual finite execution. Pending sources retain their real publications;
no numerical view-order premise or one-access-per-thread restriction appears.
The incoming map must predate the stream offset. Domain existence for current
managed targets is supplied separately by `exists_at`. -/
theorem At.monotone {initial : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} {first last tid offset firstValue lastValue : Nat}
    {target : Queue.ManagedRef} {incoming : Writers}
    (execution : Execution initial actions result profile)
    (prior : PublishedOrder.Prior offset incoming) (ordered : first ≤ last)
    (earlier : At initial actions result profile first tid target offset incoming firstValue)
    (later : At initial actions result profile last tid target offset incoming lastValue) :
    firstValue ≤ lastValue := by
  rcases earlier with ⟨firstSnapshot, firstSource⟩
  rcases later with ⟨lastSnapshot, lastSource⟩
  cases firstSource with
  | published _absent =>
    cases lastSource with
    | published _absent => exact PublishedOrder.prefix_view prior ordered target.handle.cell
    | pending _selection publication _cell =>
      have published := PublishedOrder.prefix_view (observations := result.2) prior ordered target.handle.cell
      exact Nat.le_trans published (Nat.le_of_lt (publication.published_view_lt_rank prior target.handle.cell))
  | @pending origin selection publication cell =>
    have queued : Queued firstSnapshot.state tid
        (.managed selection.reference origin.value selection.occurrence) :=
      ⟨firstSnapshot.worker, firstSnapshot.live, List.mem_of_getElem? selection.selected⟩
    have interval := firstSnapshot.interval lastSnapshot ordered
    rcases schedule_pending_retained_or_drained interval queued with retained | drained
    · obtain ⟨worker, live, member⟩ := retained
      have same : worker = lastSnapshot.worker := Option.some.inj (live.symm.trans lastSnapshot.live)
      subst worker
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
      cases lastSource with
      | published absent =>
        exact False.elim (missing_excludes_managed (cursor := lastSnapshot.worker.storeCursor)
          absent selected selection.address)
      | pending otherSelection otherPublication _cell =>
        have dominance := otherSelection.dominates (lastSnapshot.ordered execution) selected selection.address
        exact (publication.rank_le_iff otherPublication execution.sequenced offset).mpr dominance.2.1
    · obtain ⟨index, bound, observed⟩ := interval_observation drained
      have sameIndex : index = publication.index := (publication.unique _ _ _ observed).1
      cases lastSource with
      | published _absent =>
        have selected : (result.2.take last)[index]? =
            some (.drained tid (.managed selection.reference origin.value selection.occurrence)) := by
          simpa only [List.getElem?_take_of_lt bound] using observed
        have published := publication_view_bound (offset := offset) (incoming := incoming)
          selected (by rfl : writeOf (.drained tid (.managed selection.reference origin.value
            selection.occurrence)) = some (.buffered tid selection.reference origin.value selection.occurrence))
        change offset + index + 1 ≤ PublishedOrder.view (after offset (result.2.take last) incoming)
          selection.reference.handle.cell at published
        rw [cell] at published
        simpa only [PendingPublication.rank, PendingPublication.stamp, ← sameIndex] using published
      | pending _otherSelection otherPublication _cell =>
        have future := otherPublication.future
        simp only [PendingPublication.rank, PendingPublication.stamp]
        omega

/-- In particular no actual scheduler step lowers a view, including blocked
attempts, peer publications, returns and transitions from own pending to RAM. -/
theorem At.step {initial : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} {index tid offset firstValue nextValue : Nat}
    {target : Queue.ManagedRef} {incoming : Writers}
    (execution : Execution initial actions result profile)
    (prior : PublishedOrder.Prior offset incoming)
    (earlier : At initial actions result profile index tid target offset incoming firstValue)
    (later : At initial actions result profile (index + 1) tid target offset incoming nextValue) :
    firstValue ≤ nextValue :=
  earlier.monotone execution prior (Nat.le_succ index) later

end EDSL.OS.TSO64.ExecutionViews

#audit_edsl
