/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.Monotone

/-!
Numerical transfer of actual views between arbitrary workers in one successful
finite run. A worker's view covers the real published-prefix view. Consequently
an earlier view whose actual publication rank is already before a later cut is
covered by every worker's later view of the same persistent cell.

Pending sources retain their complete selected entries and real eventual
publications. Published sources retain the actual prefix map. Incoming stamps
must predate the supplied stream offset; initially nonempty mixed queues are
permitted and receive no invented instruction origins. Equal stored words are
never used to identify writers. Reference aliases may differ in their handles
provided their addresses and persistent cells agree.

These statements concern observation-position ranks in the fixed finite run.
They supply no source memory-order classification, synchronizes-with relation,
happens-before relation, C23 legality, fairness or native refinement.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.ExecutionViews
open X86 PublishedHistory StoreHistory Queue.SelectionOrder

/-- Every actual view covers the published-prefix view of its target cell.
An own-pending selection has a real future publication strictly beyond every
already published position; no assumption about empty initial queues is used. -/
theorem At.published_le {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {index tid offset value : Nat} {target : Queue.ManagedRef} {incoming : Writers}
    (view : At initial actions result profile index tid target offset incoming value)
    (prior : PublishedOrder.Prior offset incoming) :
    PublishedOrder.view (after offset (result.2.take index) incoming)
      target.handle.cell ≤ value := by
  rcases view with ⟨snapshot, source⟩
  cases source with
  | published _absent => exact Nat.le_refl _
  | pending _selection publication _cell =>
      exact Nat.le_of_lt (publication.published_view_lt_rank prior target.handle.cell)

/-- An earlier actual view is covered at a later cut of any worker once its
rank lies within that cut's observation boundary. In the pending case this
forces the retained exact writer's actual publication to precede the cut; in
the published case ordinary prefix monotonicity suffices. Target references
may differ, provided their persistent cells agree. -/
theorem At.le_of_rank_before_cut {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {first last firstTid lastTid offset firstValue lastValue : Nat}
    {firstTarget lastTarget : Queue.ManagedRef} {incoming : Writers}
    (earlier : At initial actions result profile first firstTid firstTarget
      offset incoming firstValue)
    (later : At initial actions result profile last lastTid lastTarget
      offset incoming lastValue)
    (prior : PublishedOrder.Prior offset incoming) (ordered : first ≤ last)
    (before : firstValue ≤ offset + last)
    (sameCell : firstTarget.handle.cell = lastTarget.handle.cell) :
    firstValue ≤ lastValue := by
  rcases earlier with ⟨snapshot, source⟩
  cases source with
  | published _absent =>
      have prefixBound := PublishedOrder.prefix_view (observations := result.2)
        prior ordered firstTarget.handle.cell
      have laterBound := later.published_le prior
      rw [← sameCell] at laterBound
      exact Nat.le_trans prefixBound laterBound
  | @pending origin selection publication cell =>
      have publishedBefore : publication.index < last := by
        simp only [PendingPublication.rank, PendingPublication.stamp] at before
        omega
      have selected : (result.2.take last)[publication.index]? =
          some (.drained firstTid (.managed selection.reference origin.value selection.occurrence)) := by
        simpa only [List.getElem?_take_of_lt publishedBefore] using publication.observed
      have published := publication_view_bound (offset := offset) (incoming := incoming)
        selected (by rfl : writeOf (.drained firstTid (.managed selection.reference origin.value
          selection.occurrence)) =
            some (.buffered firstTid selection.reference origin.value selection.occurrence))
      change offset + publication.index + 1 ≤
        PublishedOrder.view (after offset (result.2.take last) incoming)
          selection.reference.handle.cell at published
      rw [cell, sameCell] at published
      have bound := Nat.le_trans published (later.published_le prior)
      simpa only [PendingPublication.rank, PendingPublication.stamp] using bound

/-- Retarget an actual view to a legitimate reference alias while retaining
its exact cut, snapshot, selected entry and publication. Both address and
persistent-cell equality are explicit; handle or payload equality is unneeded.
This operation does not manufacture resource authority for the alias. -/
def At.retarget {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {index tid offset value : Nat} {target alias : Queue.ManagedRef} {incoming : Writers}
    (view : At initial actions result profile index tid target offset incoming value)
    (sameAddress : target.cell.address = alias.cell.address)
    (sameCell : target.handle.cell = alias.handle.cell) :
    At initial actions result profile index tid alias offset incoming value := by
  rcases view with ⟨snapshot, source⟩
  refine ⟨snapshot, ?_⟩
  cases source with
  | published absent =>
      have aliasAbsent : StoreBuffer.Mixed.newestQWord (payload snapshot.worker.pending)
          alias.cell.address = none := by
        simpa only [sameAddress] using absent
      simpa only [sameCell] using
        (Source.published (target := alias) (offset := offset) (incoming := incoming) aliasAbsent)
  | @pending origin selection publication cell =>
      let aliasSelection : ManagedSelection snapshot.worker.storeCursor alias.cell.address origin := {
        reference := selection.reference
        occurrence := selection.occurrence
        selected := selection.selected
        address := selection.address.trans sameAddress
        newest := by simpa only [sameAddress] using selection.newest
      }
      exact .pending aliasSelection publication (cell.trans sameCell)

/-- Current aliases of the same persistent cell have the same complete cell
descriptor. Authorization supplies the address equality used by `retarget`;
neither equal payloads nor caller-supplied address equality identify the cell. -/
def At.retarget_current {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {index tid offset value : Nat} {target alias : Queue.ManagedRef} {incoming : Writers}
    {targetResources aliasResources : Resources}
    (view : At initial actions result profile index tid target offset incoming value)
    (current : Queue.Current initial.world targetResources target)
    (aliasCurrent : Queue.Current initial.world aliasResources alias)
    (sameCell : target.handle.cell = alias.handle.cell) :
    At initial actions result profile index tid alias offset incoming value := by
  have original := current.cell
  rw [sameCell] at original
  have descriptor : target.cell = alias.cell :=
    Option.some.inj (original.symm.trans aliasCurrent.cell)
  exact view.retarget (congrArg Atomics64.Cell.address descriptor) sameCell

end EDSL.OS.TSO64.ExecutionViews

#audit_edsl
