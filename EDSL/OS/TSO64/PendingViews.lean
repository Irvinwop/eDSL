/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Order
import EDSL.OS.TSO64.StoreHistory.PendingPublication
import EDSL.OS.TSO64.Queue.SelectionOrder
import EDSL.OS.TSO64.PublishedOrder

/-!
Actual publication ranks for pending-own selections at arbitrary execution cuts.
Final quiescence supplies each exact pending writer's real future publication.
Per-worker FIFO order then orders those ranks, independently of stored values,
references, cells, intervening ordinary entries and peer steps.

The production newest-qword selector dominates all same-address managed entries
in the actual snapshot, and hence their future publication ranks. Every already
published position view lies strictly below a still-pending writer's rank.
These are reusable finite-execution facts, not assumed view monotonicity.

Selection remains exact-address metadata: byte-load framing, current authority
and persistent-cell identification need the existing resource premises. This
module does not establish monotonicity across every pending/published transition,
release/acquire transfer, fairness, or universal C23 legality.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory.PendingPublication
open X86

/-- Future publication ranks order arbitrary pending writers of one worker by
their persistent occurrences. Cuts, references and words may differ. -/
theorem rank_lt_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {firstCut secondCut tid firstOccurrence secondOccurrence : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (first : PendingPublication state actions result profile firstCut tid
      firstReference firstValue firstOccurrence)
    (second : PendingPublication state actions result profile secondCut tid
      secondReference secondValue secondOccurrence)
    (sequenced : Sequenced state) (offset : Nat) :
    first.rank offset < second.rank offset ↔ firstOccurrence < secondOccurrence := by
  have order := managed_drain_order_iff first.execution sequenced first.observed second.observed
  simp only [rank, stamp]
  omega

/-- Nonstrict occurrence order also orders the actual publication ranks.
Equal occurrences retain a unique full drain identity, even at different cuts. -/
theorem rank_le_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {firstCut secondCut tid firstOccurrence secondOccurrence : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (first : PendingPublication state actions result profile firstCut tid
      firstReference firstValue firstOccurrence)
    (second : PendingPublication state actions result profile secondCut tid
      secondReference secondValue secondOccurrence)
    (sequenced : Sequenced state) (offset : Nat) :
    first.rank offset ≤ second.rank offset ↔ firstOccurrence ≤ secondOccurrence := by
  have reversed := second.rank_lt_iff first sequenced offset
  omega

/-- Any published position view at the pending cut precedes this writer's
actual future rank. Incoming stamps must predate the stream offset; no earlier
execution is invented for them. The statement holds for every target cell. -/
theorem published_view_lt_rank {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {cut tid occurrence offset : Nat} {reference : Queue.ManagedRef} {value : Word}
    (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    {writers : PublishedHistory.Writers} (prior : PublishedOrder.Prior offset writers)
    (target : Atomics64.CellId64) :
    PublishedOrder.view
      (PublishedHistory.after offset (result.2.take cut) writers) target <
        publication.rank offset := by
  have future := publication.rank_after_cut offset
  cases found : PublishedHistory.after offset (result.2.take cut) writers target with
  | none =>
    simp only [PublishedOrder.view, found]
    omega
  | some latest =>
    have past := PublishedOrder.prior_after (observations := result.2.take cut) prior target latest found
    have bounded : (result.2.take cut).length ≤ cut := List.length_take_le _ _
    simp only [PublishedOrder.view, found]
    omega

end EDSL.OS.TSO64.StoreHistory.PendingPublication

namespace EDSL.OS.TSO64.PendingViews
open X86 StoreHistory Queue.SelectionOrder

/-- Turn the actual newest managed selection at a real prefix state into its
unique future publication witness. Neither its drain index nor rank is input. -/
theorem selected_publication {state before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {cut tid : Nat}
    {worker : Worker} {address : Word} {origin : StoreBuffer.Mixed.QWordOrigin}
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (prefixRun : schedule state (actions.take cut) profile = .ok (before, result.2.take cut))
    (empty : Quiescent result.1) (live : before.workers[tid]? = some worker)
    (selection : ManagedSelection worker.storeCursor address origin) :
    Nonempty (PendingPublication state actions result profile cut tid
      selection.reference origin.value selection.occurrence) := by
  exact pending_managed_publication success sequenced prefixRun empty
    ⟨worker, live, List.mem_of_getElem? selection.selected⟩

/-- Newest-own selection dominates every same-address pending managed writer
by its actual future publication rank, including equal payloads. The other
writer's real future drain is derived from the complete successful run. -/
theorem selected_rank_dominates {state before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {cut tid : Nat}
    {worker : Worker} {address : Word} {origin : StoreBuffer.Mixed.QWordOrigin}
    (sequenced : Sequenced state)
    (prefixRun : schedule state (actions.take cut) profile = .ok (before, result.2.take cut))
    (empty : Quiescent result.1) (live : before.workers[tid]? = some worker)
    (selection : ManagedSelection worker.storeCursor address origin)
    (publication : PendingPublication state actions result profile cut tid
      selection.reference origin.value selection.occurrence)
    {index occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    (selected : worker.pending[index]? = some (.managed reference value occurrence))
    (sameAddress : reference.cell.address = address) (offset : Nat) :
    ∃ other : PendingPublication state actions result profile cut tid reference value occurrence,
      other.rank offset ≤ publication.rank offset ∧
      (index < origin.index → other.rank offset < publication.rank offset) := by
  have ordered := schedule_sequenced sequenced prefixRun worker (List.mem_of_getElem? live)
  have dominance := selection.dominates ordered selected sameAddress
  obtain ⟨other⟩ := pending_managed_publication publication.execution sequenced prefixRun empty
    ⟨worker, live, List.mem_of_getElem? selected⟩
  exact ⟨other, (other.rank_le_iff publication sequenced offset).mpr dominance.2.1,
    fun earlier => (other.rank_lt_iff publication sequenced offset).mpr (dominance.2.2 earlier)⟩

end EDSL.OS.TSO64.PendingViews

#audit_edsl
