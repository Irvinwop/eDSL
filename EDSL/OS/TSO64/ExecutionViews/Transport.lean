/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.Model
import EDSL.OS.TSO64.ScheduleTrace

/-!
Backward authority transport along the production scheduler. A successful
finite schedule preserves exact managed authorization in both directions and
every worker's original resource record. These facts need no world invariant,
queue sequencing, quiescent boundary, publication map or view certificate.

The scheduler has a fixed worker universe and stable authority metadata. Its
actions do not allocate worker slots, change grants or revoke authorization;
these results do not describe lifecycle or resource-revocation operations.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.ExecutionViews
open StoreHistory

/-- Current authority for the complete retained descriptor is an equivalence
across an actual successful schedule, for any original resource record. -/
theorem schedule_current_iff {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    (success : schedule initial actions profile = .ok result)
    (resources : Resources) (reference : Queue.ManagedRef) :
    Queue.Current result.1.world resources reference ↔
      Queue.Current initial.world resources reference := by
  induction actions generalizing initial result with
  | nil =>
      have same : (initial, []) = result := Except.ok.inj success
      subst result
      exact Iff.rfl
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
      rw [same]
      exact (ih following).trans ((step_stable stepped).current resources reference)

/-- A live final slot comes from an actual initial worker with the very same
resource record. Slot existence follows from the scheduler's fixed worker
length; resource equality follows from its real successful step effects. -/
theorem schedule_worker_origin {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid : Nat} {current : Worker}
    (success : schedule initial actions profile = .ok result)
    (live : result.1.workers[tid]? = some current) :
    ∃ original, initial.workers[tid]? = some original ∧
      current.resources = original.resources := by
  induction actions generalizing initial result with
  | nil =>
      have same : (initial, []) = result := Except.ok.inj success
      subst result
      exact ⟨current, live, rfl⟩
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
      have tailLive : tail.1.workers[tid]? = some current := by
        simpa only [same] using live
      obtain ⟨middle, middleLive, resources⟩ := ih following tailLive
      have bound : tid < initial.workers.length := by
        have finalBound := (List.getElem_of_getElem? live).1
        rw [ScheduleTrace.workers_length success] at finalBound
        exact finalBound
      let original : Worker := initial.workers[tid]'bound
      have originalLive : initial.workers[tid]? = some original :=
        List.getElem?_eq_getElem bound
      exact ⟨original, originalLive,
        resources.trans (step_resources stepped originalLive middleLive)⟩

end EDSL.OS.TSO64.ExecutionViews

#audit_edsl
