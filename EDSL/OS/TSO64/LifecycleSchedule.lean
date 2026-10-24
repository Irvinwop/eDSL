/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.LifecycleCohort
import EDSL.OS.TSO64.Stability

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Ordered resource records survive actual schedules under their selected profile
and instruction family. Initial capability separation therefore remains valid
at the current cleanup boundary, without a future resource-manifest premise.
-/

namespace EDSL.OS.TSO64

/-- Exact equality of the ordered current resource manifests. The proof checks
all original scheduler indices, including absence past the original endpoint;
contexts, phases and pending queues remain free to change. Both the profile and
locked-instruction family are the ones used by the actual schedule. -/
theorem schedule_resource_records {before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (actual : schedule before actions profile family = .ok result) :
    result.1.workers.map Worker.resources = before.workers.map Worker.resources := by
  apply List.ext_getElem?
  intro tid
  cases live : before.workers[tid]? with
  | none =>
    have originalBound : before.workers.length ≤ tid := List.getElem?_eq_none_iff.mp live
    have currentBound : result.1.workers.length ≤ tid := by
      rw [ScheduleTrace.workers_length actual]
      exact originalBound
    simp only [List.getElem?_map, List.getElem?_eq_none currentBound, live,
      Option.map_none]
  | some original =>
    obtain ⟨current, currentLive, retained⟩ := schedule_worker_resources actual live
    simp only [List.getElem?_map, currentLive, live, Option.map_some, retained]

/-- Transport independently supplied original separation to the actual cleanup
order, using exact resource-list equality. No later separation or resource
validity is assumed. -/
theorem schedule_retirement_separate {before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (actual : schedule before actions profile family = .ok result)
    (separate : before.workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources)) :
    result.1.workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources) := by
  have original : (before.workers.reverse.map Worker.resources).Pairwise Lifecycle.Separate :=
    List.pairwise_map.mpr separate
  have current : (result.1.workers.reverse.map Worker.resources).Pairwise Lifecycle.Separate := by
    simpa only [List.map_reverse, schedule_resource_records actual] using original
  exact List.pairwise_map.mp current

#print axioms schedule_resource_records
#print axioms schedule_retirement_separate

end EDSL.OS.TSO64

#audit_edsl
