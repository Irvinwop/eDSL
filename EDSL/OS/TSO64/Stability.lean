/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Invariant
import EDSL.OS.TSO64.ScheduleTrace
import EDSL.OS.TSO64.Run
import EDSL.Audit

/-!
Resource metadata and permission stability across actual schedules under either
TSO64 authority profile. Published byte contents may change; footprint theorems
state their separate preservation obligations.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64

/-- Compose the actual metadata and per-address permission frames. -/
theorem Stable.trans {before middle after : World}
    (first : Stable before middle) (second : Stable middle after) : Stable before after :=
  ⟨second.allocations.trans first.allocations, second.frontier.trans first.frontier,
    second.loans.trans first.loans, second.nextLoan.trans first.nextLoan,
    second.cells.trans first.cells, second.nextCell.trans first.nextCell,
    second.handles.trans first.handles, second.nextHandle.trans first.nextHandle,
    second.legacyHandles.trans first.legacyHandles,
    second.legacyNextHandle.trans first.legacyNextHandle,
    fun query => (second.permissions query).trans (first.permissions query)⟩

/-- Every successful production schedule preserves resources and permissions.
Both the profile and locked-instruction family are arbitrary, including
sharedCell buffered publications and explicitly selected arithmetic LOCK. -/
theorem schedule_stable {before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    (success : schedule before actions profile family = .ok result) :
    Stable before.world result.1.world := by
  induction actions generalizing before result with
  | nil =>
    have same : (before, []) = result := Except.ok.inj success
    subst result
    exact Stable.refl _
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact (step_stable stepped).trans (ih (result := tail) following)

/-- Every actual initial slot remains present with its original resource
record, even when the context, phase and pending queue have changed. -/
theorem schedule_worker_resources {before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {initial : Worker}
    (success : schedule before actions profile family = .ok result)
    (live : before.workers[tid]? = some initial) :
    ∃ current, result.1.workers[tid]? = some current ∧ current.resources = initial.resources := by
  induction actions generalizing before result initial with
  | nil =>
    have same : (before, []) = result := Except.ok.inj success
    subst result
    exact ⟨initial, live, rfl⟩
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    have oneRun : schedule before [action] profile family = .ok (first.1, [first.2]) := by
      simp only [schedule, stepped, X86.ok_bind, X86.pure_ok]
    have bound : tid < first.1.workers.length := by
      rw [ScheduleTrace.workers_length oneRun]
      exact (List.getElem_of_getElem? live).1
    let middle : Worker := first.1.workers[tid]
    have middleLive : first.1.workers[tid]? = some middle := List.getElem?_eq_getElem bound
    have frame := step_resources stepped live middleLive
    obtain ⟨current, currentLive, retained⟩ := ih (result := tail) following middleLive
    exact ⟨current, by simpa only [same] using currentLive, retained.trans frame⟩

/-- Original resource identity and current authority hold at every successful
prefix of a well-formed execution, under the same profile and instruction family. -/
theorem schedule_current_resources {before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {initial : Worker}
    (valid : WellFormed before profile)
    (success : schedule before actions profile family = .ok result)
    (live : before.workers[tid]? = some initial) :
    ∃ current, result.1.workers[tid]? = some current ∧ current.resources = initial.resources ∧
      ResourcesValid result.1.world current.resources := by
  obtain ⟨current, currentLive, retained⟩ := schedule_worker_resources success live
  exact ⟨current, currentLive, retained,
    ((schedule_wellFormed valid success).2 current (List.mem_of_getElem? currentLive)).1⟩

#print axioms schedule_stable
#print axioms schedule_worker_resources
#print axioms schedule_current_resources

end EDSL.OS.TSO64

#audit_edsl
