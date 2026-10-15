/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Facts
import EDSL.OS.MutexTSO.TraceCore

namespace EDSL.OS.MutexTSO
open X86

/-- These actions publish existing writes without requesting user execution. -/
def DrainOnly (actions : List TSO.Action) : Prop :=
  ∀ action ∈ actions, ∃ identifier, action = .drain identifier

/-- Every successful drain-only suffix keeps the complete logical witness,
including all guards, phases, credits and loans. -/
theorem drain_schedule_stutters {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) {actions : List TSO.Action}
    (only : DrainOnly actions) {result : Physical × List TSO.Observation}
    (success : TSO.schedule physical actions = .ok result) :
    Rel config result.1 logical ∧ LiftTrace logical actions result.2 logical ∧
      retiredSelections result.2 = [] ∧ blockedCount result.2 = 0 := by
  induction actions generalizing physical result with
  | nil =>
    simp [TSO.schedule] at success
    cases success
    exact ⟨related, .nil, rfl, rfl⟩
  | cons action rest ih =>
    obtain ⟨identifier, rfl⟩ := only action (by simp)
    obtain ⟨head, tail, first, following, same⟩ := TSO.schedule_cons_ok _ _ _ _ success
    have drained : TSO.drain physical identifier = .ok head := first
    obtain ⟨_, store, _, _, _, _, _, headEq⟩ := TSO.drain_ok _ _ _ drained
    have onlyRest : DrainOnly rest := fun selected member => only selected (by simp [member])
    obtain ⟨finalRel, trace, projected, blocked⟩ := ih (related.drain drained) onlyRest following
    have observed : head.2 = .drained identifier store := by rw [headEq]
    rw [same, observed]
    exact ⟨finalRel, .cons (.drained identifier store) trace, projected, blocked⟩

/-- Every current FIFO has a concrete drain-only publication suffix. Its
length is the actual pending length and it cannot introduce a busy exchange,
retired instruction or blocked issue. This is an available finite path. -/
theorem publish_selected {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker) :
    ∃ result current,
      TSO.schedule physical (List.replicate worker.buffer.length (.drain identifier)) = .ok result ∧
      Rel config result.1 logical ∧
      result.1.workers[identifier]? = some current ∧ current.buffer = [] ∧
      current.context = worker.context ∧ current.returned = worker.returned ∧
      retiredSelections result.2 = [] ∧ TSO.retiredCount result.2 = 0 ∧
      TSO.atomicEvents result.2 = [] ∧ blockedCount result.2 = 0 := by
  obtain ⟨result, current, scheduled, found, empty, context, returned, _, retired, events⟩ :=
    TSO.publish_worker worker.buffer.length physical identifier worker
      related.buffers.pendingWritable live rfl
  have only : DrainOnly (List.replicate worker.buffer.length (.drain identifier)) := by
    intro action member
    exact ⟨identifier, List.eq_of_mem_replicate member⟩
  obtain ⟨finalRel, _, projected, blocked⟩ := drain_schedule_stutters related only scheduled
  exact ⟨result, current, scheduled, finalRel, found, empty, context, returned,
    projected, retired, events, blocked⟩

end EDSL.OS.MutexTSO
