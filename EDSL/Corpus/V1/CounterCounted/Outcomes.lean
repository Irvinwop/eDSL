/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.Conservation
import EDSL.OS.TSO64.ReturnPositions

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Package actual call responses using their original scheduler positions. A
returned initial slot has one real RET, and every own increment precedes that
RET in the complete observation list. The response RAX is the actual machine
value retained through its suffix; it is not a mathematical result for a void
call. ABI and safety frames remain separately proved inputs to this packaging.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation Concurrency


/-- Independent own-position membership authenticates an actual original RMW
lookup with the same scheduler tid, without assuming distinct event payloads. -/
theorem own_position_at {observations : List Observation} {tid index : Nat}
    (member : index ∈ Grading.ConcurrentTask.Counted64.ownPositions tid observations) :
    ∃ event : Atomics64.FetchAddEvent, observations[index]? = some (.rmw tid event) := by
  unfold Grading.ConcurrentTask.Counted64.ownPositions at member
  obtain ⟨call, callMember, selected⟩ := List.mem_filterMap.mp member
  by_cases sameThread : call.thread = tid
  · have sameIndex : call.id = index := by
      simpa only [sameThread, ↓reduceIte, Option.some.injEq] using selected
    have projected : call ∈ PositionHistory.incrementCalls observations := callMember
    rw [PositionHistory.incrementCalls_eq_map] at projected
    obtain ⟨occurrence, occurrenceMember, callEq⟩ := List.mem_map.mp projected
    have found := (PositionHistory.mem_occurrences_iff observations occurrence).mp occurrenceMember
    have thread : occurrence.tid = tid := by
      change occurrence.asCall.thread = tid
      rw [callEq]
      exact sameThread
    have position : occurrence.index = index := by
      change occurrence.asCall.id = index
      rw [callEq]
      exact sameIndex
    exact ⟨occurrence.event, by simpa only [thread, position] using found⟩
  · simp only [sameThread, ↓reduceIte] at selected
    cases selected

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {actions : List Action}
  {observations : List Observation}

/-- A previously proved actual return frame is packaged with the exact RET
origin and full-list ordering laws. The generic return theorem derives the
position from initial running and final returned phase; no position is input. -/
theorem outcome_of_frame
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations))
    (slot : Fin before.workers.length) {initial final : Worker}
    (entry : Spec.Entry (image compiler) target cell (requests slot) before initial)
    (frame : Grading.ConcurrentTask.Counted64.ReturnFrame before cut slot.val initial final) :
    Nonempty (Grading.ConcurrentTask.Counted64.Outcome (requests slot) before actions
      (cut, observations) slot.val) := by
  obtain ⟨index, _bound, observed, unique, prior, action, after, value,
    prefixRun, selected, actualStep, origin, suffixRun⟩ :=
    ReturnPositions.returned_position_of_final pre.valid actual frame.initialLive
      entry.running frame.live frame.phase
  obtain ⟨_world, _original, returnedWorker, _originalLive, returnedLive, returnedValue,
    returnedPhase, _resources, _pending, _nextStore⟩ := origin.frame
  obtain ⟨retained, retainedLive, saved⟩ :=
    ReturnPositions.schedule_saved suffixRun returnedLive returnedPhase
  have finalEq : final = retained := Option.some.inj (frame.live.symm.trans retainedLive)
  have finalValue : final.context.registers .rax = value := by
    rw [finalEq, saved.context]
    exact returnedValue
  have response : Return.ReturnOrigin prior action (after, .returned slot.val)
      slot.val (final.context.registers .rax) .ownedOnly .arithmetic := by
    rw [finalValue]
    exact origin
  exact ⟨{
    initial := initial
    final := final
    countExact := completed_count pre actual slot frame.live frame.phase
    returned := index
    responseBoundary := {
      prior := prior
      action := action
      next := (after, .returned slot.val)
      prefixRun := prefixRun
      selected := selected
      observed := observed
      actualStep := actualStep }
    responseObserved := rfl
    response := response
    uniqueResponse := unique
    beforeReturn := by
      intro position member
      obtain ⟨event, found⟩ := own_position_at member
      exact ReturnPositions.rmw_before_return pre.valid actual found observed
    frame := frame }⟩

#print axioms own_position_at
#print axioms outcome_of_frame

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
