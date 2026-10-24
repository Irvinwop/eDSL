/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.Outcomes

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Assemble the independent counted-call output from proved prefix safety and an
actual returned run. Response positions and complete history conservation are
derived from that same execution. This packaging does not itself establish
prefix safety or a candidate Claim; the candidate must supply those proofs.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation
open Grading.ConcurrentTask.Counted64 (SafePrefix Outcome Post)

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {actions : List Action}
  {observations : List Observation}

/-- Full same-run output, with one independently requested outcome per actual
original slot and exhaustive coverage of all actual RET labels. -/
theorem post_of_safe
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations))
    (safe : SafePrefix (image compiler) target cell before requests (cut, observations))
    (returned : Returned cut) :
    Nonempty (Post (image compiler) target cell before requests actions (cut, observations)) := by
  classical
  have outcomes : ∀ slot : Fin before.workers.length,
      Nonempty (Outcome (requests slot) before actions (cut, observations) slot.val) := by
    intro slot
    let data := slotData pre slot
    obtain ⟨final, _identifier, _handle, live, _resources, _valid, _nextStore,
      _selected, _selectedNow, _target, _code, _flags, _caller, complete⟩ :=
      safe.frames slot data.worker data.live
    have phase := returned final (List.mem_of_getElem? live)
    exact outcome_of_frame pre actual slot data.entry (complete phase).1
  let selectedOutcomes : (slot : Fin before.workers.length) →
      Outcome (requests slot) before actions (cut, observations) slot.val :=
    fun slot => Classical.choice (outcomes slot)
  have allReturns : ∀ index tid, observations[index]? = some (.returned tid) →
      ∃ slot : Fin before.workers.length, slot.val = tid ∧
        (selectedOutcomes slot).returned = index := by
    intro index tid observed
    obtain ⟨_prior, _action, _after, _value, prefixRun, _selected, _step, origin, _suffixRun⟩ :=
      ReturnPositions.returned_at pre.valid actual observed
    obtain ⟨_world, priorWorker, _current, priorLive, _currentLive, _returnedValue,
      _phase, _resources, _pending, _nextStore⟩ := origin.frame
    have bound : tid < before.workers.length := by
      rw [← ScheduleTrace.workers_length prefixRun]
      exact (List.getElem_of_getElem? priorLive).1
    let slot : Fin before.workers.length := ⟨tid, bound⟩
    exact ⟨slot, rfl, ((selectedOutcomes slot).uniqueResponse index observed).symm⟩
  obtain ⟨old, current, oldWord, currentWord, sequential, total⟩ :=
    completed_history pre actual returned
  exact ⟨{
    scheduled := actual
    safe := safe
    finished := ⟨returned, safe.empty⟩
    outcomes := selectedOutcomes
    allReturns := allReturns
    old := old
    current := current
    oldWord := oldWord
    currentWord := currentWord
    sequential := sequential
    total := total }⟩

#print axioms post_of_safe

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
