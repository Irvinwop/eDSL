/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.PrefixEvents
import EDSL.OS.TSO64.PositionHistory

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Chronological full64 conservation for arbitrary independently admitted counted
populations. The current final word comes from the actual checked OS history;
exhaustive original scheduler slots connect its unit inputs to independent
requests. Reduction occurs only at the final 64-bit word. No selected-event
count, desired final value, serial permutation or physical observation is an
input to this proof.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation Concurrency

private theorem inputSum_relabel {width : Nat} {Id Thread Id' Thread' : Type}
    {left : List (ModuloCounter.Call width Id Thread)}
    {right : List (ModuloCounter.Call width Id' Thread')}
    (same : ModuloCounter.Forall₂ ModuloCounter.SameValues left right) :
    ModuloCounter.inputSum left = ModuloCounter.inputSum right := by
  induction same with
  | nil => rfl
  | cons pair _tail ih =>
    simp only [ModuloCounter.inputSum, pair.1, ih]

private theorem finRange_values (n : Nat) :
    ((List.finRange n).map Fin.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {actions : List Action}
  {observations : List Observation}

/-- Count every RMW exactly once through the exhaustive distinct original slots. -/
theorem completed_total_count
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations))
    (returned : Returned cut) :
    Mixed.EventCounts.totalRMW observations =
      Grading.ConcurrentTask.Counted64.requestedTotal requests := by
  let tids := (List.finRange before.workers.length).map Fin.val
  have distinct : tids.Nodup := by
    dsimp only [tids]
    rw [finRange_values]
    exact List.nodup_range
  have covered : ∀ tid event, Observation.rmw tid event ∈ observations → tid ∈ tids := by
    intro tid event member
    dsimp only [tids]
    rw [finRange_values]
    exact List.mem_range.mpr (ScheduleTrace.rmw_tid_lt actual member)
  have partition := Mixed.EventCounts.totalRMW_eq_sum_countRMW distinct covered
  change Mixed.EventCounts.totalRMW observations =
    (((List.finRange before.workers.length).map Fin.val).map
      (fun tid => Mixed.Counts.countRMW tid observations)).sum at partition
  rw [List.map_map] at partition
  change Mixed.EventCounts.totalRMW observations =
    ((List.finRange before.workers.length).map
      (fun slot => Mixed.Counts.countRMW slot.val observations)).sum at partition
  have counts : (List.finRange before.workers.length).map
      (fun slot => Mixed.Counts.countRMW slot.val observations) =
      (List.finRange before.workers.length).map (fun slot => (requests slot).toNat) := by
    apply List.map_congr_left
    intro slot _member
    have bound : slot.val < cut.workers.length := by
      rw [ScheduleTrace.workers_length actual]
      exact slot.isLt
    have live : cut.workers[slot.val]? = some (cut.workers[slot.val]'bound) :=
      List.getElem?_eq_getElem bound
    exact completed_count pre actual slot live (returned _ (List.mem_of_getElem? live))
  rw [counts] at partition
  exact partition

/-- Every original RMW remains in the chronological indexed call history.
Their unit inputs sum to the actual RMW count before slot partitioning. -/
theorem increment_input_sum
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations)) :
    ModuloCounter.inputSum (Grading.ConcurrentTask.Counted64.incrementCalls observations) =
      Mixed.EventCounts.totalRMW observations := by
  have increments : ∀ tid event, Observation.rmw tid event ∈ observations →
      event.cell = target ∧ event.arithmetic.delta = 1 := by
    intro tid event member
    obtain ⟨_slot, _tid, eventOK⟩ := prefix_event pre actual member
    exact ⟨eventOK.2.1, eventOK.2.2.2.1⟩
  have covered : ∀ tid event, Observation.rmw tid event ∈ observations → event.cell = target :=
    fun tid event member => (increments tid event member).1
  have relabeled := PositionHistory.selectedCalls_forall₂_incrementCalls target
    (fun _ => ()) (fun _ => ()) observations covered
  have sameSum := inputSum_relabel relabeled
  have total := Mixed.EventCounts.inputSum_selectedCalls_eq_totalRMW target
    (fun _ => ()) (fun _ => ()) observations increments
  exact sameSum.symm.trans total

/-- Same-run actual initial/current reads and indexed chronological legality,
with the final modular sum expressed using the independent original requests. -/
theorem completed_history
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations))
    (returned : Returned cut) :
    ∃ old current,
      loadQWord (published before.world) cell.address = .ok old ∧
      loadQWord (published cut.world) cell.address = .ok current ∧
      ModuloCounter.Sequential old (Grading.ConcurrentTask.Counted64.incrementCalls observations)
        current ∧
      current.toNat =
        (old.toNat + Grading.ConcurrentTask.Counted64.requestedTotal requests) % 2^64 := by
  obtain ⟨old, initialRead⟩ := pre.validCell.1.load_exists
  have covered : ∀ tid event, Observation.rmw tid event ∈ observations → event.cell = target := by
    intro tid event member
    obtain ⟨_slot, _tid, eventOK⟩ := prefix_event pre actual member
    exact eventOK.2.1
  obtain ⟨current, currentRead, legal⟩ := PositionHistory.schedule_sequential pre.valid actual
    target cell pre.liveTarget covered old initialRead
  refine ⟨old, current, initialRead, currentRead, legal, ?_⟩
  have total := legal.total
  change current.toNat =
    (old.toNat + ModuloCounter.inputSum
      (Grading.ConcurrentTask.Counted64.incrementCalls observations)) % 2^64 at total
  rw [increment_input_sum pre actual, completed_total_count pre actual returned] at total
  exact total

#print axioms inputSum_relabel
#print axioms finRange_values
#print axioms completed_total_count
#print axioms increment_input_sum
#print axioms completed_history

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
