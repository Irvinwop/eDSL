/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.PrefixEvents
import EDSL.OS.TSO64.CellFrame
import EDSL.OS.TSO64.RMWSelection
import EDSL.OS.TSO64.EffectSimulation.Mixed.RetirementTrace

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Complete RAM-cell frames and actual ordered-handle provenance at every
successful prefix of an independently admitted counted-call population.
Caller-only cohort closure derives the absence of drains; every actual RMW
is authenticated before applying the general memory effect theorem. No
future frame or issue-only trace premise is added to independent admission.
The imported represented-memory, authority and translation assumptions apply;
these modeled effects establish no physical CPU/OS or compiler refinement.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {actions : List Action}
  {observations : List Observation}

/-- Classify all original scheduler positions from present caller-only rules. -/
theorem retirement_trace
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations)) :
    (cohort pre).toCohort.RetirementTrace actions observations := by
  obtain ⟨_empty, _covered, _current, retiring⟩ :=
    (cohort pre).toCohort.schedule_from_current ((cohort pre).covers rfl)
      ((cohort pre).current_toCohort (current pre)) pre.empty actual
  exact retiring

/-- Full optional cells, including permissions and inaccessible stored bytes,
are unchanged outside the common qword throughout any successful prefix. -/
theorem prefix_memory
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations)) :
    ∀ address, ¬(AddressSpace.qwordRegion cell.address).Contains address →
      cut.world.legacy.shared.resources.space.cells address =
        before.world.legacy.shared.resources.space.cells address := by
  have targets : ∀ tid event, Observation.rmw tid event ∈ observations → event.cell = target := by
    intro tid event member
    obtain ⟨slot, _slotTid, eventOK⟩ := prefix_event pre actual member
    exact eventOK.2.1
  exact CellFrame.schedule_frame pre.liveTarget
    (retirement_trace pre actual).no_drains targets actual

/-- The exact handle named by an actual RMW is the first matching initial
ordered selection, with the original slot's resource principal and target.
Current authority is transported through this very step's real prefix. -/
theorem prefix_increment
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations))
    {index tid : Nat} {event : Atomics64.FetchAddEvent}
    (observed : observations[index]? = some (.rmw tid event)) :
    ∃ slot : Fin before.workers.length, slot.val = tid ∧
      ∃ (initial : Worker) (handle : Atomics64.Handle),
        before.workers[slot.val]? = some initial ∧ event.actor = initial.resources.actor ∧
        atomicFor before.world initial.resources cell.address = some (event.handle, handle, cell) ∧
        handle.cell = target ∧ event.cell = target ∧ event.arithmetic.event.address = cell.address ∧
        event.arithmetic.delta = 1 ∧
        Concurrency.ModuloCounter.Step event.arithmetic.event.before event.arithmetic.delta
          event.arithmetic.event.before event.arithmetic.event.after := by
  obtain ⟨slot, slotTid, eventOK⟩ := prefix_event_at pre actual observed
  let data := slotData pre slot
  obtain ⟨prior, action, next, prefixRun, _actionAt, actualStep⟩ :=
    ScheduleTrace.observation_at actual observed
  obtain ⟨worker, handle, selectedCell, live, selected, linked, _address, _actor⟩ :=
    rmw_selection actualStep
  obtain ⟨retained, retainedLive, resources⟩ := schedule_worker_resources prefixRun data.live
  have retainedAtTid : prior.workers[tid]? = some retained := by
    rw [← slotTid]
    exact retainedLive
  have sameWorker : worker = retained := Option.some.inj (live.symm.trans retainedAtTid)
  have workerResources : worker.resources = data.worker.resources := by
    rw [sameWorker]
    exact resources
  have priorSelection : atomicFor before.world data.worker.resources cell.address =
      some (event.handle, handle, selectedCell) := by
    rw [workerResources, eventOK.2.2.1] at selected
    rw [(schedule_stable prefixRun).atomicFor] at selected
    exact selected
  obtain ⟨identifier, originalHandle, originalSelection, _originalTarget⟩ := data.entry.selected
  have equalSelection : (event.handle, handle, selectedCell) = (identifier, originalHandle, cell) :=
    Option.some.inj (priorSelection.symm.trans originalSelection)
  have sameCell : selectedCell = cell := congrArg (fun entry => entry.2.2) equalSelection
  subst selectedCell
  refine ⟨slot, slotTid, data.worker, handle, data.live, eventOK.1, priorSelection,
    linked.trans eventOK.2.1, eventOK.2.1, eventOK.2.2.1, eventOK.2.2.2.1, ?_⟩
  apply Concurrency.ModuloCounter.step_iff.mpr
  refine ⟨rfl, ?_⟩
  rw [eventOK.2.2.2.1]
  exact eventOK.2.2.2.2

/-- No original observation is blocked or drained in an admitted successful
prefix. This is derived from actual closure, rather than a filtered log. -/
theorem prefix_retired
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations)) :
    ∀ seen ∈ observations, seen.retired = 1 :=
  (retirement_trace pre actual).all_retired

#print axioms retirement_trace
#print axioms prefix_memory
#print axioms prefix_increment
#print axioms prefix_retired

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
