/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Counted64.Contract
import EDSL.Corpus.V1.CounterCompletion

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Translate independent counted-call entry facts to the existing checked counter
annotations. Every actual scheduler slot is retained, with its original
worker, resource principal, low32 count and protected continuation. No manager
constructor, desired result, future schedule or proof annotation is required
from the caller. The finite ranked cohort is a proof-side consequence of the
fixed candidate bytes and present admission, not an extra behavioral premise.

This module establishes admission and initial invariants only. The independent
Counted64.Claim still requires its prefix, history, ABI and progress proofs.
The imported represented-memory, CET-off, protected-resource and translation
assumptions apply; physical CPU/OS and compiler correspondence remain separate.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation
namespace Spec
abbrev Pre := Grading.ConcurrentTask.Counted64.Pre
abbrev Entry := Grading.ConcurrentTask.Counted64.Entry
abbrev Requests := Grading.ConcurrentTask.Counted64.Requests
end Spec

/-- Exact complete callable symbol used by the existing checked annotation. -/
def image (compiler : CounterCommon.Compiler) : ScalarCall64.Image :=
  ⟨CounterCommon.base compiler, CounterMixedGraphs.bytes compiler⟩

/-- Current facts for one actual slot; data is selected from independent Pre. -/
structure SlotData (compiler : CounterCommon.Compiler) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (before : TSO64.State) (requests : Spec.Requests before)
    (slot : Fin before.workers.length) where
  worker : Worker
  live : before.workers[slot.val]? = some worker
  entry : Spec.Entry (image compiler) target cell (requests slot) before worker
  continuation : Word
  caller : Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
    worker.resources.caller.identifier worker.resources.callerAddress = .ok continuation
  canonical : X86.canonical continuation = true

/-- Select an actual listed worker and its current protected return address.
Classical choice selects only present witnesses, never a run or a result. -/
noncomputable def slotData {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests)
    (slot : Fin before.workers.length) : SlotData compiler target cell before requests slot := by
  classical
  let worker := Classical.choose (pre.entries slot)
  have facts := Classical.choose_spec (pre.entries slot)
  let continuation := Classical.choose facts.2.caller
  have returnFacts := Classical.choose_spec facts.2.caller
  exact ⟨worker, facts.1, facts.2, continuation, returnFacts.1, returnFacts.2⟩

/-- The existing site takes the actual original worker and its original loan. -/
def SlotData.site {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    {slot : Fin before.workers.length} (data : SlotData compiler target cell before requests slot) :
    CounterCommon.Site compiler where
  profile := .ownedOnly
  tid := slot.val
  original := data.worker
  codeLoan := data.entry.fits

/-- Count and target come from the independent inputs, with the actual caller. -/
def SlotData.call {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    {slot : Fin before.workers.length} (data : SlotData compiler target cell before requests slot) :
    CounterCommon.Call where
  address := cell.address
  iterations := requests slot
  target := target
  returnAddress := data.continuation

/-- Independent current facts satisfy the previous candidate admission exactly. -/
theorem SlotData.pre {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    {slot : Fin before.workers.length} (data : SlotData compiler target cell before requests slot)
    (valid : WellFormed before .ownedOnly) :
    CounterCommon.Pre data.site data.call before := by
  refine ⟨⟨valid, data.live, data.entry.running, data.entry.code, data.caller⟩,
    data.entry.pc, data.entry.pointer, data.entry.request,
    data.entry.originalRsp, data.canonical, ?_⟩
  obtain ⟨identifier, handle, selected, linked⟩ := data.entry.selected
  exact ⟨identifier, handle, cell, selected, linked⟩

/-- One independently admitted subject for each actual Fin slot. -/
noncomputable def subjects {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests) :
    Fin before.workers.length → CounterCommon.CohortSubject before := fun slot =>
  let data := slotData pre slot
  ⟨compiler, data.site, data.call, data.pre pre.valid, rfl⟩

/-- No supplied tid enumeration can omit or duplicate a physical worker slot. -/
theorem subjects_slots {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests) :
    ∀ slot, (subjects pre slot).site.tid = slot.val := fun _ => rfl

/-- All local rules and rank laws follow from the actual candidate admission. -/
noncomputable def cohort {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests) :
    Mixed.RankedCohort before.workers.length .ownedOnly .arithmetic :=
  CounterCommon.counterRankedCohort (subjects pre) (subjects_slots pre)

/-- Exact entry ghosts, initialized independently of any future trace. -/
noncomputable def ghosts {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests) : (cohort pre).Ghosts before :=
  CounterCommon.counterInitialGhosts (subjects pre) (subjects_slots pre)

theorem current {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests) :
    (cohort pre).Current before (ghosts pre) :=
  CounterCommon.counterInitialGhosts_current (subjects pre) (subjects_slots pre)

#print axioms image
#print axioms slotData
#print axioms SlotData.pre
#print axioms subjects_slots
#print axioms cohort
#print axioms ghosts
#print axioms current

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
