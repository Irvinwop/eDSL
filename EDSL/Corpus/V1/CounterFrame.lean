/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCohort
import EDSL.Corpus.V1.CounterCohortClosure
import EDSL.OS.TSO64.EffectSimulation.Mixed.CohortFrame

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
No-other-writes contract for an actual finished pair of independently admitted
frozen GCC/Clang counter workers. A Bool cohort is constructed from the two
Pre proofs, with exact slots 0/1 and an exhaustive two-worker universe. Its
checked Entries and caller policy supply closure from initially empty queues.

Both actual returned workers' completed-event contracts authenticate every
observed cell target using the production schedule's issuer bound. Only cell
identities are passed to the generic frame: actual addresses are derived there
from checked OS authorization and the stable initial cell registry.

The imported target, resource, lifetime, protected-loan, synchronization and
translation assumptions remain. These conditional successful finite-run
theorems establish no termination, source/native refinement, corpus credit or
cost bound. Initial empty queues are an additional explicit frame premise.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Actual final RAM equals initial RAM at every byte outside the independent
common registered cell. No future frame, no-enqueue or desired value is input. -/
theorem two_completed_frame {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial final : S}
    (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1)
    (workerUniverse : initial.workers.length = 2) (empty : Quiescent initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations))
    {leftWorker rightWorker : Worker}
    (leftLive : final.workers[left.tid]? = some leftWorker)
    (rightLive : final.workers[right.tid]? = some rightWorker)
    (leftReturned : leftWorker.phase = .returned) (rightReturned : rightWorker.phase = .returned)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (registered : initial.world.cells target = some cell)
    (leftTarget : leftCall.target = target) (rightTarget : rightCall.target = target) :
    ∀ query : Word, 8 ≤ (query - cell.address).toNat →
      (published final.world).read query = (published initial.world).read query := by
  let subjects : Bool → CohortSubject initial := fun subject => match subject with
    | false => ⟨leftCompiler, left, leftCall, leftPre, leftProfile⟩
    | true => ⟨rightCompiler, right, rightCall, rightPre, rightProfile⟩
  let cohort := counterCohort subjects
  have covered : cohort.Covers initial := by
    intro tid worker live
    have bound := (List.getElem_of_getElem? live).1
    rw [workerUniverse] at bound
    have slots : tid = 0 ∨ tid = 1 := by omega
    rcases slots with rfl | rfl
    · exact ⟨false, leftSlot⟩
    · exact ⟨true, rightSlot⟩
  have entries : cohort.Entries initial := counterCohort_entries subjects
  have leftRun : TSO64.schedule initial actions left.profile .arithmetic =
      .ok (final, observations) := by rw [leftProfile]; exact actual
  have rightRun : TSO64.schedule initial actions right.profile .arithmetic =
      .ok (final, observations) := by rw [rightProfile]; exact actual
  have leftEvents := leftPre.completed_events leftRun leftLive leftReturned
  have rightEvents := rightPre.completed_events rightRun rightLive rightReturned
  have targets : ∀ tid event, Observation.rmw tid event ∈ observations → event.cell = target := by
    intro tid event member
    have bound := ScheduleTrace.rmw_tid_lt actual member
    rw [workerUniverse] at bound
    have slots : tid = 0 ∨ tid = 1 := by omega
    rcases slots with leftIssuer | rightIssuer
    · have observed : Observation.rmw left.tid event ∈ observations := by
        simpa only [leftSlot, leftIssuer] using member
      exact (leftEvents event observed).2.1.trans leftTarget
    · have observed : Observation.rmw right.tid event ∈ observations := by
        simpa only [rightSlot, rightIssuer] using member
      exact (rightEvents event observed).2.1.trans rightTarget
  exact cohort.schedule_frame covered entries empty registered targets actual

/-- Combine the independent no-other-writes contract with the existing actual
OS-history counter total. The only memory-value input is the initial read. -/
theorem two_completed_total_frame {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial final : S}
    (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1)
    (workerUniverse : initial.workers.length = 2) (empty : Quiescent initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations))
    {leftWorker rightWorker : Worker}
    (leftLive : final.workers[left.tid]? = some leftWorker)
    (rightLive : final.workers[right.tid]? = some rightWorker)
    (leftReturned : leftWorker.phase = .returned) (rightReturned : rightWorker.phase = .returned)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (registered : initial.world.cells target = some cell)
    (leftTarget : leftCall.target = target) (rightTarget : rightCall.target = target)
    (prior : Word)
    (readBefore : loadQWord (published initial.world) cell.address = .ok prior) :
    ∃ value,
      loadQWord (published final.world) cell.address = .ok value ∧
      value.toNat =
        (prior.toNat + leftCall.iterations.toNat + rightCall.iterations.toNat) % 2^64 ∧
      ∀ query : Word, 8 ≤ (query - cell.address).toNat →
        (published final.world).read query = (published initial.world).read query := by
  obtain ⟨value, readAfter, total⟩ := two_completed_total leftPre rightPre leftProfile rightProfile
    leftSlot rightSlot workerUniverse actual leftLive rightLive leftReturned rightReturned target cell
    registered leftTarget rightTarget prior readBefore
  exact ⟨value, readAfter, total, two_completed_frame leftPre rightPre leftProfile rightProfile
    leftSlot rightSlot workerUniverse empty actual leftLive rightLive leftReturned rightReturned
    target cell registered leftTarget rightTarget⟩

#print axioms two_completed_frame
#print axioms two_completed_total_frame

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
