/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Completion
import EDSL.OS.MutexTSO.Accounting

namespace EDSL.OS.MutexTSO
open X86 AddressSpace

/-- A no-busy entry execution attains the lower bound while publishing each
of its two stores per worker. Fifteen counts model actions, thirteen counts
retired instructions; neither is a hardware time or micro-operation bound. -/
theorem entry_action_completion {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) :
    ∃ actions result,
      TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result ∧
      TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
      blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 = 13 * state.workers.length ∧
      drainCount result.2 = 2 * state.workers.length ∧ actions.length = 15 * state.workers.length ∧
      CompletedResult config state initial result := by
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired, outcome⟩ :=
    entry_completion admitted
  have drained := completed_drains admitted scheduled finished.1
  have count := completed_action_count admitted scheduled finished.1
  rw [noBusy, noBlocked] at count
  exact ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired, drained, by omega, outcome⟩

/-- Positive collection is also available from an arbitrary related state,
without any original-entry value witness. The collected full memory equals
physical RAM and exactly the current cohort's original loans are revoked. -/
theorem completion_collection {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config) :
    ∃ actions result finalState collected,
      TSO.schedule physical actions = .ok result ∧ TSO.Finished result.1 ∧
      MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧ blockedCount result.2 = 0 ∧
      TSO.retiredCount result.2 = MutexReplay.potentialSum logical ∧
      TSO.retiredCount result.2 ≤ 15 * logical.workers.length ∧
      MutexReplay.schedule logical (retiredSelections result.2) = .ok (finalState, TSO.atomicEvents result.2) ∧
      Rel config result.1 finalState ∧ MutexReplay.collect finalState = .ok collected ∧
      toMemory collected.1.shared.resources.space = result.1.memory ∧
      ∀ loanId, collected.1.shared.loans loanId =
        if loanId ∈ MutexReplay.cohortLoanIds logical.workers then none else logical.shared.shared.loans loanId := by
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired, bound⟩ := completion related closed
  obtain ⟨finalState, replayed, finalRel⟩ := schedule_lifts related closed scheduled
  have ready : MutexReplay.LoanReady finalState := MutexReplay.executionReady_loanReady _ finalRel.ready
  obtain ⟨collected, joined⟩ := MutexReplay.collect_enabled finalState
    (finalRel.invariant.completed (finalRel.returned_finished finished.1)) ready
  refine ⟨actions, result, finalState, collected, scheduled, finished, noBusy, noBlocked,
    retired, bound, replayed, finalRel, joined, ?_, ?_⟩
  · rw [(MutexReplay.collect_resources _ _ joined).1]
    exact (finalRel.quiescent_memory finished.2).symm
  · intro loanId
    have loans : finalState.shared.shared.loans = logical.shared.shared.loans :=
      MutexReplay.schedule_loans _ _ _ replayed
    have identifiers : MutexReplay.cohortLoanIds finalState.workers =
        MutexReplay.cohortLoanIds logical.workers := MutexReplay.schedule_loanIds _ _ _ replayed
    simpa only [identifiers, loans] using MutexReplay.collect_loans _ _ joined loanId

/-- A completing schedule needs at least fifteen abstract actions per entry
worker: thirteen retirements and two actual publications. This is a bound on
schedules of the fixed routine, excluding loader, runtime and kernel work. -/
theorem completed_action_minimum {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {actions : List TSO.Action}
    {result : Physical × List TSO.Observation}
    (success : TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result)
    (returned : TSO.Returned result.1) : 15 * state.workers.length ≤ actions.length := by
  have count := completed_action_count admitted success returned
  omega

end EDSL.OS.MutexTSO
