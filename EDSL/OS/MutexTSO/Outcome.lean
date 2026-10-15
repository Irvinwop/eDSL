/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Coverage

namespace EDSL.OS.MutexTSO
open X86 AddressSpace

/-- Direct observations of a completed physical run. Completion observes the
actual RET flags; publication is a conclusion for this byte profile. -/
structure CompletedResult (config : Mutex.Config) (initialState : Logical)
    (initial : BitVec 32) (result : Physical × List TSO.Observation) : Prop where
  quiescent : TSO.Quiescent result.1
  cohort : result.1.workers.length = initialState.workers.length
  returns : ∀ worker ∈ result.1.workers, worker.context.registers .rax = 0
  unlocked : loadDWord result.1.memory config.lockAddress = .ok 0
  total : loadDWord result.1.memory config.dataAddress =
    .ok (initial + BitVec.ofNat 32 (2 * initialState.workers.length))
  retired : TSO.retiredCount result.2 =
    13 * initialState.workers.length + 4 * MutexReplay.busyCount (TSO.atomicEvents result.2)

/-- Every completing physical schedule establishes the modular total, full
return registers and exact retired-instruction count against the independent
entry contract. No successful logical replay is an assumption. -/
theorem completed_observations {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {actions : List TSO.Action}
    {result : Physical × List TSO.Observation}
    (success : TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result)
    (returned : TSO.Returned result.1) : CompletedResult config state initial result := by
  obtain ⟨finalState, replayed, related⟩ := schedule_lifts
    (Rel.initial admitted.invariant admitted.ready admitted.profile) admitted.closed success
  have finished := related.returned_finished returned
  have empty := related.returned_quiescent returned
  have memoryEq := related.quiescent_memory empty
  obtain ⟨record, present, configured, free⟩ := related.invariant.unheld finished
  have phase := (related.invariant.shared.2 record present).phase
  rw [free, configured] at phase
  refine ⟨empty, ?_, ?_, ?_, ?_, ?_⟩
  · exact related.length.trans (MutexReplay.schedule_trace _ _ _ replayed).length
  · intro physical member
    obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨logical, found, contextEq, _⟩ := related.physical_live live
    have control := (related.invariant.workers identifier logical found).control
    have facts : logical.guard = none ∧ logical.context.registers .rax = 0 := by
      simpa only [MutexReplay.Control, finished identifier logical found] using control
    rw [contextEq]
    exact facts.2
  · rw [memoryEq]
    exact phase.1
  · rw [memoryEq]
    exact MutexReplay.completed_total _ _ _ _ _ admitted.invariant admitted.closed
      admitted.entry admitted.observed replayed finished
  · have cost := MutexReplay.completed_cost _ _ _ admitted.invariant.controlled admitted.entry
      replayed (related.invariant.completed finished)
    rw [retiredSelections_length] at cost
    exact cost

/-- Collection succeeds from retained code/stack loans. Its entire memory
projection equals physical RAM; exactly the original cohort's loans are
revoked, and every other loan record is retained. -/
theorem completed_collection_exists {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {actions : List TSO.Action}
    {result : Physical × List TSO.Observation}
    (success : TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result)
    (returned : TSO.Returned result.1) :
    ∃ finalState collected,
      MutexReplay.schedule state (retiredSelections result.2) = .ok (finalState, TSO.atomicEvents result.2) ∧
      Rel config result.1 finalState ∧
      MutexReplay.collect finalState = .ok collected ∧
      MutexReplay.CollectedOutcome state config initial collected ∧
      toMemory collected.1.shared.resources.space = result.1.memory ∧
      ∀ loanId, collected.1.shared.loans loanId =
        if loanId ∈ MutexReplay.cohortLoanIds state.workers then none else state.shared.shared.loans loanId := by
  obtain ⟨finalState, replayed, related⟩ := schedule_lifts
    (Rel.initial admitted.invariant admitted.ready admitted.profile) admitted.closed success
  have ready : MutexReplay.LoanReady state := fun identifier worker live =>
    (admitted.ready identifier worker live).loans
  obtain ⟨collected, joined, outcome, loans⟩ := MutexReplay.completed_collection_exists _ _ _ _ _
    admitted.invariant ready admitted.closed admitted.entry admitted.observed replayed
    (related.returned_finished returned)
  refine ⟨finalState, collected, replayed, related, joined, outcome, ?_, loans⟩
  rw [(MutexReplay.collect_resources _ _ joined).1]
  exact (related.quiescent_memory (related.returned_quiescent returned)).symm

/-- A lower bound for completing executions of these same bytes. It measures
retired user instructions, independently of drains and blocked issues. -/
theorem completed_minimum {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {actions : List TSO.Action}
    {result : Physical × List TSO.Observation}
    (success : TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result)
    (returned : TSO.Returned result.1) :
    13 * state.workers.length ≤ TSO.retiredCount result.2 := by
  have count := (completed_observations admitted success returned).retired
  omega

end EDSL.OS.MutexTSO
