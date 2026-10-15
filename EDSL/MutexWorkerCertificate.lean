/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay
import EDSL.OS.MutexReplay.Coverage

namespace EDSL.MutexWorkerCertificate
open X86 OS.AddressSpace OS.MutexReplay

def accepts (candidate : List Byte) : Bool := decide (candidate = bytes)

/-- Partial correctness for every successful completing supplied schedule.
Completion is recognized by actual RET phases, not by a checked final value. -/
def CompletedSpecification (state : OS.MutexReplay.State) (config : OS.Mutex.Config) (initial : BitVec 32) : Prop :=
  ∀ selections result, schedule state selections = .ok result → Finished result.1 →
    Post state result.1 initial ∧
    selections.length = 13 * state.workers.length + 4 * busyCount result.2 ∧
    ∃ collected, collect result.1 = .ok collected ∧ CollectedOutcome state config initial collected ∧
      ∀ loanId, collected.1.shared.loans loanId =
        if loanId ∈ cohortLoanIds state.workers then none else state.shared.shared.loans loanId

theorem universal_sound (candidate : List Byte) (accepted : accepts candidate = true)
    (state : OS.MutexReplay.State) (config : OS.Mutex.Config) (initial : BitVec 32)
    (valid : Invariant config state) (ready : LoanReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial) :
    candidate = bytes ∧ CompletedSpecification state config initial := by
  refine ⟨of_decide_eq_true accepted, ?_⟩
  intro selections result success finished
  have finalInv := schedule_invariant _ _ _ _ valid closed success
  exact ⟨completed_post _ _ _ _ _ valid closed entry observed success finished,
    completed_cost _ _ _ valid.controlled entry success (finalInv.completed finished),
    completed_collection_exists _ _ _ _ _ valid ready closed entry observed success finished⟩

/-- The architectural scheduler selects an existing unreturned call and executes
`X86.step` on the current shared memory. Its prefixes retain the OS witness,
completed calls meet the independent result/resource contract, and an admitted
entry cohort has a constructively supplied completing schedule. Neither checked-replay
success nor scheduler fairness is a premise of this contract. -/
structure MachineSpecification (state : OS.MutexReplay.State) (config : OS.Mutex.Config)
    (initial : BitVec 32) : Prop where
  prefixes : ∀ selections actual,
    OS.MachineThreads.schedule (erase state) selections = .ok actual →
    ∃ result, schedule state selections = .ok result ∧ actual = (erase result.1, result.2) ∧
      Invariant config result.1 ∧ ExecutionReady result.1 ∧
      ∀ identifier selected, actual.1.workers[identifier]? = some selected → selected.returned = false →
        ∃ next, OS.MachineThreads.dispatch actual.1 identifier = .ok next
  completed : ∀ selections actual,
    OS.MachineThreads.schedule (erase state) selections = .ok actual → OS.MachineThreads.Finished actual.1 →
    actual.1.workers.length = state.workers.length ∧
    (∀ worker ∈ actual.1.workers, worker.context.registers .rax = 0) ∧
    loadDWord actual.1.memory config.lockAddress = .ok 0 ∧
    loadDWord actual.1.memory config.dataAddress = .ok (initial + BitVec.ofNat 32 (2 * state.workers.length)) ∧
    selections.length = 13 * state.workers.length + 4 * busyCount actual.2 ∧
    ∃ finalState collected, actual.1 = erase finalState ∧
      collect finalState = .ok collected ∧ CollectedOutcome state config initial collected ∧
      ∀ loanId, collected.1.shared.loans loanId =
        if loanId ∈ cohortLoanIds state.workers then none else state.shared.shared.loans loanId
  completion : ∃ selections result,
    OS.MachineThreads.schedule (erase state) selections = .ok result ∧ OS.MachineThreads.Finished result.1 ∧
    busyCount result.2 = 0 ∧ selections.length = 13 * state.workers.length

/-- Exact artifact admission covers every instruction-only prefix, positive
enabledness, the completed architectural observations and OS collection, and
constructive completion with thirteen instructions per entry worker. -/
theorem machine_sound (candidate : List Byte) (accepted : accepts candidate = true)
    (state : OS.MutexReplay.State) (config : OS.Mutex.Config) (initial : BitVec 32)
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial) :
    candidate = bytes ∧ MachineSpecification state config initial := by
  refine ⟨of_decide_eq_true accepted, ?_, ?_, machine_entry_completion _ _ valid ready closed entry⟩
  · intro selections actual success
    obtain ⟨result, scheduled, same, finalInv, finalReady⟩ :=
      machine_prefix _ _ _ _ valid ready closed success
    refine ⟨result, scheduled, same, finalInv, finalReady, ?_⟩
    intro identifier selected live unreturned
    rw [same] at live ⊢
    exact machine_dispatch_enabled _ _ _ _ finalInv finalReady live unreturned
  · intro selections actual success finished
    obtain ⟨length, returns, unlocked, total, cost⟩ :=
      machine_completed_observations _ _ _ _ _ valid ready closed entry observed success finished
    refine ⟨length, returns, unlocked, total, cost, ?_⟩
    obtain ⟨result, scheduled, same⟩ := schedule_lifts _ _ _ _ valid ready closed success
    have done : Finished result.1 := by
      rw [same] at finished
      exact (erase_finished _).mp finished
    obtain ⟨collected, collectedOk, outcome, loans⟩ := completed_collection_exists _ _ _ _ _ valid
      (executionReady_loanReady _ ready) closed entry observed scheduled done
    exact ⟨result.1, collected, congrArg Prod.fst same, collectedOk, outcome, loans⟩

/-- Artifact admission is separate from finite-schedule admission. The latter
executes actual instructions and checks the independently stated endpoint.
No universal completion, enabledness or fairness claim is hidden here. -/
theorem sound (candidate : List Byte) (accepted : accepts candidate = true)
    (state : OS.MutexReplay.State) (selections : List Nat)
    (result : OS.MutexReplay.State × List (Nat × AtomicEvent))
    (verified : verify state selections = .ok result) :
    candidate = bytes ∧ ∃ record initial, state.shared.mutex = some record ∧
      loadDWord (toMemory state.shared.shared.resources.space) record.config.dataAddress = .ok initial ∧
      schedule state selections = .ok result ∧ Trace state selections result.2 result.1 ∧
      Post state result.1 initial :=
  ⟨of_decide_eq_true accepted, verify_sound _ _ _ verified⟩

end EDSL.MutexWorkerCertificate
