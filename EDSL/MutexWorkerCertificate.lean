/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay

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
