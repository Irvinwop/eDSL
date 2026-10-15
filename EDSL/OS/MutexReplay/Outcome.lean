/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Preservation
import EDSL.OS.MutexReplay.Loans

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- All successful completing schedules establish the independent endpoint.
The hypotheses describe the admitted initial program state and its local
invariant; none assumes a final value or a successful postcondition checker. -/
theorem completed_post (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (initial : BitVec 32)
    (valid : Invariant config state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial)
    (success : schedule state selections = .ok result) (finished : Finished result.1) : Post state result.1 initial := by
  have finalInv := schedule_invariant _ _ _ _ valid closed success
  have total := completed_total _ _ _ _ _ valid closed entry observed success finished
  obtain ⟨original, originalAt, originalConfig⟩ := valid.registered
  obtain ⟨record, recordAt, recordConfig, free⟩ := finalInv.unheld finished
  have phase := (finalInv.shared.2 record recordAt).phase
  rw [free] at phase
  obtain ⟨value, readback, invariant⟩ := phase.2
  rw [recordConfig] at readback invariant
  have valueEq := Except.ok.inj (readback.symm.trans total)
  refine ⟨(schedule_trace _ _ _ success).length, finalInv.completed finished,
    original, record, originalAt, recordAt, free, ?_, ?_, ?_⟩
  · simpa only [originalConfig, recordConfig] using phase.1
  · simpa only [originalConfig] using total
  · simpa only [originalConfig, ← valueEq] using invariant

def CollectedOutcome (state : State) (config : Mutex.Config) (initial : BitVec 32)
    (collected : Mutex.State × List Word) : Prop :=
  Mutex.WellFormed collected.1 ∧ collected.2 = List.replicate state.workers.length 0 ∧
    loadDWord (toMemory collected.1.shared.resources.space) config.lockAddress = .ok 0 ∧
    loadDWord (toMemory collected.1.shared.resources.space) config.dataAddress =
      .ok (initial + BitVec.ofNat 32 (2 * state.workers.length)) ∧
    Mutex.Closed collected.1.shared config

theorem completed_collection (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (initial : BitVec 32) (collected : Mutex.State × List Word)
    (valid : Invariant config state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial)
    (success : schedule state selections = .ok result) (finished : Finished result.1)
    (joined : collect result.1 = .ok collected) : CollectedOutcome state config initial collected := by
  have finalInv := schedule_invariant _ _ _ _ valid closed success
  obtain ⟨record, live, same, free⟩ := finalInv.unheld finished
  have phase := (finalInv.shared.2 record live).phase
  rw [free, same] at phase
  have resources := (collect_resources _ _ joined).1
  have total := completed_total _ _ _ _ _ valid closed entry observed success finished
  have length := (schedule_trace _ _ _ success).length
  refine ⟨collect_wellFormed _ _ finalInv.shared joined, ?_, ?_, ?_, ?_⟩
  · simpa only [length] using collect_zero _ _ joined
  · rw [resources]; exact phase.1
  · rw [resources]; exact total
  · exact ⟨_, by rw [resources]; exact total, by
      obtain ⟨value, readback, invariant⟩ := phase.2
      have equal := Except.ok.inj (readback.symm.trans total)
      simpa only [← equal] using invariant⟩

theorem schedule_loans (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : result.1.shared.shared.loans = state.shared.shared.loans := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨worker, output, _, advanced, firstEq⟩ := dispatch_ok _ _ _ head
    obtain ⟨_, _, _, performed, _⟩ := advance_ok _ _ _ _ advanced
    rw [same, induction first.1 tail next, firstEq]
    exact (perform_loans _ _ _ _ _ performed).1

theorem cohortLoanIds_set (workers : List Worker) (identifier : Nat) (worker : Worker) (output : Result)
    (live : workers[identifier]? = some worker) :
    cohortLoanIds (workers.set identifier (evolved worker output)) = cohortLoanIds workers := by
  induction workers generalizing identifier with
  | nil => simp at live
  | cons first rest induction =>
    cases identifier with
    | zero => simp at live; cases live; rfl
    | succ index =>
      have tail : rest[index]? = some worker := by simpa using live
      simpa only [List.set, cohortLoanIds, List.flatMap_cons] using
        congrArg (fun loans => [first.codeLoan, first.stackLoan] ++ loans) (induction index tail)

theorem schedule_loanIds (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : cohortLoanIds result.1.workers = cohortLoanIds state.workers := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨worker, output, live, _, firstEq⟩ := dispatch_ok _ _ _ head
    rw [same, induction first.1 tail next, firstEq]
    exact cohortLoanIds_set _ _ _ _ live

/-- Every completing admitted cohort can be collected. All of its original
loan identifiers are revoked, while every unrelated loan record is retained. -/
theorem completed_collection_exists (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (initial : BitVec 32)
    (valid : Invariant config state) (ready : LoanReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial)
    (success : schedule state selections = .ok result) (finished : Finished result.1) :
    ∃ collected, collect result.1 = .ok collected ∧ CollectedOutcome state config initial collected ∧
      ∀ loanId, collected.1.shared.loans loanId =
        if loanId ∈ cohortLoanIds state.workers then none else state.shared.shared.loans loanId := by
  have finalInv := schedule_invariant _ _ _ _ valid closed success
  have finalReady := schedule_loanReady _ _ _ ready success
  obtain ⟨collected, joined⟩ := collect_enabled result.1 (finalInv.completed finished) finalReady
  refine ⟨collected, joined, completed_collection _ _ _ _ _ _ valid closed entry observed success finished joined, ?_⟩
  intro loanId
  simpa only [schedule_loanIds _ _ _ success, schedule_loans _ _ _ success] using collect_loans _ _ joined loanId

end EDSL.OS.MutexReplay
