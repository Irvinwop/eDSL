/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Control
import EDSL.OS.MutexReplay.Payload
import EDSL.OS.MutexReplay.Totals

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem advance_invariant (state : State) (config : Mutex.Config) (identifier : Nat) (worker : Worker)
    (result : Result) (valid : Mutex.WellFormed state.shared) (registered : Registered state.shared config)
    (privateInv : WorkerInvariant state.shared config identifier worker) (closed : ClosedUnderTwo config)
    (success : advance state identifier worker = .ok result) :
    WorkerInvariant result.shared config identifier (evolved worker result) := by
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ success
  exact ⟨(advance_contexts _ _ _ _ success).2, privateInv.operands,
    advance_control _ _ _ _ valid privateInv.control success,
    perform_self_authority _ _ _ _ _ _ selected registered privateInv.authority performed,
    advance_payload _ _ _ _ _ valid registered privateInv closed success⟩

theorem dispatch_invariant (state : State) (config : Mutex.Config) (identifier : Nat)
    (result : State × Option AtomicEvent) (valid : Invariant config state)
    (closed : ClosedUnderTwo config) (success : dispatch state identifier = .ok result) :
    Invariant config result.1 := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ advanced
  have privateInv := valid.workers identifier worker live
  have own := advance_invariant _ _ _ _ _ valid.shared valid.registered privateInv closed advanced
  have bound := (List.getElem_of_getElem? live).1
  rw [same]
  refine ⟨(perform_history _ _ _ _ _ performed).wellFormed valid.shared,
    perform_registered _ _ _ _ _ _ valid.registered performed, ?_,
    perform_tracked _ _ _ _ _ valid.tracked live selected performed⟩
  intro query current found
  by_cases selectedId : identifier = query
  · subst query
    rw [List.getElem?_set_self bound] at found
    cases found
    exact own
  · have before : state.workers[query]? = some current := by
      simpa only [List.getElem?_set_ne selectedId] using found
    exact perform_peer _ _ _ _ _ _ _ _ valid.shared valid.registered selectedId (valid.workers _ _ before) performed

theorem dispatch_accounted (state : State) (config : Mutex.Config) (identifier : Nat)
    (result : State × Option AtomicEvent) (initial : BitVec 32) (valid : Invariant config state)
    (accounted : Accounted config initial state) (success : dispatch state identifier = .ok result) :
    Accounted config initial result.1 := by
  obtain ⟨worker, _, live, _, _⟩ := dispatch_ok _ _ _ success
  have value := dispatch_value _ _ _ _ _ _ valid.shared valid.registered (valid.workers _ _ live) live accounted success
  have count := dispatch_credits _ _ _ _ live success
  simpa only [Accounted, count, BitVec.ofNat_add, BitVec.add_assoc] using value

theorem schedule_invariant (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (valid : Invariant config state)
    (closed : ClosedUnderTwo config) (success : schedule state selections = .ok result) : Invariant config result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact valid
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact induction first.1 tail (dispatch_invariant _ _ _ _ valid closed head) next

theorem schedule_accounted (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (initial : BitVec 32) (valid : Invariant config state)
    (closed : ClosedUnderTwo config) (accounted : Accounted config initial state)
    (success : schedule state selections = .ok result) : Accounted config initial result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact accounted
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact induction first.1 tail (dispatch_invariant _ _ _ _ valid closed head)
      (dispatch_accounted _ _ _ _ _ valid accounted head) next

def Finished (state : State) : Prop :=
  ∀ (identifier : Nat) (worker : Worker), state.workers[identifier]? = some worker → worker.phase = .completed

theorem Invariant.completed {state : State} {config : Mutex.Config}
    (valid : Invariant config state) (finished : Finished state) : completed state = true := by
  apply List.all_eq_true.mpr
  intro worker member
  obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp member
  have phase := finished identifier worker live
  have control := (valid.workers identifier worker live).control
  have facts : worker.guard = none ∧ worker.context.registers .rax = 0 := by simpa only [Control, phase] using control
  simp only [decide_eq_true_eq]
  exact ⟨phase, facts.2, facts.1⟩

theorem Invariant.unheld {state : State} {config : Mutex.Config}
    (valid : Invariant config state) (finished : Finished state) :
    ∃ record, state.shared.mutex = some record ∧ record.config = config ∧ record.holder = none := by
  obtain ⟨record, live, same⟩ := valid.registered
  refine ⟨record, live, same, ?_⟩
  cases holder : record.holder with
  | none => rfl
  | some lease =>
    obtain ⟨identifier, worker, found, held⟩ := valid.tracked record lease live holder
    have phase := finished identifier worker found
    have control := (valid.workers identifier worker found).control
    simp [Control, phase, held] at control

/-- The program invariant discharges release's payload-admission condition
before the release operation is attempted. It is not a final-state premise. -/
theorem release_admitted (state : State) (config : Mutex.Config) (identifier : Nat) (worker : Worker)
    (lease : Mutex.Lease) (valid : Invariant config state)
    (live : state.workers[identifier]? = some worker) (phase : worker.phase = .releasing)
    (held : worker.guard = some lease) :
    ∃ result, Mutex.release state.shared (principal identifier) lease = .ok result := by
  have privateInv := valid.workers _ _ live
  obtain ⟨record, authorized, configEq⟩ := privateInv.authority lease held
  have closed : Mutex.Closed state.shared.shared config := by
    simpa only [Payload, phase] using privateInv.payload lease held
  apply Mutex.release_enabled _ _ _ record valid.shared authorized
  simpa only [configEq] using closed

/-- Every successful completing schedule has the independent requested total.
No final-value checker or assumption about the resulting payload is used. -/
theorem completed_total (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (initial : BitVec 32)
    (valid : Invariant config state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial)
    (success : schedule state selections = .ok result) (finished : Finished result.1) :
    loadDWord (toMemory result.1.shared.shared.resources.space) config.dataAddress =
      .ok (initial + BitVec.ofNat 32 (2 * state.workers.length)) := by
  have counted : Accounted config initial state := by simpa [Accounted, entry_credits _ entry] using observed
  have after := schedule_accounted _ _ _ _ _ valid closed counted success
  have finalInv := schedule_invariant _ _ _ _ valid closed success
  have total := completed_credits result.1 (finalInv.completed finished)
  have length := (schedule_trace _ _ _ success).length
  simpa only [Accounted, total, length] using after

end EDSL.OS.MutexReplay
