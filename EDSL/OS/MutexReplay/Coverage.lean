/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Erasure
import EDSL.OS.MutexReplay.Progress
import EDSL.OS.MutexReplay.Outcome

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem erase_live (state : State) (identifier : Nat) (selected : MachineThreads.Worker)
    (live : (erase state).workers[identifier]? = some selected) :
    ∃ worker, state.workers[identifier]? = some worker ∧ eraseWorker worker = selected := by
  simp only [erase, List.getElem?_map] at live
  cases found : state.workers[identifier]? with
  | none => simp [found] at live
  | some worker =>
    simp only [found, Option.map_some, Option.some.injEq] at live
    exact ⟨worker, rfl, live⟩

/-- Existing unreturned selections cannot fault or cross a syscall boundary.
The successful architectural step is constructed from current admission; no
future replay result or successful bare step is assumed. -/
theorem machine_dispatch_enabled (state : State) (config : Mutex.Config) (identifier : Nat)
    (selected : MachineThreads.Worker) (valid : Invariant config state) (ready : ExecutionReady state)
    (live : (erase state).workers[identifier]? = some selected) (unreturned : selected.returned = false) :
    ∃ result, MachineThreads.dispatch (erase state) identifier = .ok result := by
  obtain ⟨worker, found, same⟩ := erase_live _ _ _ live
  have unfinished : worker.phase ≠ .completed := by
    intro done
    rw [← same] at unreturned
    simp [eraseWorker, done] at unreturned
  obtain ⟨result, success⟩ := dispatch_enabled _ _ _ _ valid ready found unfinished
  exact ⟨(erase result.1, result.2), dispatch_erases _ _ _ success⟩

/-- Every actual architectural dispatch lifts to a protocol step. Enabledness
constructs the protocol result first; architectural determinism identifies it
with the independently supplied step. -/
theorem dispatch_lifts (state : State) (config : Mutex.Config) (identifier : Nat)
    (actual : MachineThreads.State × Option AtomicEvent) (valid : Invariant config state)
    (ready : ExecutionReady state)
    (success : MachineThreads.dispatch (erase state) identifier = .ok actual) :
    ∃ result, dispatch state identifier = .ok result ∧ actual = (erase result.1, result.2) := by
  obtain ⟨selected, live, unreturned⟩ := MachineThreads.dispatch_live _ _ _ success
  obtain ⟨worker, found, same⟩ := erase_live _ _ _ live
  have unfinished : worker.phase ≠ .completed := by
    intro done
    rw [← same] at unreturned
    simp [eraseWorker, done] at unreturned
  obtain ⟨result, performed⟩ := dispatch_enabled _ _ _ _ valid ready found unfinished
  exact ⟨result, performed, (Except.ok.inj ((dispatch_erases _ _ _ performed).symm.trans success)).symm⟩

/-- Arbitrary finite instruction-only schedules lift without adding mutex,
phase, guard, code-check or resource gates to the architectural scheduler. -/
theorem schedule_lifts (state : State) (config : Mutex.Config) (selections : List Nat)
    (actual : MachineThreads.State × List (Nat × AtomicEvent)) (valid : Invariant config state)
    (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (success : MachineThreads.schedule (erase state) selections = .ok actual) :
    ∃ result, schedule state selections = .ok result ∧ actual = (erase result.1, result.2) := by
  induction selections generalizing state actual with
  | nil => simp [MachineThreads.schedule] at success; cases success; exact ⟨(state, []), rfl, rfl⟩
  | cons identifier rest induction =>
    obtain ⟨head, tail, first, following, actualEq⟩ := MachineThreads.schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, selected, headEq⟩ := dispatch_lifts _ _ _ _ valid ready first
    rw [headEq] at following
    obtain ⟨result, scheduled, tailEq⟩ := induction middle.1 tail
      (dispatch_invariant _ _ _ _ valid closed selected)
      (dispatch_executionReady _ _ _ valid.shared ready selected) following
    refine ⟨(result.1, recordEvent identifier middle.2 result.2), ?_, ?_⟩
    · simp [schedule, selected, scheduled]
    · rw [actualEq, headEq, tailEq]
      cases event : middle.2 <;> rfl

theorem erase_finished (state : State) : MachineThreads.Finished (erase state) ↔ Finished state := by
  constructor
  · intro finished identifier worker live
    have member : eraseWorker worker ∈ (erase state).workers :=
      List.mem_map.mpr ⟨worker, List.mem_of_getElem? live, rfl⟩
    exact of_decide_eq_true (finished _ member)
  · intro finished selected member
    obtain ⟨worker, original, same⟩ := List.mem_map.mp member
    obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp original
    rw [← same]
    exact decide_eq_true (finished identifier worker live)

/-- Every reachable architectural prefix retains the complete OS witness and
execution readiness. Subsequent live selections therefore remain enabled. -/
theorem machine_prefix (state : State) (config : Mutex.Config) (selections : List Nat)
    (actual : MachineThreads.State × List (Nat × AtomicEvent)) (valid : Invariant config state)
    (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (success : MachineThreads.schedule (erase state) selections = .ok actual) :
    ∃ result, schedule state selections = .ok result ∧ actual = (erase result.1, result.2) ∧
      Invariant config result.1 ∧ ExecutionReady result.1 := by
  obtain ⟨result, scheduled, same⟩ := schedule_lifts _ _ _ _ valid ready closed success
  exact ⟨result, scheduled, same, schedule_invariant _ _ _ _ valid closed scheduled,
    schedule_executionReady _ _ _ _ valid ready closed scheduled⟩

theorem machine_trace_lifts {state : State} {config : Mutex.Config} {selections : List Nat}
    {events : List (Nat × AtomicEvent)} {after : MachineThreads.State}
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (trace : MachineThreads.Trace (erase state) selections events after) :
    ∃ finalState, Trace state selections events finalState ∧ after = erase finalState ∧
      Invariant config finalState ∧ ExecutionReady finalState := by
  obtain ⟨result, scheduled, same, finalInv, finalReady⟩ :=
    machine_prefix _ _ _ _ valid ready closed trace.schedule
  have eventEq : events = result.2 := congrArg Prod.snd same
  exact ⟨result.1, eventEq ▸ schedule_trace _ _ _ scheduled,
    congrArg Prod.fst same, finalInv, finalReady⟩

/-- The raw machine observations expose the independent payload, lock, return,
and instruction-count contracts directly on the architectural result. -/
theorem machine_completed_observations (state : State) (config : Mutex.Config) (selections : List Nat)
    (actual : MachineThreads.State × List (Nat × AtomicEvent)) (initial : BitVec 32)
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial)
    (success : MachineThreads.schedule (erase state) selections = .ok actual)
    (finished : MachineThreads.Finished actual.1) :
    actual.1.workers.length = state.workers.length ∧
    (∀ worker ∈ actual.1.workers, worker.context.registers .rax = 0) ∧
    loadDWord actual.1.memory config.lockAddress = .ok 0 ∧
    loadDWord actual.1.memory config.dataAddress = .ok (initial + BitVec.ofNat 32 (2 * state.workers.length)) ∧
    selections.length = 13 * state.workers.length + 4 * busyCount actual.2 := by
  obtain ⟨result, scheduled, same, finalInv, _⟩ := machine_prefix _ _ _ _ valid ready closed success
  rw [same] at finished ⊢
  have done := (erase_finished _).mp finished
  obtain ⟨record, present, configured, free⟩ := finalInv.unheld done
  have phase := (finalInv.shared.2 record present).phase
  rw [free, configured] at phase
  refine ⟨?_, ?_, phase.1,
    completed_total _ _ _ _ _ valid closed entry observed scheduled done,
    completed_cost _ _ _ valid.controlled entry scheduled (finalInv.completed done)⟩
  · simpa only [erase, List.length_map] using (schedule_trace _ _ _ scheduled).length
  · intro selected member
    obtain ⟨worker, original, equal⟩ := List.mem_map.mp member
    obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp original
    have control := (finalInv.workers identifier worker live).control
    have facts : worker.guard = none ∧ worker.context.registers .rax = 0 := by
      simpa only [Control, done identifier worker live] using control
    rw [← equal]
    exact facts.2

/-- Completed bare-machine schedules establish the requested modular total.
The only completion premise observes actual RET markers. -/
theorem machine_completed_total (state : State) (config : Mutex.Config) (selections : List Nat)
    (actual : MachineThreads.State × List (Nat × AtomicEvent)) (initial : BitVec 32)
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok initial)
    (success : MachineThreads.schedule (erase state) selections = .ok actual)
    (finished : MachineThreads.Finished actual.1) :
    loadDWord actual.1.memory config.dataAddress = .ok (initial + BitVec.ofNat 32 (2 * state.workers.length)) := by
  obtain ⟨result, scheduled, same⟩ := schedule_lifts _ _ _ _ valid ready closed success
  rw [same] at finished ⊢
  exact completed_total _ _ _ _ _ valid closed entry observed scheduled ((erase_finished _).mp finished)

/-- A completing architectural schedule exists for every admitted entry
cohort. Its thirteen instructions per worker attain the existing lower bound
for this fixed routine, without a scheduler-fairness or timing premise. -/
theorem machine_entry_completion (state : State) (config : Mutex.Config)
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry) :
    ∃ selections result, MachineThreads.schedule (erase state) selections = .ok result ∧
      MachineThreads.Finished result.1 ∧ busyCount result.2 = 0 ∧
      selections.length = 13 * state.workers.length := by
  obtain ⟨selections, result, success, finished, noBusy, length⟩ :=
    entry_cohort_completion _ _ valid ready closed entry
  exact ⟨selections, (erase result.1, result.2), schedule_erases _ _ _ success,
    (erase_finished _).mpr finished, noBusy, length⟩

/-- Completion is also constructive from any admitted intermediate state.
Finishing the tracked holder first avoids any new busy exchanges. -/
theorem machine_completion (state : State) (config : Mutex.Config)
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config) :
    ∃ selections result, MachineThreads.schedule (erase state) selections = .ok result ∧
      MachineThreads.Finished result.1 ∧ busyCount result.2 = 0 ∧
      selections.length = potentialSum state ∧ selections.length ≤ 15 * state.workers.length := by
  obtain ⟨selections, result, success, finished, noBusy, length, bound⟩ :=
    cohort_completion _ _ valid ready closed
  exact ⟨selections, (erase result.1, result.2), schedule_erases _ _ _ success,
    (erase_finished _).mpr finished, noBusy, length, bound⟩

/-- Every completing schedule of this same byte profile needs at least
thirteen user instructions per entry worker. machine_entry_completion attains
the bound; no comparison with other programs or hardware timings is made. -/
theorem machine_entry_minimum (state : State) (config : Mutex.Config) (selections : List Nat)
    (actual : MachineThreads.State × List (Nat × AtomicEvent))
    (valid : Invariant config state) (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (success : MachineThreads.schedule (erase state) selections = .ok actual)
    (finished : MachineThreads.Finished actual.1) : 13 * state.workers.length ≤ selections.length := by
  obtain ⟨result, scheduled, same, finalInv, _⟩ := machine_prefix _ _ _ _ valid ready closed success
  rw [same] at finished
  have cost := completed_cost _ _ _ valid.controlled entry scheduled
    (finalInv.completed ((erase_finished _).mp finished))
  omega

end EDSL.OS.MutexReplay
