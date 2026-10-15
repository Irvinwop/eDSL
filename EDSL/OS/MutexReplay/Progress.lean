/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Readiness
import EDSL.OS.MutexReplay.Solo
import EDSL.OS.MutexReplay.Enabled

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem busyCount_append (first rest : List (Nat × AtomicEvent)) :
    busyCount (first ++ rest) = busyCount first + busyCount rest := by
  simp only [busyCount, List.map_append, List.sum_append]

/-- Concatenating two constructed, successful schedules concatenates their
actual atomic traces in execution order. -/
theorem schedule_append_ok (state : State) (first : List Nat)
    (middle : State × List (Nat × AtomicEvent)) (rest : List Nat)
    (result : State × List (Nat × AtomicEvent))
    (scheduledFirst : schedule state first = .ok middle)
    (suffix : schedule middle.1 rest = .ok result) :
    schedule state (first ++ rest) = .ok (result.1, middle.2 ++ result.2) := by
  induction first generalizing state middle with
  | nil =>
    simp [schedule] at scheduledFirst
    cases scheduledFirst
    simpa using suffix
  | cons identifier following induction =>
    obtain ⟨head, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ scheduledFirst
    rw [same] at suffix ⊢
    have joined := induction head.1 tail scheduled suffix
    cases event : head.2 <;>
      simp [schedule, selected, joined, recordEvent, event]

/-- Selecting one worker for exactly its current potential executes its real
RET and leaves the mutex free. The high potentials of a previously busy CMP
or branch include the remaining retry instructions. No future success is a
premise: each dispatch is obtained from the current execution invariant. -/
theorem schedule_solo_completes (steps : Nat) (state : State) (config : Mutex.Config)
    (identifier : Nat) (worker : Worker) (valid : Invariant config state)
    (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (live : state.workers[identifier]? = some worker) (solo : FreeOrOwn state worker)
    (rank : potential worker = steps) :
    ∃ result current,
      schedule state (List.replicate steps identifier) = .ok result ∧
      result.1.workers[identifier]? = some current ∧ current.phase = .completed ∧
      (∀ record, result.1.shared.mutex = some record → record.holder = none) ∧
      busyCount result.2 = 0 := by
  induction steps generalizing state worker with
  | zero =>
    have done := (potential_zero_iff_completed worker).mp rank
    have facts : worker.guard = none ∧ worker.context.registers .rax = 0 := by
      simpa only [Control, done] using (valid.workers identifier worker live).control
    exact ⟨(state, []), worker, rfl, live, done, solo.free facts.1, rfl⟩
  | succ steps induction =>
    have unfinished : worker.phase ≠ .completed := by
      intro done
      have zero := (potential_zero_iff_completed worker).mpr done
      omega
    obtain ⟨first, selected⟩ := dispatch_enabled state config identifier worker valid ready live unfinished
    obtain ⟨middle, middleAt, afterSolo, noBusy, decrease⟩ :=
      dispatch_solo _ _ _ _ valid.shared (valid.workers _ _ live).control live solo selected
    have nextRank : potential middle = steps := by omega
    have nextValid := dispatch_invariant _ _ _ _ valid closed selected
    have nextReady := dispatch_executionReady _ _ _ valid.shared ready selected
    obtain ⟨tail, current, scheduled, currentAt, done, free, tailBusy⟩ :=
      induction first.1 middle nextValid nextReady middleAt afterSolo nextRank
    refine ⟨(tail.1, recordEvent identifier first.2 tail.2), current, ?_, currentAt, done, free, ?_⟩
    · simp [List.replicate_succ, schedule, selected, scheduled]
    · simp only [busyCount_recordEvent, noBusy, tailBusy, Nat.zero_add]

theorem worker_completion (state : State) (config : Mutex.Config) (identifier : Nat)
    (worker : Worker) (valid : Invariant config state) (ready : ExecutionReady state)
    (closed : ClosedUnderTwo config) (live : state.workers[identifier]? = some worker)
    (solo : FreeOrOwn state worker) :
    ∃ result current,
      schedule state (List.replicate (potential worker) identifier) = .ok result ∧
      result.1.workers[identifier]? = some current ∧ current.phase = .completed ∧
      (∀ record, result.1.shared.mutex = some record → record.holder = none) ∧
      busyCount result.2 = 0 :=
  schedule_solo_completes (potential worker) state config identifier worker valid ready closed live solo rfl

/-- Finish a finite list of immutable cohort indices consecutively. Already
completed indices need zero selections; all previous returns survive each
subsequent schedule, including when an index appears more than once. -/
theorem finish_indices (indices : List Nat) (state : State) (config : Mutex.Config)
    (valid : Invariant config state) (ready : ExecutionReady state)
    (closed : ClosedUnderTwo config)
    (free : ∀ record, state.shared.mutex = some record → record.holder = none)
    (bounds : ∀ identifier ∈ indices, identifier < state.workers.length) :
    ∃ selections result, schedule state selections = .ok result ∧
      (∀ identifier ∈ indices, ∃ worker,
        result.1.workers[identifier]? = some worker ∧ worker.phase = .completed) ∧
      (∀ record, result.1.shared.mutex = some record → record.holder = none) ∧
      busyCount result.2 = 0 := by
  induction indices generalizing state with
  | nil =>
    refine ⟨[], (state, []), rfl, ?_, free, rfl⟩
    intro identifier member
    cases member
  | cons identifier rest induction =>
    have bound := bounds identifier (by simp)
    let worker := state.workers[identifier]
    have live : state.workers[identifier]? = some worker := List.getElem?_eq_getElem bound
    obtain ⟨first, current, scheduled, currentAt, done, afterFree, noBusy⟩ :=
      worker_completion state config identifier worker valid ready closed live (FreeOrOwn.of_free worker free)
    have nextValid := schedule_invariant _ _ _ _ valid closed scheduled
    have nextReady := schedule_executionReady _ _ _ _ valid ready closed scheduled
    have length := (schedule_trace _ _ _ scheduled).length
    have tailBounds : ∀ query ∈ rest, query < first.1.workers.length := by
      intro query member
      rw [length]
      exact bounds query (by simp [member])
    obtain ⟨selections, tail, following, allDone, finalFree, tailBusy⟩ :=
      induction first.1 nextValid nextReady afterFree tailBounds
    refine ⟨List.replicate (potential worker) identifier ++ selections,
      (tail.1, first.2 ++ tail.2), schedule_append_ok _ _ _ _ _ scheduled following,
      ?_, finalFree, ?_⟩
    · intro query member
      rcases List.mem_cons.mp member with own | member
      · subst query
        exact ⟨current,
          schedule_keeps_completed first.1 selections identifier current tail currentAt done following, done⟩
      · exact allDone query member
    · simp only [busyCount_append, noBusy, tailBusy, Nat.zero_add]

/-- If replay is paused while the mutex is held, Tracked identifies the
actual holder. Finish that worker first; otherwise the empty prefix suffices.
The constructed prefix introduces no additional busy acquisitions. -/
theorem completion_free_prefix (state : State) (config : Mutex.Config)
    (valid : Invariant config state) (ready : ExecutionReady state)
    (closed : ClosedUnderTwo config) :
    ∃ selections result, schedule state selections = .ok result ∧
      (∀ record, result.1.shared.mutex = some record → record.holder = none) ∧
      busyCount result.2 = 0 := by
  obtain ⟨record, present, _⟩ := valid.registered
  cases holder : record.holder with
  | none =>
    refine ⟨[], (state, []), rfl, ?_, rfl⟩
    intro current live
    have equal := Option.some.inj (live.symm.trans present)
    subst current
    exact holder
  | some lease =>
    obtain ⟨identifier, worker, live, owns⟩ := valid.tracked record lease present holder
    have solo : FreeOrOwn state worker := by
      intro current token registered held
      have equal := Option.some.inj (registered.symm.trans present)
      subst current
      have same := Option.some.inj (holder.symm.trans held)
      exact owns.trans (congrArg some same)
    obtain ⟨result, _, scheduled, _, _, free, noBusy⟩ :=
      worker_completion state config identifier worker valid ready closed live solo
    exact ⟨List.replicate (potential worker) identifier, result, scheduled, free, noBusy⟩

/-- Constructive completion from any admitted intermediate cohort. A current
holder finishes first and the remaining immutable indices finish in order.
The bound counts future user instructions only, with no new busy exchanges;
it makes no fairness, elapsed-time, or machine-code minimality claim. -/
theorem cohort_completion (state : State) (config : Mutex.Config)
    (valid : Invariant config state) (ready : ExecutionReady state)
    (closed : ClosedUnderTwo config) :
    ∃ selections result, schedule state selections = .ok result ∧ Finished result.1 ∧
      busyCount result.2 = 0 ∧ selections.length = potentialSum state ∧
      selections.length ≤ 15 * state.workers.length := by
  obtain ⟨first, middle, scheduled, free, firstBusy⟩ :=
    completion_free_prefix state config valid ready closed
  have middleValid := schedule_invariant _ _ _ _ valid closed scheduled
  have middleReady := schedule_executionReady _ _ _ _ valid ready closed scheduled
  obtain ⟨rest, tail, following, allDone, _, tailBusy⟩ :=
    finish_indices (List.range middle.1.workers.length) middle.1 config middleValid middleReady closed free
      (by intro identifier member; exact List.mem_range.mp member)
  let selections := first ++ rest
  let result := (tail.1, middle.2 ++ tail.2)
  have success : schedule state selections = .ok result :=
    schedule_append_ok _ _ _ _ _ scheduled following
  have finished : Finished result.1 := by
    intro identifier worker live
    have bound : identifier < middle.1.workers.length := by
      rw [← (schedule_trace _ _ _ following).length]
      exact (List.getElem_of_getElem? live).1
    obtain ⟨current, found, done⟩ := allDone identifier (List.mem_range.mpr bound)
    have equal := Option.some.inj (found.symm.trans live)
    exact equal ▸ done
  have noBusy : busyCount result.2 = 0 := by
    simp only [result, busyCount_append, firstBusy, tailBusy, Nat.zero_add]
  have finalValid := schedule_invariant _ _ _ _ valid closed success
  have cost := schedule_potential _ _ _ valid.controlled success
  rw [completed_potential _ (finalValid.completed finished), noBusy] at cost
  have length : selections.length = potentialSum state := by omega
  exact ⟨selections, result, success, finished, noBusy, length,
    length ▸ potentialSum_le_fifteen state⟩

/-- Every finite entry cohort has a successful thirteen-instruction-per-worker
schedule. The length follows from the independent exact-cost theorem. All
payload words, return targets, and the cohort size remain symbolic. -/
theorem entry_cohort_completion (state : State) (config : Mutex.Config)
    (valid : Invariant config state) (ready : ExecutionReady state)
    (closed : ClosedUnderTwo config)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry) :
    ∃ selections result, schedule state selections = .ok result ∧ Finished result.1 ∧
      busyCount result.2 = 0 ∧ selections.length = 13 * state.workers.length := by
  obtain ⟨selections, result, success, finished, noBusy, _, _⟩ :=
    cohort_completion state config valid ready closed
  have finalValid := schedule_invariant _ _ _ _ valid closed success
  have cost := completed_cost _ _ _ valid.controlled entry success (finalValid.completed finished)
  rw [noBusy, Nat.mul_zero, Nat.add_zero] at cost
  exact ⟨selections, result, success, finished, noBusy, cost⟩

end EDSL.OS.MutexReplay
