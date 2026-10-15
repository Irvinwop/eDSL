/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Cost
import EDSL.OS.MutexReplay.Ready
import EDSL.OS.MutexReplay.Tracking

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- A selected worker can run alone when any current holder is its own guard.
This describes the current protocol state, independently of future execution. -/
def FreeOrOwn (state : State) (worker : Worker) : Prop :=
  ∀ record lease, state.shared.mutex = some record → record.holder = some lease →
    worker.guard = some lease

theorem FreeOrOwn.of_free {state : State} (worker : Worker)
    (free : ∀ record, state.shared.mutex = some record → record.holder = none) :
    FreeOrOwn state worker := by
  intro record lease present held
  rw [free record present] at held
  cases held

theorem FreeOrOwn.free {state : State} {worker : Worker} (solo : FreeOrOwn state worker)
    (unguarded : worker.guard = none) :
    ∀ record, state.shared.mutex = some record → record.holder = none := by
  intro record present
  cases held : record.holder with
  | none => rfl
  | some lease =>
    have owns := solo record lease present held
    rw [unguarded] at owns
    cases owns

/-- The actual protocol/machine operation preserves solo ownership and cannot
emit a busy exchange. In the acquisition case the selected action has no
guard, so the current mutex is free and the real acquiring attempt succeeds. -/
theorem perform_freeOrOwn (state : State) (identifier : Nat) (worker : Worker)
    (operation : Action) (result : Result) (valid : Mutex.WellFormed state.shared)
    (solo : FreeOrOwn state worker) (selected : action worker = .ok operation)
    (success : perform state.shared identifier worker operation = .ok result) :
    FreeOrOwn ⟨result.shared, state.workers.set identifier (evolved worker result)⟩
      (evolved worker result) ∧ busy result.event = 0 := by
  cases perform_effect _ _ _ _ _ success with
  | plain instruction context ran => exact ⟨solo, rfl⟩
  | load lease record value context authorized operand loaded ran => exact ⟨solo, rfl⟩
  | ret context ran => exact ⟨solo, rfl⟩
  | store lease record after context authorized operand stored ran =>
    obtain ⟨_, _, _, _, same⟩ := Mutex.guardStore_ok _ _ _ _ _ stored
    refine ⟨?_, rfl⟩
    simpa only [FreeOrOwn, evolved, same] using solo
  | acquire record attempt context found operand replacement acquired ran =>
    have free := solo.free (action_acquire_none _ selected)
    have present := Mutex.registered_ok _ _ found
    obtain ⟨enabled, lease, current, enabledOk, guarded, _⟩ :=
      Mutex.acquire_free _ _ _ valid present (free record present)
    have equal := Except.ok.inj (enabledOk.symm.trans acquired)
    subst enabled
    rcases Mutex.acquisition _ _ _ valid acquired with granted | failed
    · obtain ⟨fresh, after, guard, live, held, _, _, _, before, replacement⟩ := granted
      refine ⟨?_, by simp [busy, before, replacement]⟩
      intro current token present holder
      have equal := Option.some.inj (present.symm.trans live)
      subst current
      have tokenEq := Option.some.inj (held.symm.trans holder)
      exact guard.trans (congrArg some tokenEq)
    · rw [failed.1] at guarded
      cases guarded
  | release lease record released context authorized operand replacement finished ran =>
    obtain ⟨after, live, free, _, before, replacement⟩ :=
      Mutex.release_result _ _ _ _ valid finished
    refine ⟨?_, by simp [busy, before, replacement]⟩
    intro current token present held
    have equal := Option.some.inj (present.symm.trans live)
    subst current
    rw [free] at held
    cases held

theorem advance_freeOrOwn (state : State) (identifier : Nat) (worker : Worker)
    (result : Result) (valid : Mutex.WellFormed state.shared)
    (solo : FreeOrOwn state worker) (success : advance state identifier worker = .ok result) :
    FreeOrOwn ⟨result.shared, state.workers.set identifier (evolved worker result)⟩
      (evolved worker result) ∧ busy result.event = 0 := by
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ success
  exact perform_freeOrOwn _ _ _ _ _ valid solo selected performed

theorem potential_zero_iff_completed (worker : Worker) :
    potential worker = 0 ↔ worker.phase = .completed := by
  cases phase : worker.phase <;> cases guard : worker.guard <;> simp [potential, phase, guard]

theorem potential_le_fifteen (worker : Worker) : potential worker ≤ 15 := by
  cases phase : worker.phase <;> cases guard : worker.guard <;> simp [potential, phase, guard]

theorem potentialSum_le_fifteen (state : State) :
    potentialSum state ≤ 15 * state.workers.length := by
  suffices ∀ workers : List Worker, (workers.map potential).sum ≤ 15 * workers.length from
    this state.workers
  intro workers
  induction workers with
  | nil => simp
  | cons worker rest induction =>
    have bound := potential_le_fifteen worker
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Dispatch changes only the selected immutable cohort index. -/
theorem dispatch_peer (state : State) (identifier query : Nat)
    (result : State × Option AtomicEvent) (other : identifier ≠ query)
    (success : dispatch state identifier = .ok result) :
    result.1.workers[query]? = state.workers[query]? := by
  obtain ⟨_, _, _, _, same⟩ := dispatch_ok _ _ _ success
  simp only [same, List.getElem?_set_ne other]

theorem dispatch_solo (state : State) (identifier : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (valid : Mutex.WellFormed state.shared)
    (control : Control worker) (live : state.workers[identifier]? = some worker)
    (solo : FreeOrOwn state worker) (success : dispatch state identifier = .ok result) :
    ∃ current, result.1.workers[identifier]? = some current ∧
      FreeOrOwn result.1 current ∧ busy result.2 = 0 ∧
      potential current + 1 = potential worker := by
  obtain ⟨selected, output, found, advanced, same⟩ := dispatch_ok _ _ _ success
  have equal := Option.some.inj (found.symm.trans live)
  subst selected
  obtain ⟨afterSolo, noBusy⟩ := advance_freeOrOwn _ _ _ _ valid solo advanced
  have decrease := advance_potential _ _ _ _ valid control advanced
  rw [noBusy] at decrease
  rw [same]
  refine ⟨evolved worker output, List.getElem?_set_self (List.getElem_of_getElem? live).1,
    afterSolo, noBusy, ?_⟩
  simpa only [Nat.mul_zero, Nat.add_zero] using decrease

/-- A successful instruction cannot select a completed worker, and therefore
retains each previously completed worker's exact private state. -/
theorem dispatch_keeps_completed (state : State) (identifier query : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (live : state.workers[query]? = some worker)
    (done : worker.phase = .completed) (success : dispatch state identifier = .ok result) :
    result.1.workers[query]? = some worker := by
  by_cases own : identifier = query
  · subst query
    obtain ⟨selected, output, found, advanced, _⟩ := dispatch_ok _ _ _ success
    have equal := Option.some.inj (found.symm.trans live)
    subst selected
    obtain ⟨_, operation, selected, _, _⟩ := advance_ok _ _ _ _ advanced
    simp [action, done] at selected
  · exact (dispatch_peer _ _ _ _ own success).trans live

theorem schedule_keeps_completed (state : State) (selections : List Nat) (query : Nat)
    (worker : Worker) (result : State × List (Nat × AtomicEvent))
    (live : state.workers[query]? = some worker) (done : worker.phase = .completed)
    (success : schedule state selections = .ok result) :
    result.1.workers[query]? = some worker := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact live
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact induction first.1 tail (dispatch_keeps_completed _ _ _ _ _ live done head) next

theorem schedule_peer (state : State) (selections : List Nat) (query : Nat)
    (result : State × List (Nat × AtomicEvent)) (absent : query ∉ selections)
    (success : schedule state selections = .ok result) :
    result.1.workers[query]? = state.workers[query]? := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    have other : identifier ≠ query := by intro equal; subst query; exact absent (by simp)
    have tailAbsent : query ∉ rest := by intro member; exact absent (by simp [member])
    rw [same]
    exact (induction first.1 tail tailAbsent next).trans (dispatch_peer _ _ _ _ other head)

end EDSL.OS.MutexReplay
