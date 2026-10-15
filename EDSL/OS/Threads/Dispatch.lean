/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Spawn

namespace EDSL.OS.Threads
open X86 AddressSpace

theorem replace_wellFormed (state : State) (identifier : Nat) (old next : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some old)
    (nextValid : WorkerValid state.shared identifier next) :
    WellFormed (replace state identifier (some next)) := by
  refine ⟨valid.1, ?_⟩
  intro query worker found
  by_cases same : query = identifier
  · subst query
    simp [replace] at found
    cases found
    exact ⟨(valid.2 _ _ live).1, nextValid⟩
  · exact valid.2 _ _ (by simpa [replace, same] using found)

theorem dispatch_loading (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (phase : worker.phase = .loading context) :
    dispatch state identifier = .ok (replace state identifier
      (some { worker with phase := .returning (worker.entry.loaded worker.value) })) := by
  obtain ⟨_, _, _, _, _, _, _, code, data, _, _, shape⟩ := valid
  rw [phase] at shape
  cases shape
  have instruction := loading_step worker.entry state.shared.resources.space worker.value code data
  simp [dispatch, live, phase, loading_decode _ _ code, instruction, Except.mapError]

theorem dispatch_returning (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (phase : worker.phase = .returning context) :
    dispatch state identifier = .ok (replace state identifier
      (some { worker with phase := .completed (worker.entry.returned worker.value worker.returnAddress) })) := by
  obtain ⟨_, _, _, _, _, _, _, code, _, stack, canonical, shape⟩ := valid
  rw [phase] at shape
  cases shape
  have instruction := returning_step worker.entry state.shared.resources.space worker.value worker.returnAddress
    code stack canonical
  simp [dispatch, live, phase, returning_decode _ _ _ code, instruction, Except.mapError]

theorem dispatch_completed (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (live : state.workers identifier = some worker) (phase : worker.phase = .completed context) :
    dispatch state identifier = .error .alreadyCompleted := by
  simp [dispatch, live, phase]

theorem WorkerValid.with_returning {shared : Borrowing.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) :
    WorkerValid shared identifier { worker with phase := .returning (worker.entry.loaded worker.value) } := by
  obtain ⟨parent, data, code, stack, dc, ds, cs, executable, value, target, canonical, _⟩ := valid
  exact ⟨parent, data, code, stack, dc, ds, cs, executable, value, target, canonical, rfl⟩

theorem WorkerValid.with_completed {shared : Borrowing.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) :
    WorkerValid shared identifier { worker with phase := .completed (worker.entry.returned worker.value worker.returnAddress) } := by
  obtain ⟨parent, data, code, stack, dc, ds, cs, executable, value, target, canonical, _⟩ := valid
  exact ⟨parent, data, code, stack, dc, ds, cs, executable, value, target, canonical, rfl⟩

theorem dispatch_wellFormed (state : State) (identifier : Nat) (result : State)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) : WellFormed result := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    cases phase : worker.phase with
    | loading context =>
      have expected := dispatch_loading state identifier worker context found workerValid phase
      have same := Except.ok.inj (success.symm.trans expected)
      rw [same]
      exact replace_wellFormed state identifier worker _ valid found workerValid.with_returning
    | returning context =>
      have expected := dispatch_returning state identifier worker context found workerValid phase
      have same := Except.ok.inj (success.symm.trans expected)
      rw [same]
      exact replace_wellFormed state identifier worker _ valid found workerValid.with_completed
    | completed context => rw [dispatch_completed _ _ _ _ found phase] at success; cases success

/-- A successful scheduler selection changes one private context only. -/
theorem dispatch_frame (state : State) (identifier : Nat) (result : State)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    result.shared = state.shared ∧ result.nextThread = state.nextThread ∧
    ∀ query, query ≠ identifier → result.workers query = state.workers query := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    cases phase : worker.phase with
    | loading context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_loading _ _ _ _ found workerValid phase))
      rw [same]
      exact ⟨rfl, rfl, fun query different => by simp [replace, different]⟩
    | returning context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ found workerValid phase))
      rw [same]
      exact ⟨rfl, rfl, fun query different => by simp [replace, different]⟩
    | completed context => rw [dispatch_completed _ _ _ _ found phase] at success; cases success

/-- Selecting a live unfinished worker is enabled; no fairness is inferred. -/
theorem dispatch_enabled (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (unfinished : ∀ context, worker.phase ≠ .completed context) :
    ∃ result, dispatch state identifier = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  cases phase : worker.phase with
  | loading context => exact ⟨_, dispatch_loading _ _ _ _ live workerValid phase⟩
  | returning context => exact ⟨_, dispatch_returning _ _ _ _ live workerValid phase⟩
  | completed context => exact False.elim (unfinished context phase)

end EDSL.OS.Threads
