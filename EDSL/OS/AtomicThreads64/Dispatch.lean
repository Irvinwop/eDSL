/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Spawn

namespace EDSL.OS.AtomicThreads64
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

theorem WorkerValid.with_returning {shared : Atomics64.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (event : Atomics64.Event) (af : Bool) :
    WorkerValid shared identifier { worker with phase := .returning event (applied worker.entry event.logical.event.after af) } :=
  ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.executable,
    valid.target, valid.canonical, af, rfl⟩

theorem WorkerValid.with_completed {shared : Atomics64.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (event : Atomics64.Event) (af : Bool) :
    WorkerValid shared identifier { worker with phase := .completed event (returned (applied worker.entry event.logical.event.after af) worker.returnAddress) } :=
  ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.executable,
    valid.target, valid.canonical, af, rfl⟩

theorem dispatch_applying (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (af : Bool) (result : Atomics64.State × Atomics64.Event)
    (live : state.workers identifier = some worker) (valid : WellFormed state)
    (phase : worker.phase = .applying context)
    (success : Atomics64.logicalDiscard state.shared (principal identifier) worker.handle
      (worker.entry.registers .rsi) = .ok result) :
    dispatch state identifier af = .ok
      ({ replace state identifier (some { worker with phase := .returning result.2 (applied worker.entry result.2.logical.event.after af) }) with shared := result.1 }, some result.2) := by
  have workerValid := (valid.2 _ _ live).2
  have shape := workerValid.phase
  rw [phase] at shape
  change context = worker.entry at shape
  cases shape
  obtain ⟨handle, cell, authorized, address, _⟩ := workerValid.authorized valid.1
  have instruction := Atomics64.logicalDiscard_step state.shared (principal identifier) worker.handle
    (worker.entry.registers .rsi) result handle cell
    (worker.entry.snapshot state.shared.legacy.shared.resources.space) af success authorized rfl
    address.symm rfl (applying_decode _ _ workerValid.executable)
  simp [dispatch, live, phase, applying_decode _ _ workerValid.executable, authorized,
    address, success, instruction, apply_context, Except.mapError]

theorem dispatch_returning (state : State) (identifier : Nat) (worker : Worker)
    (event : Atomics64.Event) (context : Context) (af : Bool)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (phase : worker.phase = .returning event context) :
    dispatch state identifier af = .ok (replace state identifier
      (some { worker with phase := .completed event (returned context worker.returnAddress) }), none) := by
  have shape := valid.phase
  rw [phase] at shape
  obtain ⟨chosen, shape⟩ := shape
  cases shape
  simp [dispatch, live, phase, returning_decode _ _ _ _ valid.executable,
    returning_step _ _ _ _ _ _ valid.executable valid.target valid.canonical, Except.mapError]

theorem dispatch_completed (state : State) (identifier : Nat) (worker : Worker)
    (event : Atomics64.Event) (context : Context) (af : Bool)
    (live : state.workers identifier = some worker) (phase : worker.phase = .completed event context) :
    dispatch state identifier af = .error .alreadyCompleted := by
  simp [dispatch, live, phase]

theorem dispatch_wellFormed (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) : WellFormed result.1 := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    cases phase : worker.phase with
    | returning event context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ _ _ found workerValid phase))
      rw [same]
      have shape := workerValid.phase
      rw [phase] at shape
      obtain ⟨chosen, shape⟩ := shape
      cases shape
      exact replace_wellFormed state identifier worker _ valid found (workerValid.with_completed event chosen)
    | completed event context => rw [dispatch_completed _ _ _ _ _ _ found phase] at success; cases success
    | applying context =>
      obtain ⟨handle, cell, authorized, _, _⟩ := workerValid.authorized valid.1
      obtain ⟨shared, changed⟩ := Atomics64.logicalDiscard_enabled _ _ _
        (worker.entry.registers .rsi) handle cell valid.1 authorized
      have same := Except.ok.inj (success.symm.trans (dispatch_applying _ _ _ _ _ _ found valid phase changed))
      have keeps := Atomics64.logicalDiscard_effect _ _ _ _ _ changed
      have history : Atomics64.History state.shared [some shared.2] shared.1 :=
        .next (.logicalDiscard changed) .refl
      have frame : ∀ query peer, state.workers query = some peer → WorkerValid shared.1 query peer := by
        intro query peer live
        exact ((valid.2 _ _ live).2).frame valid.1 history
          ⟨congrFun keeps.handles _, congrFun keeps.cells _, congrFun keeps.shared.loans _,
            congrFun keeps.shared.loans _⟩
      rw [same]
      refine ⟨Atomics64.logicalDiscard_wellFormed _ _ _ _ _ valid.1 changed, ?_⟩
      intro query peer live
      by_cases selected : query = identifier
      · subst query
        simp [replace] at live
        cases live
        exact ⟨(valid.2 _ _ found).1, (frame identifier worker found).with_returning shared.2 af⟩
      · have beforeAt : state.workers query = some peer := by simpa [replace, selected] using live
        exact ⟨(valid.2 _ _ beforeAt).1, frame query peer beforeAt⟩

/-- Present authority and current code/stack suffice for either AF choice.
The only excluded live phase is already completed, which must be joined. -/
theorem dispatch_enabled (state : State) (identifier : Nat) (worker : Worker) (af : Bool)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (unfinished : ∀ event context, worker.phase ≠ .completed event context) :
    ∃ result, dispatch state identifier af = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  cases phase : worker.phase with
  | returning event context => exact ⟨_, dispatch_returning _ _ _ _ _ _ live workerValid phase⟩
  | completed event context => exact False.elim (unfinished event context phase)
  | applying context =>
    obtain ⟨handle, cell, authorized, _, _⟩ := workerValid.authorized valid.1
    obtain ⟨shared, changed⟩ := Atomics64.logicalDiscard_enabled _ _ _
      (worker.entry.registers .rsi) handle cell valid.1 authorized
    exact ⟨_, dispatch_applying _ _ _ _ _ _ live valid phase changed⟩

end EDSL.OS.AtomicThreads64
