/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Spawn

namespace EDSL.OS.AtomicThreads
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

theorem WorkerValid.with_exchanging {shared : Atomics.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) :
    WorkerValid shared identifier { worker with phase := .exchanging (prepared worker.entry) } :=
  ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.executable,
    valid.target, valid.canonical, rfl⟩

theorem WorkerValid.with_returning {shared : Atomics.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (old : BitVec 32) :
    WorkerValid shared identifier { worker with phase := .returning old (exchanged worker.entry old) } :=
  ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.executable,
    valid.target, valid.canonical, rfl⟩

theorem WorkerValid.with_completed {shared : Atomics.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (old : BitVec 32) :
    WorkerValid shared identifier { worker with phase := .completed old (worker.entry.returned old worker.returnAddress) } :=
  ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.executable,
    valid.target, valid.canonical, rfl⟩

theorem WorkerValid.authorized {shared : Atomics.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) :
    ∃ handle, Atomics.authorize shared (principal identifier) worker.handle = .ok handle ∧
      handle.address = worker.entry.registers .rdi := by
  obtain ⟨handle, live, actor, address⟩ := valid.handle
  exact ⟨handle, by simp [Atomics.authorize, live, actor], address⟩

theorem dispatch_preparing (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (phase : worker.phase = .preparing context) :
    dispatch state identifier = .ok (replace state identifier
      (some { worker with phase := .exchanging (prepared worker.entry) }), none) := by
  have shape := valid.phase
  rw [phase] at shape
  change context = worker.entry at shape
  cases shape
  simp [dispatch, live, phase, preparing_decode _ _ valid.executable,
    preparing_step _ _ valid.executable, Except.mapError]

theorem dispatch_returning (state : State) (identifier : Nat) (worker : Worker) (old : BitVec 32) (context : Context)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (phase : worker.phase = .returning old context) :
    dispatch state identifier = .ok (replace state identifier
      (some { worker with phase := .completed old (worker.entry.returned old worker.returnAddress) }), none) := by
  have shape := valid.phase
  rw [phase] at shape
  change context = exchanged worker.entry old at shape
  cases shape
  simp [dispatch, live, phase, returning_decode _ _ _ valid.executable,
    returning_step _ _ _ _ valid.executable valid.target valid.canonical, Except.mapError]

theorem dispatch_exchanging (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (result : Atomics.State × BitVec 32)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (phase : worker.phase = .exchanging context)
    (success : Atomics.exchange state.shared (principal identifier) worker.handle
      ((worker.entry.registers .rsi).setWidth 32) = .ok result) :
    dispatch state identifier = .ok
      ({ replace state identifier (some { worker with phase := .returning result.2 (exchanged worker.entry result.2) }) with
        shared := result.1 }, some ⟨worker.entry.registers .rdi, result.2, (worker.entry.registers .rsi).setWidth 32⟩) := by
  have shape := valid.phase
  rw [phase] at shape
  change context = prepared worker.entry at shape
  cases shape
  obtain ⟨handle, authorized, address⟩ := valid.authorized
  have operand : ((prepared worker.entry).snapshot state.shared.shared.resources.space).registers .rdi = handle.address :=
    (prepared_rdi worker.entry).trans address.symm
  have instruction := Atomics.exchange_step state.shared (principal identifier) worker.handle
    ((worker.entry.registers .rsi).setWidth 32) result handle
    ((prepared worker.entry).snapshot state.shared.shared.resources.space) success authorized rfl operand
    (prepared_replacement worker.entry) (exchanging_decode _ _ valid.executable)
  simp [dispatch, live, phase, exchanging_decode _ _ valid.executable, authorized,
    prepared_rdi, prepared_replacement, address, success, instruction, exchange_context, Except.mapError]

theorem dispatch_completed (state : State) (identifier : Nat) (worker : Worker) (old : BitVec 32) (context : Context)
    (live : state.workers identifier = some worker) (phase : worker.phase = .completed old context) :
    dispatch state identifier = .error .alreadyCompleted := by
  simp [dispatch, live, phase]

theorem dispatch_wellFormed (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) : WellFormed result.1 := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    cases phase : worker.phase with
    | preparing context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_preparing _ _ _ _ found workerValid phase))
      rw [same]
      exact replace_wellFormed state identifier worker _ valid found workerValid.with_exchanging
    | returning old context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ _ found workerValid phase))
      rw [same]
      exact replace_wellFormed state identifier worker _ valid found (workerValid.with_completed old)
    | completed old context => rw [dispatch_completed _ _ _ _ _ found phase] at success; cases success
    | exchanging context =>
      obtain ⟨handle, authorized, _⟩ := workerValid.authorized
      obtain ⟨shared, exchangedOk⟩ := Atomics.exchange_enabled _ _ _ handle
        ((worker.entry.registers .rsi).setWidth 32) valid.1 authorized
      have same := Except.ok.inj (success.symm.trans (dispatch_exchanging _ _ _ _ _ found workerValid phase exchangedOk))
      have keeps := exchange_keeps exchangedOk
      have history : Atomics.History state.shared shared.1 := .next (.exchange exchangedOk) .refl
      have frame : ∀ query peer, state.workers query = some peer → WorkerValid shared.1 query peer := by
        intro query peer live
        exact ((valid.2 _ _ live).2).frame valid.1 history ⟨congrFun keeps.1 _, congrFun keeps.2 _, congrFun keeps.2 _⟩
      rw [same]
      refine ⟨Atomics.exchange_wellFormed _ _ _ _ _ valid.1 exchangedOk, ?_⟩
      intro query peer live
      by_cases selected : query = identifier
      · subst query
        simp [replace] at live
        cases live
        exact ⟨(valid.2 _ _ found).1, (frame identifier worker found).with_returning shared.2⟩
      · have beforeAt : state.workers query = some peer := by simpa [replace, selected] using live
        exact ⟨(valid.2 _ _ beforeAt).1, frame query peer beforeAt⟩

theorem dispatch_enabled (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (unfinished : ∀ old context, worker.phase ≠ .completed old context) :
    ∃ result, dispatch state identifier = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  cases phase : worker.phase with
  | preparing context => exact ⟨_, dispatch_preparing _ _ _ _ live workerValid phase⟩
  | returning old context => exact ⟨_, dispatch_returning _ _ _ _ _ live workerValid phase⟩
  | completed old context => exact False.elim (unfinished old context phase)
  | exchanging context =>
    obtain ⟨handle, authorized, _⟩ := workerValid.authorized
    obtain ⟨shared, exchangedOk⟩ := Atomics.exchange_enabled _ _ _ handle
      ((worker.entry.registers .rsi).setWidth 32) valid.1 authorized
    exact ⟨_, dispatch_exchanging _ _ _ _ _ live workerValid phase exchangedOk⟩

end EDSL.OS.AtomicThreads
