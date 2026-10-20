/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Mutation

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

/-- Inversion facts for a successful actual-instruction dispatch. The
exchanging case retains the checked OS operation used by that instruction. -/
inductive DispatchEffect (state : State) (identifier : Nat) (worker : Worker) : State × Option AtomicEvent → Prop where
  | preparing {context} (phase : worker.phase = .preparing context) :
      DispatchEffect state identifier worker (replace state identifier
        (some { worker with phase := .exchanging (prepared worker.entry) }), none)
  | exchanging {context result} (phase : worker.phase = .exchanging context)
      (success : Atomics.exchange state.shared (principal identifier) worker.handle
        ((worker.entry.registers .rsi).setWidth 32) = .ok result) :
      DispatchEffect state identifier worker
        ({ replace state identifier (some { worker with phase := .returning result.2 (exchanged worker.entry result.2) }) with
          shared := result.1 }, some ⟨worker.entry.registers .rdi, result.2, (worker.entry.registers .rsi).setWidth 32⟩)
  | returning {old context} (phase : worker.phase = .returning old context) :
      DispatchEffect state identifier worker (replace state identifier
        (some { worker with phase := .completed old (worker.entry.returned old worker.returnAddress) }), none)

theorem dispatch_effect (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧ DispatchEffect state identifier worker result := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    refine ⟨worker, rfl, ?_⟩
    cases phase : worker.phase with
    | preparing context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_preparing _ _ _ _ found workerValid phase))
      rw [same]
      exact .preparing phase
    | returning old context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ _ found workerValid phase))
      rw [same]
      exact .returning phase
    | completed old context => rw [dispatch_completed _ _ _ _ _ found phase] at success; cases success
    | exchanging context =>
      obtain ⟨handle, authorized, _⟩ := workerValid.authorized
      obtain ⟨shared, exchangedOk⟩ := Atomics.exchange_enabled _ _ _ handle
        ((worker.entry.registers .rsi).setWidth 32) valid.1 authorized
      have same := Except.ok.inj (success.symm.trans (dispatch_exchanging _ _ _ _ _ found workerValid phase exchangedOk))
      rw [same]
      exact .exchanging phase exchangedOk

theorem dispatch_history (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    Atomics.History state.shared result.1.shared := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ valid success
  cases effect with
  | preparing _ | returning _ => exact .refl
  | exchanging _ exchangedOk => exact .next (.exchange exchangedOk) .refl

theorem dispatch_frame (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    result.1.nextThread = state.nextThread ∧
    ∀ query, query ≠ identifier → result.1.workers query = state.workers query := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ valid success
  cases effect <;> exact ⟨rfl, fun query different => by simp [replace, different]⟩

theorem dispatch_keeps (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.shared.loans = state.shared.shared.loans := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ valid success
  cases effect with
  | preparing _ | returning _ => exact ⟨rfl, rfl⟩
  | exchanging _ exchangedOk => exact exchange_keeps exchangedOk

/-- Every emitted event reads the current shared word and binds its old value
to the selected worker's private state. A later peer may replace the cell. -/
theorem dispatch_atomic_spec (state : State) (identifier : Nat) (after : State) (event : AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok (after, some event)) :
    ∃ worker current, state.workers identifier = some worker ∧ after.workers identifier = some current ∧
      event.address = worker.entry.registers .rdi ∧ event.after = (worker.entry.registers .rsi).setWidth 32 ∧
      loadDWord (toMemory state.shared.shared.resources.space) event.address = .ok event.before ∧
      loadDWord (toMemory after.shared.shared.resources.space) event.address = .ok event.after ∧
      current.captured = some event.before := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ valid success
  cases effect with
  | @exchanging context result phase exchangedOk =>
    obtain ⟨handle, authorized, transition⟩ := Atomics.exchange_sound _ _ _ _ _ exchangedOk
    obtain ⟨other, otherAuthorized, address⟩ := ((valid.2 _ _ live).2).authorized
    have same := Except.ok.inj (authorized.symm.trans otherAuthorized)
    subst other
    refine ⟨worker, { worker with phase := .returning result.2 (exchanged worker.entry result.2) },
      live, by simp [replace], rfl, rfl, ?_, ?_, rfl⟩
    · simpa only [address] using transition.2.2.1
    · simpa only [address] using transition.readback

end EDSL.OS.AtomicThreads
