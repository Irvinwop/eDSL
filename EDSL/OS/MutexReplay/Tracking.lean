/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Invariant

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem action_acquire_none (worker : Worker) (selected : action worker = .ok .acquire) : worker.guard = none := by
  cases phase : worker.phase <;> cases held : worker.guard <;> simp [action, phase, held] at selected ⊢

theorem Tracked.replace {state : State} {identifier : Nat} {worker after : Worker} {shared : Mutex.State}
    (tracked : Tracked state) (live : state.workers[identifier]? = some worker)
    (same : shared.mutex = state.shared.mutex) (guard : after.guard = worker.guard) :
    Tracked ⟨shared, state.workers.set identifier after⟩ := by
  intro record lease registered held
  obtain ⟨query, previous, found, owns⟩ := tracked record lease (same ▸ registered) held
  by_cases own : query = identifier
  · subst query
    have equal := Option.some.inj (found.symm.trans live)
    subst previous
    have bound := (List.getElem_of_getElem? live).1
    exact ⟨identifier, after, List.getElem?_set_self bound, guard.trans owns⟩
  · exact ⟨query, previous, by simpa only [List.getElem?_set_ne (Ne.symm own)] using found, owns⟩

theorem tracked_acquired (state : State) (identifier : Nat) (worker : Worker)
    (attempt : Mutex.Attempt) (context : Context)
    (tracked : Tracked state) (live : state.workers[identifier]? = some worker)
    (guard : worker.guard = none) (success : Mutex.tryAcquire state.shared (principal identifier) = .ok attempt) :
    Tracked ⟨attempt.state, state.workers.set identifier
      (evolved worker ⟨attempt.state, context, attempt.acquired, some attempt.event, false⟩)⟩ := by
  obtain ⟨record, exchanged, _, _, branches⟩ := Mutex.tryAcquire_ok _ _ _ success
  rcases branches with ⟨_, same⟩ | ⟨_, same⟩
  · rw [same]
    intro current lease registered held
    simp only [Option.some.injEq] at registered
    cases registered
    have equal := Option.some.inj held
    subst lease
    have bound := (List.getElem_of_getElem? live).1
    exact ⟨identifier, _, List.getElem?_set_self bound, rfl⟩
  · rw [same]
    apply tracked.replace live rfl
    exact guard.symm

theorem perform_tracked (state : State) (identifier : Nat) (worker : Worker) (operation : Action) (result : Result)
    (tracked : Tracked state) (live : state.workers[identifier]? = some worker)
    (selected : action worker = .ok operation) (success : perform state.shared identifier worker operation = .ok result) :
    Tracked ⟨result.shared, state.workers.set identifier (evolved worker result)⟩ := by
  cases perform_effect _ _ _ _ _ success with
  | plain instruction context ran => exact tracked.replace live rfl rfl
  | acquire record attempt context found operand replacement acquired ran =>
    exact tracked_acquired state identifier worker attempt context tracked live (action_acquire_none _ selected) acquired
  | load guard record value context authorized operand loaded ran => exact tracked.replace live rfl rfl
  | store guard record after context authorized operand stored ran =>
    obtain ⟨_, _, _, _, same⟩ := Mutex.guardStore_ok _ _ _ _ _ stored
    exact tracked.replace live (by rw [same]) rfl
  | release guard record released context authorized operand replacement finished ran =>
    obtain ⟨_, _, _, _, _, _, _, same⟩ := Mutex.release_ok _ _ _ _ finished
    rw [same]
    intro current lease registered held
    simp only [Option.some.injEq] at registered
    cases registered
    cases held
  | ret context ran => exact tracked.replace live rfl rfl

end EDSL.OS.MutexReplay
