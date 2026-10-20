/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Advance

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

theorem dispatch_ok (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (success : dispatch state identifier = .ok result) :
    ∃ worker advanced, state.workers identifier = some worker ∧ advance state identifier worker = .ok advanced ∧
      result = ({ replace state identifier (some advanced.worker) with shared := advanced.shared }, advanced.event) := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    cases selected : advance state identifier worker with
    | error fault => simp [dispatch, found, selected] at success
    | ok advanced =>
      simp [dispatch, found, selected] at success
      exact ⟨worker, advanced, rfl, selected, success.symm⟩

theorem AdvanceEffect.history {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) : Atomics.History state.shared result.shared := by
  cases effect with
  | adding _ success => exact Atomics.fetchAdd_history _ _ _ _ _ success
  | entry _ | preparing _ | backedge _ | finishing _ | returning _ => exact .refl

theorem AdvanceEffect.keeps {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) :
    result.shared.handles = state.shared.handles ∧ result.shared.shared.loans = state.shared.shared.loans := by
  cases effect with
  | adding _ success => exact fetchAdd_keeps success
  | entry _ | preparing _ | backedge _ | finishing _ | returning _ => exact ⟨rfl, rfl⟩

theorem WorkerValid.evolved {shared : Atomics.State} {identifier : Nat} {worker : Worker} (context : Context)
    (valid : WorkerValid shared identifier worker) (privateContext : PrivateValid (evolved worker context)) :
    WorkerValid shared identifier (evolved worker context) :=
  ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.executable,
    valid.target, valid.canonical, privateContext⟩

theorem AdvanceEffect.workerValid {state : State} {identifier : Nat} {worker : Worker} {result : Advance}
    (effect : AdvanceEffect state identifier worker result) (sharedValid : Atomics.WellFormed state.shared)
    (valid : WorkerValid state.shared identifier worker) : WorkerValid result.shared identifier result.worker := by
  have kept := effect.keeps
  have retained : Retains state.shared result.shared worker :=
    ⟨congrFun kept.1 _, congrFun kept.2 _, congrFun kept.2 _⟩
  have frame := valid.frame sharedValid effect.history retained
  cases effect with
  | entry phase => exact frame.evolved _ (entry_private worker valid.privateContext phase)
  | preparing phase => exact frame.evolved _ (preparing_private worker valid.privateContext phase)
  | adding phase _ => exact frame.evolved _ (adding_private worker _ valid.privateContext phase)
  | backedge phase => exact frame.evolved _ (backedge_private worker valid.privateContext phase)
  | finishing phase => exact frame.evolved _ (finishing_private worker valid.privateContext phase)
  | returning phase => exact frame.evolved _ (returning_private worker valid.privateContext phase)

theorem dispatch_history (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    Atomics.History state.shared result.1.shared := by
  obtain ⟨worker, advanced, found, selected, same⟩ := dispatch_ok _ _ _ success
  have effect := advance_effect state identifier worker advanced valid.1 (valid.2 _ _ found).2 selected
  rw [same]
  exact effect.history

theorem dispatch_keeps (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.shared.loans = state.shared.shared.loans := by
  obtain ⟨worker, advanced, found, selected, same⟩ := dispatch_ok _ _ _ success
  have effect := advance_effect state identifier worker advanced valid.1 (valid.2 _ _ found).2 selected
  rw [same]
  exact effect.keeps

theorem dispatch_wellFormed (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) : WellFormed result.1 := by
  obtain ⟨worker, advanced, found, selected, same⟩ := dispatch_ok _ _ _ success
  have workerValid := (valid.2 _ _ found).2
  have effect := advance_effect state identifier worker advanced valid.1 workerValid selected
  have keeps := effect.keeps
  have history := effect.history
  rw [same]
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro query current live
  by_cases own : query = identifier
  · subst query
    simp [replace] at live
    cases live
    exact ⟨(valid.2 _ _ found).1, effect.workerValid valid.1 workerValid⟩
  · have previous : state.workers query = some current := by simpa [replace, own] using live
    have currentValid := (valid.2 _ _ previous).2
    exact ⟨(valid.2 _ _ previous).1,
      currentValid.frame valid.1 history ⟨congrFun keeps.1 _, congrFun keeps.2 _, congrFun keeps.2 _⟩⟩

theorem dispatch_enabled (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (unfinished : worker.phase ≠ .completed) : ∃ result, dispatch state identifier = .ok result := by
  obtain ⟨advanced, success⟩ := advance_enabled state identifier worker valid.1 (valid.2 _ _ live).2 unfinished
  exact ⟨({ replace state identifier (some advanced.worker) with shared := advanced.shared }, advanced.event),
    by simp [dispatch, live, success]⟩

theorem dispatch_frame (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (success : dispatch state identifier = .ok result) :
    result.1.nextThread = state.nextThread ∧ ∀ query, query ≠ identifier → result.1.workers query = state.workers query := by
  obtain ⟨_, _, _, _, same⟩ := dispatch_ok _ _ _ success
  rw [same]
  exact ⟨rfl, fun query different => by simp [replace, different]⟩

end EDSL.OS.CounterThreads
