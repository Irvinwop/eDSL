/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Join

namespace EDSL.OS.CounterThreads

theorem mutate_ok (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) :
    ∃ shared, Atomics.mutate state.shared operation = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  cases changed : Atomics.mutate state.shared operation with
  | error fault => simp [mutate, changed, Except.mapError] at success
  | ok shared =>
    simp [mutate, changed, Except.mapError] at success
    exact ⟨shared, rfl, success.symm⟩

theorem mutate_history (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) : Atomics.History state.shared result.1.shared := by
  obtain ⟨_, changed, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact .next (.mutate changed) .refl

theorem mutate_keeps (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.shared.loans = state.shared.shared.loans := by
  obtain ⟨shared, changed, same⟩ := mutate_ok _ _ _ success
  obtain ⟨_, borrowing, borrowed, atomicEq⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, _, _, borrowEq⟩ := Borrowing.mutate_ok _ _ _ borrowed
  rw [same]
  refine ⟨congrArg (fun pair : Atomics.State × Option Ownership.Ticket => pair.1.handles) atomicEq, ?_⟩
  exact (congrArg (fun pair : Atomics.State × Option Ownership.Ticket => pair.1.shared.loans) atomicEq).trans
    (congrArg (fun pair : Borrowing.State × Option Ownership.Ticket => pair.1.loans) borrowEq)

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (valid : WellFormed state) (success : mutate state operation = .ok result) : WellFormed result.1 := by
  have history := mutate_history _ _ _ success
  have keeps := mutate_keeps _ _ _ success
  obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
  rw [same] at history keeps ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro identifier worker live
  exact ⟨(valid.2 _ _ live).1, ((valid.2 _ _ live).2).frame valid.1 history
    ⟨congrFun keeps.1 _, congrFun keeps.2 _, congrFun keeps.2 _⟩⟩

end EDSL.OS.CounterThreads
