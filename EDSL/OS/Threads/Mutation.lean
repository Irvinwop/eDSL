/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Join

namespace EDSL.OS.Threads

theorem mutate_ok (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) :
    ∃ shared, Borrowing.mutate state.shared operation = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  cases changed : Borrowing.mutate state.shared operation with
  | error fault => simp [mutate, changed, Except.mapError] at success
  | ok shared =>
    simp [mutate, changed, Except.mapError] at success
    exact ⟨shared, rfl, success.symm⟩

theorem mutate_history (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) : Borrowing.History state.shared result.1.shared := by
  obtain ⟨_, changed, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact .next (.mutate changed) .refl

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (valid : WellFormed state) (success : mutate state operation = .ok result) : WellFormed result.1 := by
  have history := mutate_history state operation result success
  obtain ⟨shared, changed, same⟩ := mutate_ok _ _ _ success
  obtain ⟨_, _, _, resourcesSame⟩ := Borrowing.mutate_ok _ _ _ changed
  rw [same] at history ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro identifier worker live
  obtain ⟨below, workerValid⟩ := valid.2 _ _ live
  refine ⟨below, workerValid.frame valid.1 history ?_⟩
  rw [resourcesSame]
  exact fun _ _ => rfl

end EDSL.OS.Threads
