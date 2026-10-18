/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Join

namespace EDSL.OS.AtomicThreads64

theorem mutate_ok (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    ∃ shared, Atomics64.mutate state.shared operation = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  cases changed : Atomics64.mutate state.shared operation with
  | error fault => simp [mutate, changed, Except.mapError] at success
  | ok shared =>
    simp [mutate, changed, Except.mapError] at success
    exact ⟨shared, rfl, success.symm⟩

theorem mutate_history (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    Atomics64.History state.shared [none] result.1.shared := by
  obtain ⟨_, changed, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact .next (.mutate changed) .refl

theorem mutate_keeps (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.cells = state.shared.cells ∧
      result.1.shared.legacy.shared.loans = state.shared.legacy.shared.loans := by
  obtain ⟨shared, changed, same⟩ := mutate_ok _ _ _ success
  obtain ⟨_, legacy, mutation, outerEq⟩ := Atomics64.mutate_ok _ _ _ changed
  obtain ⟨_, borrowing, borrowed, legacyEq⟩ := Atomics.mutate_ok _ _ _ mutation
  obtain ⟨_, _, _, borrowEq⟩ := Borrowing.mutate_ok _ _ _ borrowed
  rw [same, outerEq]
  exact ⟨rfl, rfl,
    (congrArg (fun pair : Atomics.State × Option Ownership.Ticket => pair.1.shared.loans) legacyEq).trans
      (congrArg (fun pair : Borrowing.State × Option Ownership.Ticket => pair.1.loans) borrowEq)⟩

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (valid : WellFormed state)
    (success : mutate state operation = .ok result) : WellFormed result.1 := by
  have history := mutate_history _ _ _ success
  have keeps := mutate_keeps _ _ _ success
  obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
  rw [same] at history keeps ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro identifier worker live
  exact ⟨(valid.2 _ _ live).1, ((valid.2 _ _ live).2).frame valid.1 history
    ⟨congrFun keeps.1 _, congrFun keeps.2.1 _, congrFun keeps.2.2 _, congrFun keeps.2.2 _⟩⟩

theorem retire_ok (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (success : retire state owner cell = .ok after) :
    owner = 0 ∧ ∃ shared, Atomics64.retire state.shared owner cell = .ok shared ∧
      after = { state with shared := shared } := by
  by_cases root : owner = 0
  · have guard : ¬owner ≠ 0 := by simp [root]
    cases changed : Atomics64.retire state.shared owner cell with
    | error fault => simp [retire, guard, changed, Except.mapError] at success
    | ok shared =>
      simp [retire, guard, changed, Except.mapError] at success
      exact ⟨root, shared, rfl, success.symm⟩
  · simp [retire, root] at success

/-- Every live worker, including a completed one, prevents retirement of its
cell. Successful JOIN removes that particular pinned handle. -/
theorem retire_in_use_denied (state : State) (owner : Nat) (cell : Atomics64.CellId64)
    (valid : WellFormed state) (identifier : Nat) (worker : Worker)
    (live : state.workers identifier = some worker) (sameCell : worker.cell = cell) (after : State) :
    retire state owner cell ≠ .ok after := by
  intro success
  obtain ⟨_, shared, retired, _⟩ := retire_ok _ _ _ _ success
  obtain ⟨handle, _, atHandle, _, link, _⟩ := ((valid.2 _ _ live).2).handle
  have excluded := Atomics64.retire_no_handles _ _ _ _ valid.1 retired worker.handle handle atHandle
  exact excluded (link.trans sameCell)

theorem retire_wellFormed (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (valid : WellFormed state) (success : retire state owner cell = .ok after) : WellFormed after := by
  obtain ⟨_, shared, retired, same⟩ := retire_ok _ _ _ _ success
  have history : Atomics64.History state.shared [none] shared := .next (.retire retired) .refl
  obtain ⟨_, _, _, sharedEq⟩ := Atomics64.retire_ok _ _ _ _ retired
  rw [same]
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro identifier worker live
  have previous := (valid.2 _ _ live).2
  have other : worker.cell ≠ cell := by
    intro equal
    exact retire_in_use_denied state owner cell valid identifier worker live equal _ success
  refine ⟨(valid.2 _ _ live).1, previous.frame valid.1 history ?_⟩
  rw [sharedEq]
  exact ⟨rfl, by simp [Atomics64.removeCell, other], rfl, rfl⟩

theorem retire_history (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (success : retire state owner cell = .ok after) :
    Atomics64.History state.shared [none] after.shared := by
  obtain ⟨_, _, retired, same⟩ := retire_ok _ _ _ _ success
  rw [same]
  exact .next (.retire retired) .refl

end EDSL.OS.AtomicThreads64
