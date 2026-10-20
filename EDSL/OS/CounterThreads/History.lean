/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Mutation
import EDSL.OS.CounterThreads.Spawn

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

/-- Worker-owned resources can be released only by checked join. No raw
outside atomic operations or internal handle/loan release actions are admitted. -/
inductive Step : State → State → Prop where
  | spawn {before parent start available result} (success : CounterThreads.spawn before parent start available = .ok result) : Step before result.1
  | dispatch {before identifier result} (success : CounterThreads.dispatch before identifier = .ok result) : Step before result.1
  | join {before parent identifier result} (success : CounterThreads.join before parent identifier = .ok result) : Step before result.1
  | mutate {before operation result} (success : CounterThreads.mutate before operation = .ok result) : Step before result.1
  | idle {state} : Step state state

inductive History : State → State → Prop where
  | refl {state} : History state state
  | next {before middle after} (first : Step before middle) (tail : History middle after) : History before after

theorem Step.wellFormed {before after : State} (step : Step before after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | spawn success => exact spawn_wellFormed _ _ _ _ _ valid success
  | dispatch success => exact dispatch_wellFormed _ _ _ valid success
  | join success => exact join_wellFormed _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | idle => exact valid

theorem History.wellFormed {before after : State} (history : History before after) (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem Step.atomics {before after : State} (step : Step before after) (valid : WellFormed before) : Atomics.History before.shared after.shared := by
  cases step with
  | spawn success => exact spawn_history _ _ _ _ _ success
  | dispatch success => exact dispatch_history _ _ _ valid success
  | join success => exact join_history _ _ _ _ success
  | mutate success => exact mutate_history _ _ _ success
  | idle => exact .refl

theorem History.atomics {before after : State} (history : History before after) (valid : WellFormed before) : Atomics.History before.shared after.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction => exact Atomics.history_append (first.atomics valid) (induction (first.wellFormed valid))

def Advances (before after : State) : Prop :=
  before.nextThread ≤ after.nextThread ∧ ∀ identifier, identifier < before.nextThread → ∀ worker,
    after.workers identifier = some worker → ∃ previous, before.workers identifier = some previous ∧ previous.entry = worker.entry

theorem advances_refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ worker live => ⟨worker, live, rfl⟩⟩

theorem advances_trans {before middle after : State} (first : Advances before middle) (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below worker live
  obtain ⟨previous, previousAt, entry⟩ := last.2 identifier (by have next := first.1; omega) worker live
  obtain ⟨original, originalAt, initial⟩ := first.2 identifier below previous previousAt
  exact ⟨original, originalAt, initial.trans entry⟩

theorem Step.advances {before after : State} (step : Step before after) (valid : WellFormed before) : Advances before after := by
  cases step with
  | spawn success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ _ _ success
    rw [same]
    refine ⟨by simp [install], ?_⟩
    intro identifier below worker live
    have old : identifier ≠ before.nextThread := by omega
    exact ⟨worker, by simpa [install, old] using live, rfl⟩
  | @dispatch identifier _ success =>
    obtain ⟨worker, advanced, found, selected, same⟩ := dispatch_ok _ _ _ success
    have effect := advance_effect _ _ _ _ valid.1 (valid.2 _ _ found).2 selected
    rw [same]
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ current live
    by_cases own : query = identifier
    · subst query
      simp [replace] at live
      cases live
      exact ⟨worker, found, by cases effect <;> rfl⟩
    · exact ⟨current, by simpa [replace, own] using live, rfl⟩
  | join success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
    rw [same]
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ worker live
    dsimp only [replace] at live
    split at live
    · cases live
    · exact ⟨worker, live, rfl⟩
  | mutate success =>
    obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
    rw [same]
    exact advances_refl _
  | idle => exact advances_refl _

theorem History.advances {before after : State} (history : History before after) (valid : WellFormed before) : Advances before after := by
  induction history with
  | refl => exact advances_refl _
  | next first _ induction => exact advances_trans (first.advances valid) (induction (first.wellFormed valid))

def Revoked (state : State) (identifier : Nat) : Prop := identifier < state.nextThread ∧ state.workers identifier = none

theorem Revoked.persists {before after : State} {identifier : Nat} (revoked : Revoked before identifier)
    (valid : WellFormed before) (history : History before after) : Revoked after identifier := by
  have advances := history.advances valid
  refine ⟨by have a := revoked.1; have b := advances.1; omega, ?_⟩
  cases found : after.workers identifier with
  | none => rfl
  | some worker =>
    obtain ⟨original, originalAt, _⟩ := advances.2 identifier revoked.1 worker found
    rw [revoked.2] at originalAt
    cases originalAt

theorem join_revokes_thread (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : Revoked result.1 identifier := by
  obtain ⟨worker, _, _, _, live, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨(valid.2 _ _ live).1, by simp [replace]⟩

theorem joined_for_history {before after : State} {middle : State × Word} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle) (history : History middle.1 after) : Revoked after identifier :=
  (join_revokes_thread before parent identifier middle valid joined).persists (join_wellFormed _ _ _ _ valid joined) history

theorem joined_resources_for_history {before after : State} {middle : State × Word} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle) (history : History middle.1 after) :
    ∃ worker, before.workers identifier = some worker ∧ Atomics.Revoked after.shared worker.handle ∧
      Borrowing.Revoked after.shared.shared worker.codeLoan ∧ Borrowing.Revoked after.shared.shared worker.stackLoan := by
  obtain ⟨worker, live, handle, code, stack⟩ := join_revokes _ _ _ _ valid joined
  have nextValid := join_wellFormed _ _ _ _ valid joined
  have atomicHistory := history.atomics nextValid
  exact ⟨worker, live, handle.persists atomicHistory,
    code.persists nextValid.1.shared atomicHistory.borrowing, stack.persists nextValid.1.shared atomicHistory.borrowing⟩

theorem idle_trace (state : State) :
    ∃ trace : Nat → State, trace 0 = state ∧ ∀ index, Step (trace index) (trace (index + 1)) :=
  ⟨fun _ => state, rfl, fun _ => .idle⟩

end EDSL.OS.CounterThreads
