/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Mutation

namespace EDSL.OS.Threads

/-- Environment and scheduler actions admitted by this read-worker profile.
There is deliberately no operation to finish an internal worker loan early. -/
inductive Step : State → State → Prop where
  | spawn {before parent start available result}
      (success : Threads.spawn before parent start available = .ok result) : Step before result.1
  | dispatch {before identifier after}
      (success : Threads.dispatch before identifier = .ok after) : Step before after
  | join {before parent identifier result}
      (success : Threads.join before parent identifier = .ok result) : Step before result.1
  | mutate {before operation result}
      (success : Threads.mutate before operation = .ok result) : Step before result.1
  | idle {state} : Step state state

inductive History : State → State → Prop where
  | refl {state} : History state state
  | next {before middle after} (first : Step before middle) (tail : History middle after) : History before after

theorem Step.wellFormed {before after : State} (step : Step before after) (valid : WellFormed before) :
    WellFormed after := by
  cases step with
  | spawn success => exact spawn_wellFormed _ _ _ _ _ valid success
  | dispatch success => exact dispatch_wellFormed _ _ _ valid success
  | join success => exact join_wellFormed _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | idle => exact valid

theorem Step.borrowing {before after : State} (step : Step before after) (valid : WellFormed before) :
    Borrowing.History before.shared after.shared := by
  cases step with
  | spawn success => exact spawn_history _ _ _ _ _ success
  | dispatch success => rw [(dispatch_frame _ _ _ valid success).1]; exact .refl
  | join success => exact join_history _ _ _ _ success
  | mutate success => exact mutate_history _ _ _ success
  | idle => exact .refl

theorem History.wellFormed {before after : State} (history : History before after) (valid : WellFormed before) :
    WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem borrowing_append {before middle after : Borrowing.State}
    (first : Borrowing.History before middle) (last : Borrowing.History middle after) :
    Borrowing.History before after := by
  induction first with
  | refl => exact last
  | next step _ induction => exact .next step (induction last)

theorem History.borrowing {before after : State} (history : History before after) (valid : WellFormed before) :
    Borrowing.History before.shared after.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction => exact borrowing_append (first.borrowing valid) (induction (first.wellFormed valid))

/-- Issued thread IDs cannot be installed again. A surviving worker retains the
word published at spawn, independent of subsequent scheduler selections. -/
def Advances (before after : State) : Prop :=
  before.nextThread ≤ after.nextThread ∧ ∀ identifier, identifier < before.nextThread → ∀ worker,
    after.workers identifier = some worker →
      ∃ previous, before.workers identifier = some previous ∧ previous.value = worker.value

theorem advances_refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ worker live => ⟨worker, live, rfl⟩⟩

theorem advances_trans {before middle after : State} (first : Advances before middle)
    (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below worker live
  have frontier := first.1
  obtain ⟨previous, old, value⟩ := last.2 identifier (by omega) worker live
  obtain ⟨original, originalAt, originalValue⟩ := first.2 identifier below previous old
  exact ⟨original, originalAt, originalValue.trans value⟩

theorem dispatch_advances (state : State) (identifier : Nat) (result : State)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) : Advances state result := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    cases phase : worker.phase with
    | loading context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_loading _ _ _ _ found workerValid phase))
      rw [same]
      refine ⟨Nat.le_refl _, ?_⟩
      intro query _ current live
      by_cases selected : query = identifier
      · subst query
        simp [replace] at live
        cases live
        exact ⟨worker, found, rfl⟩
      · exact ⟨current, by simpa [replace, selected] using live, rfl⟩
    | returning context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ found workerValid phase))
      rw [same]
      refine ⟨Nat.le_refl _, ?_⟩
      intro query _ current live
      by_cases selected : query = identifier
      · subst query
        simp [replace] at live
        cases live
        exact ⟨worker, found, rfl⟩
      · exact ⟨current, by simpa [replace, selected] using live, rfl⟩
    | completed context => rw [dispatch_completed _ _ _ _ found phase] at success; cases success

theorem Step.advances {before after : State} (step : Step before after) (valid : WellFormed before) :
    Advances before after := by
  cases step with
  | spawn success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ _ _ success
    rw [same]
    refine ⟨by simp [install], ?_⟩
    intro identifier below worker live
    have old : identifier ≠ before.nextThread := by omega
    exact ⟨worker, by simpa [install, old] using live, rfl⟩
  | dispatch success => exact dispatch_advances _ _ _ valid success
  | @join parent identifier result success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
    rw [same]
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ worker live
    by_cases removed : query = identifier
    · subst query; simp [replace] at live
    · exact ⟨worker, by simpa [replace, removed] using live, rfl⟩
  | mutate success =>
    obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
    rw [same]
    exact advances_refl _
  | idle => exact advances_refl _

theorem History.advances {before after : State} (history : History before after) (valid : WellFormed before) :
    Advances before after := by
  induction history with
  | refl => exact advances_refl _
  | next first _ induction => exact advances_trans (first.advances valid) (induction (first.wellFormed valid))

/-- Every successful join after any admitted history returns the original
published word, even with intervening peers, managed mutations and idle delays. -/
theorem joined_value_for_history {before after : State} (history : History before after)
    (valid : WellFormed before) (identifier : Nat) (worker : Worker)
    (live : before.workers identifier = some worker) (parent : Nat) (result : State × X86.Word)
    (joined : join after parent identifier = .ok result) : result.2 = worker.value.setWidth 64 := by
  obtain ⟨current, found, value⟩ := join_result _ _ _ _ (history.wellFormed valid) joined
  obtain ⟨original, old, originalValue⟩ := (history.advances valid).2 identifier
    (valid.2 _ _ live).1 current found
  have same := Option.some.inj (old.symm.trans live)
  cases same
  exact value.trans (congrArg (fun word : BitVec 32 => word.setWidth 64) originalValue.symm)

def Revoked (state : State) (identifier : Nat) : Prop :=
  identifier < state.nextThread ∧ state.workers identifier = none

theorem Revoked.persists {before after : State} {identifier : Nat} (revoked : Revoked before identifier)
    (valid : WellFormed before) (history : History before after) : Revoked after identifier := by
  have advances := history.advances valid
  have bound := revoked.1
  have frontier := advances.1
  refine ⟨by omega, ?_⟩
  cases found : after.workers identifier with
  | none => rfl
  | some worker =>
    obtain ⟨_, original, _⟩ := advances.2 identifier revoked.1 worker found
    rw [revoked.2] at original
    cases original

theorem join_thread_revokes (state : State) (parent identifier : Nat) (result : State × X86.Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : Revoked result.1 identifier := by
  obtain ⟨worker, _, _, _, _, found, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨(valid.2 identifier worker found).1, by simp [replace]⟩

theorem joined_for_history {before middle after : State} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok (middle, result))
    (history : History middle after) : Revoked after identifier :=
  (join_thread_revokes before parent identifier (middle, result) valid joined).persists
    (join_wellFormed _ _ _ _ valid joined) history

end EDSL.OS.Threads
