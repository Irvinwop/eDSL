/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Effects

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

/-- No environment action may prematurely close an internal worker handle or
finish a worker loan. Scheduling and lifecycle operations own those resources. -/
inductive Step : State → State → Prop where
  | spawn {before parent start available result}
      (success : AtomicThreads.spawn before parent start available = .ok result) : Step before result.1
  | dispatch {before identifier result}
      (success : AtomicThreads.dispatch before identifier = .ok result) : Step before result.1
  | join {before parent identifier result}
      (success : AtomicThreads.join before parent identifier = .ok result) : Step before result.1
  | mutate {before operation result}
      (success : AtomicThreads.mutate before operation = .ok result) : Step before result.1
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

theorem History.wellFormed {before after : State} (history : History before after) (valid : WellFormed before) :
    WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem Step.atomics {before after : State} (step : Step before after) (valid : WellFormed before) :
    Atomics.History before.shared after.shared := by
  cases step with
  | spawn success => exact spawn_history _ _ _ _ _ success
  | dispatch success => exact dispatch_history _ _ _ valid success
  | join success => exact join_history _ _ _ _ success
  | mutate success => exact mutate_history _ _ _ success
  | idle => exact .refl

theorem atomics_append {before middle after : Atomics.State}
    (first : Atomics.History before middle) (last : Atomics.History middle after) : Atomics.History before after := by
  induction first with
  | refl => exact last
  | next first _ induction => exact .next first (induction last)

theorem History.atomics {before after : State} (history : History before after) (valid : WellFormed before) :
    Atomics.History before.shared after.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction => exact atomics_append (first.atomics valid) (induction (first.wellFormed valid))

/-- Surviving worker IDs retain their published input context and any old word
already captured by XCHG. The current shared word is intentionally absent. -/
def Advances (before after : State) : Prop :=
  before.nextThread ≤ after.nextThread ∧ ∀ identifier, identifier < before.nextThread → ∀ worker,
    after.workers identifier = some worker → ∃ previous, before.workers identifier = some previous ∧
      previous.entry = worker.entry ∧
      ∀ old, previous.captured = some old → worker.captured = some old

theorem advances_refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ worker live => ⟨worker, live, rfl, fun _ captured => captured⟩⟩

theorem advances_trans {before middle after : State} (first : Advances before middle)
    (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below worker live
  obtain ⟨previous, previousAt, entry, captured⟩ := last.2 identifier (by have next := first.1; omega) worker live
  obtain ⟨original, originalAt, oldEntry, oldCaptured⟩ := first.2 identifier below previous previousAt
  exact ⟨original, originalAt, oldEntry.trans entry, fun old observed => captured old (oldCaptured old observed)⟩

theorem dispatch_advances (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : WellFormed state) (success : dispatch state identifier = .ok result) : Advances state result.1 := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ valid success
  have one (phase : Phase)
      (stable : ∀ old, worker.captured = some old → ({ worker with phase := phase }).captured = some old) :
      Advances state (replace state identifier (some { worker with phase := phase })) := by
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ current found
    by_cases selected : query = identifier
    · subst query
      simp [replace] at found
      cases found
      exact ⟨worker, live, rfl, stable⟩
    · exact ⟨current, by simpa [replace, selected] using found, rfl, fun _ captured => captured⟩
  cases effect with
  | preparing phase => exact one _ (by intro old captured; simp [Worker.captured, phase] at captured)
  | exchanging phase _ => exact one _ (by intro old captured; simp [Worker.captured, phase] at captured)
  | returning phase =>
    apply one
    intro old captured
    simpa only [Worker.captured, phase] using captured

theorem Step.advances {before after : State} (step : Step before after) (valid : WellFormed before) :
    Advances before after := by
  cases step with
  | spawn success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ _ _ success
    rw [same]
    refine ⟨by simp [install], ?_⟩
    intro identifier below worker live
    have old : identifier ≠ before.nextThread := by omega
    exact ⟨worker, by simpa [install, old] using live, rfl, fun _ captured => captured⟩
  | dispatch success => exact dispatch_advances _ _ _ valid success
  | join success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
    rw [same]
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ worker live
    dsimp only [replace] at live
    split at live
    · cases live
    · exact ⟨worker, live, rfl, fun _ captured => captured⟩
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

theorem joined_captured_value {before after : State} (history : History before after)
    (valid : WellFormed before) (identifier : Nat) (worker : Worker) (old : BitVec 32)
    (live : before.workers identifier = some worker) (captured : worker.captured = some old)
    (parent : Nat) (result : State × Word) (joined : join after parent identifier = .ok result) :
    result.2 = old.setWidth 64 := by
  obtain ⟨current, value, currentAt, observed, returned⟩ := join_result _ _ _ _ (history.wellFormed valid) joined
  obtain ⟨original, originalAt, _, stable⟩ := (history.advances valid).2 identifier
    (valid.2 _ _ live).1 current currentAt
  have same := Option.some.inj (originalAt.symm.trans live)
  cases same
  have equal := Option.some.inj ((stable old captured).symm.trans observed)
  rwa [← equal] at returned

/-- Every successful later join returns exactly the actual XCHG event's old
word, despite arbitrary intervening admitted peer/lifecycle/resource actions. -/
theorem dispatched_join_value {before middle after : State} (identifier : Nat) (event : AtomicEvent)
    (valid : WellFormed before) (dispatched : dispatch before identifier = .ok (middle, some event))
    (history : History middle after) (parent : Nat) (result : State × Word)
    (joined : join after parent identifier = .ok result) : result.2 = event.before.setWidth 64 := by
  obtain ⟨_, worker, _, live, _, _, _, _, captured⟩ := dispatch_atomic_spec _ _ _ _ valid dispatched
  exact joined_captured_value history (dispatch_wellFormed _ _ _ valid dispatched) identifier worker event.before
    live captured parent result joined

def Revoked (state : State) (identifier : Nat) : Prop :=
  identifier < state.nextThread ∧ state.workers identifier = none

theorem Revoked.persists {before after : State} {identifier : Nat} (revoked : Revoked before identifier)
    (valid : WellFormed before) (history : History before after) : Revoked after identifier := by
  have advances := history.advances valid
  refine ⟨by have a := revoked.1; have b := advances.1; omega, ?_⟩
  cases found : after.workers identifier with
  | none => rfl
  | some worker =>
    obtain ⟨original, originalAt, _, _⟩ := advances.2 identifier revoked.1 worker found
    rw [revoked.2] at originalAt
    cases originalAt

theorem join_revokes_thread (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : Revoked result.1 identifier := by
  obtain ⟨worker, _, _, _, _, _, live, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨(valid.2 _ _ live).1, by simp [replace]⟩

theorem joined_for_history {before after : State} {middle : State × Word} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle)
    (history : History middle.1 after) : Revoked after identifier :=
  (join_revokes_thread before parent identifier middle valid joined).persists
    (join_wellFormed _ _ _ _ valid joined) history

theorem joined_resources_for_history {before after : State} {middle : State × Word} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle)
    (history : History middle.1 after) :
    ∃ worker, before.workers identifier = some worker ∧ Atomics.Revoked after.shared worker.handle ∧
      Borrowing.Revoked after.shared.shared worker.codeLoan ∧ Borrowing.Revoked after.shared.shared worker.stackLoan := by
  obtain ⟨worker, live, handle, code, stack⟩ := join_revokes _ _ _ _ valid joined
  have nextValid := join_wellFormed _ _ _ _ valid joined
  have atomicHistory := history.atomics nextValid
  exact ⟨worker, live, handle.persists atomicHistory,
    code.persists nextValid.1.shared atomicHistory.borrowing,
    stack.persists nextValid.1.shared atomicHistory.borrowing⟩

end EDSL.OS.AtomicThreads
