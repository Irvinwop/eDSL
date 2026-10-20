/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Effects

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Managed wrappers only. Internal handles and loans can be discharged only
by join; an arbitrary lower history is never an environment action. -/
inductive Step : State → Option Atomics64.Event → State → Prop where
  | spawn {before parent start available result}
      (success : AtomicThreads64.spawn before parent start available = .ok result) :
      Step before none result.1
  | dispatch {before identifier af result}
      (success : AtomicThreads64.dispatch before identifier af = .ok result) :
      Step before result.2 result.1
  | join {before parent identifier result}
      (success : AtomicThreads64.join before parent identifier = .ok result) :
      Step before none result.1
  | mutate {before operation result}
      (success : AtomicThreads64.mutate before operation = .ok result) :
      Step before none result.1
  | retire {before owner cell after}
      (success : AtomicThreads64.retire before owner cell = .ok after) : Step before none after
  | idle {state} : Step state none state

/-- Lifecycle positions and actual instruction outputs remain explicit. This
rich history makes no value-stability claim across retirement. -/
inductive History : State → List (Option Atomics64.Event) → State → Prop where
  | refl {state} : History state [] state
  | next {before middle after label labels} (first : Step before label middle)
      (tail : History middle labels after) : History before (label :: labels) after

theorem Step.wellFormed {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | spawn success => exact spawn_wellFormed _ _ _ _ _ valid success
  | dispatch success => exact dispatch_wellFormed _ _ _ _ valid success
  | join success => exact join_wellFormed _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | retire success => exact retire_wellFormed _ _ _ _ valid success
  | idle => exact valid

theorem History.wellFormed {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

theorem History.trans {before middle after : State} {firstLabels lastLabels : List (Option Atomics64.Event)}
    (first : History before firstLabels middle) (last : History middle lastLabels after) :
    History before (firstLabels ++ lastLabels) after := by
  induction first with
  | refl => exact last
  | next first _ induction => exact .next first (induction last)

/-- Projection expands managed transactions into their successful checked
resource actions. Its existence cannot admit an unwrapped lower action. -/
theorem Step.atomics {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) :
    ∃ labels, Atomics64.History before.shared labels after.shared := by
  cases step with
  | spawn success => exact ⟨_, spawn_history _ _ _ _ _ success⟩
  | dispatch success => exact ⟨_, dispatch_history _ _ _ _ valid success⟩
  | join success => exact ⟨_, join_history _ _ _ _ success⟩
  | mutate success => exact ⟨_, mutate_history _ _ _ success⟩
  | retire success => exact ⟨_, retire_history _ _ _ _ success⟩
  | idle => exact ⟨[], .refl⟩

theorem History.atomics {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) :
    ∃ lowerLabels, Atomics64.History before.shared lowerLabels after.shared := by
  induction history with
  | refl => exact ⟨[], .refl⟩
  | next first _ induction =>
    obtain ⟨initial, firstHistory⟩ := first.atomics valid
    obtain ⟨rest, tailHistory⟩ := induction (first.wellFormed valid)
    exact ⟨initial ++ rest, firstHistory.trans tailHistory⟩

/-- Surviving thread identities retain the published input and every captured
actual event. Shared RAM is intentionally absent: peers may update it. -/
def Advances (before after : State) : Prop :=
  before.nextThread ≤ after.nextThread ∧ ∀ identifier, identifier < before.nextThread → ∀ worker,
    after.workers identifier = some worker → ∃ previous, before.workers identifier = some previous ∧
      previous.entry = worker.entry ∧
      ∀ event, previous.captured = some event → worker.captured = some event

theorem Advances.refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ worker live => ⟨worker, live, rfl, fun _ captured => captured⟩⟩

theorem Advances.trans {before middle after : State} (first : Advances before middle)
    (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below worker live
  obtain ⟨previous, previousAt, entry, captured⟩ := last.2 identifier (by have next := first.1; omega) worker live
  obtain ⟨original, originalAt, oldEntry, oldCaptured⟩ := first.2 identifier below previous previousAt
  exact ⟨original, originalAt, oldEntry.trans entry,
    fun event observed => captured event (oldCaptured event observed)⟩

theorem dispatch_advances (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) : Advances state result.1 := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  have one (phase : Phase)
      (stable : ∀ event, worker.captured = some event →
        ({ worker with phase := phase }).captured = some event) (shared : Atomics64.State) :
      Advances state { replace state identifier (some { worker with phase := phase }) with shared := shared } := by
    refine ⟨Nat.le_refl _, ?_⟩
    intro query _ current found
    by_cases selected : query = identifier
    · subst query
      simp [replace] at found
      cases found
      exact ⟨worker, live, rfl, stable⟩
    · exact ⟨current, by simpa [replace, selected] using found, rfl, fun _ captured => captured⟩
  cases effect with
  | applying phase _ => exact one _ (by intro event captured; simp [Worker.captured, phase] at captured) _
  | returning phase =>
    apply one
    intro event captured
    simpa only [Worker.captured, phase] using captured

theorem Step.advances {before after : State} {label : Option Atomics64.Event}
    (step : Step before label after) (valid : WellFormed before) : Advances before after := by
  cases step with
  | spawn success =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := spawn_ok _ _ _ _ _ success
    rw [same]
    refine ⟨by simp [install], ?_⟩
    intro identifier below worker live
    have old : identifier ≠ before.nextThread := by omega
    exact ⟨worker, by simpa [install, old] using live, rfl, fun _ captured => captured⟩
  | dispatch success => exact dispatch_advances _ _ _ _ valid success
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
    exact .refl _
  | retire success =>
    obtain ⟨_, _, _, same⟩ := retire_ok _ _ _ _ success
    rw [same]
    exact .refl _
  | idle => exact .refl _

theorem History.advances {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) : Advances before after := by
  induction history with
  | refl => exact .refl _
  | next first _ induction => exact (first.advances valid).trans (induction (first.wellFormed valid))

def Revoked (state : State) (identifier : Nat) : Prop :=
  identifier < state.nextThread ∧ state.workers identifier = none

theorem Revoked.persists {before after : State} {labels : List (Option Atomics64.Event)} {identifier : Nat}
    (revoked : Revoked before identifier) (valid : WellFormed before)
    (history : History before labels after) : Revoked after identifier := by
  have advances := history.advances valid
  refine ⟨by have a := revoked.1; have b := advances.1; omega, ?_⟩
  cases found : after.workers identifier with
  | none => rfl
  | some worker =>
    obtain ⟨original, originalAt, _, _⟩ := advances.2 identifier revoked.1 worker found
    rw [revoked.2] at originalAt
    cases originalAt

theorem Revoked.dispatch_denied {state : State} {identifier : Nat}
    (revoked : Revoked state identifier) (af : Bool) :
    dispatch state identifier af = .error .missingThread := by simp [dispatch, revoked.2]

theorem join_revokes_thread (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    Revoked result.1 identifier := by
  obtain ⟨worker, _, _, _, _, _, live, _, _, _, _, _, _⟩ := join_ok _ _ _ _ success
  have frames := join_workers _ _ _ _ success
  exact ⟨by rw [frames.2.1]; exact (valid.2 _ _ live).1, frames.1⟩

theorem joined_for_history {before after : State} {middle : State × Context}
    {labels : List (Option Atomics64.Event)} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle)
    (history : History middle.1 labels after) : Revoked after identifier :=
  (join_revokes_thread before parent identifier middle valid joined).persists
    (join_wellFormed _ _ _ _ valid joined) history

/-- Actual surviving loan contents and permissions are stable, not merely
allocation metadata. The managed wrappers alone justify this projection. -/
theorem History.loan_stable {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (below : identifier < before.shared.legacy.shared.nextLoan)
    (loan : Borrowing.Loan) (live : after.shared.legacy.shared.loans identifier = some loan) :
    before.shared.legacy.shared.loans identifier = some loan ∧
      ∀ query, loan.region.Contains query →
        after.shared.legacy.shared.resources.space.cells query = before.shared.legacy.shared.resources.space.cells query := by
  obtain ⟨_, lower⟩ := history.atomics valid
  exact lower.loan_stable valid.1 identifier below loan live

theorem History.handle_revoked {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Atomics64.HandleId64}
    (revoked : Atomics64.HandleRevoked before.shared identifier) :
    Atomics64.HandleRevoked after.shared identifier := by
  obtain ⟨_, lower⟩ := history.atomics valid
  exact lower.handle_revoked revoked

theorem History.loan_revoked {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Nat}
    (revoked : Borrowing.Revoked before.shared.legacy.shared identifier) :
    Borrowing.Revoked after.shared.legacy.shared identifier := by
  obtain ⟨_, lower⟩ := history.atomics valid
  exact lower.loan_revoked valid.1 revoked

/-- Captured labels persist for a surviving worker through all managed peer,
lifecycle and ordinary-resource actions; no after-word is promised current. -/
theorem History.captured {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (previous current : Worker) (event : Atomics64.Event)
    (live : before.workers identifier = some previous) (captured : previous.captured = some event)
    (survives : after.workers identifier = some current) : current.captured = some event := by
  obtain ⟨original, originalAt, _, stable⟩ := (history.advances valid).2 identifier
    (valid.2 _ _ live).1 current survives
  have same := Option.some.inj (originalAt.symm.trans live)
  cases same
  exact stable event captured

/-- Joining revokes the actual internal identities. The two loan finishes
and the handle close are checked core operations, not synthetic removals. -/
theorem join_revokes_resources (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      Atomics64.HandleRevoked result.1.shared worker.handle ∧
      Borrowing.Revoked result.1.shared.legacy.shared worker.codeLoan ∧
      Borrowing.Revoked result.1.shared.legacy.shared worker.stackLoan := by
  obtain ⟨worker, _, _, data, code, stack, live, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have dataValid := Atomics64.close_wellFormed _ _ _ _ valid.1 d
  have codeValid := Atomics64.finishLoan_wellFormed _ _ _ _ dataValid c
  have rest : Atomics64.History data [none, none] stack :=
    .next (.finishLoan c) (.next (.finishLoan s) .refl)
  rw [same]
  exact ⟨worker, live,
    rest.handle_revoked (Atomics64.close_revokes _ _ _ _ valid.1 d),
    Atomics64.finished_for_history _ _ dataValid c (.next (.finishLoan s) .refl),
    Atomics64.finished_for_history _ _ codeValid s .refl⟩

theorem joined_resources_for_history {before after : State} {middle : State × Context}
    {labels : List (Option Atomics64.Event)} (parent identifier : Nat)
    (valid : WellFormed before) (joined : join before parent identifier = .ok middle)
    (history : History middle.1 labels after) :
    ∃ worker, before.workers identifier = some worker ∧ Atomics64.HandleRevoked after.shared worker.handle ∧
      Borrowing.Revoked after.shared.legacy.shared worker.codeLoan ∧
      Borrowing.Revoked after.shared.legacy.shared worker.stackLoan := by
  obtain ⟨worker, live, handle, code, stack⟩ := join_revokes_resources _ _ _ _ valid joined
  have nextValid := join_wellFormed _ _ _ _ valid joined
  exact ⟨worker, live, history.handle_revoked nextValid handle,
    history.loan_revoked nextValid code, history.loan_revoked nextValid stack⟩

theorem History.cell_revoked {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before) {identifier : Atomics64.CellId64}
    (revoked : Atomics64.CellRevoked before.shared identifier) :
    Atomics64.CellRevoked after.shared identifier := by
  obtain ⟨_, lower⟩ := history.atomics valid
  exact lower.cell_revoked revoked

/-- Join returns the preserved private GPR frame after any managed history.
There is no memory field in this return value that could restore stale RAM. -/
theorem joined_private_frame {before after : State} {labels : List (Option Atomics64.Event)}
    (history : History before labels after) (valid : WellFormed before)
    (identifier : Nat) (worker : Worker) (live : before.workers identifier = some worker)
    (parent : Nat) (result : State × Context) (joined : join after parent identifier = .ok result) :
    result.2.registers .rsp = worker.entry.registers .rsp + 8 ∧
      ∀ register, register ≠ .rsp → result.2.registers register = worker.entry.registers register := by
  obtain ⟨current, _, currentAt, _, _, rsp, _, registers⟩ :=
    join_result _ _ _ _ (history.wellFormed valid) joined
  obtain ⟨original, originalAt, entry, _⟩ := (history.advances valid).2 identifier
    (valid.2 _ _ live).1 current currentAt
  have same := Option.some.inj (originalAt.symm.trans live)
  subst original
  rw [← entry] at rsp registers
  exact ⟨rsp, registers⟩

end EDSL.OS.AtomicThreads64
