/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Registration
import EDSL.OS.Mutex.Mutation

namespace EDSL.OS.Mutex
open X86 AddressSpace

/-- Complete admitted transition surface. There is no raw outside XCHG/store,
underlying resource operation, or guard-ID reset in this relation. -/
inductive Step : State → State → Prop where
  | register {before config after} (success : Mutex.register before config = .ok after) : Step before after
  | acquire {before actor result} (success : tryAcquire before actor = .ok result) : Step before result.state
  | store {before actor lease value after} (success : guardStore before actor lease value = .ok after) : Step before after
  | release {before actor lease result} (success : Mutex.release before actor lease = .ok result) : Step before result.1
  | unregister {before owner after} (success : Mutex.unregister before owner = .ok after) : Step before after
  | mutate {before operation result} (success : Mutex.mutate before operation = .ok result) : Step before result.1
  | readBorrow {before lender ticket borrower region result}
      (success : Mutex.readBorrow before lender ticket borrower region = .ok result) : Step before result.1
  | finishLoan {before borrower identifier after}
      (success : Mutex.finishLoan before borrower identifier = .ok after) : Step before after
  | idle {state} : Step state state

inductive History : State → State → Prop where
  | refl {state} : History state state
  | next {before middle after} (first : Step before middle) (tail : History middle after) : History before after

theorem Step.wellFormed {before after : State} (step : Step before after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | register success => exact register_wellFormed _ _ _ valid success
  | acquire success => exact tryAcquire_wellFormed _ _ _ valid success
  | store success => exact guardStore_wellFormed _ _ _ _ _ valid success
  | release success => exact release_wellFormed _ _ _ _ valid success
  | unregister success => exact unregister_wellFormed _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | readBorrow success => exact readBorrow_wellFormed _ _ _ _ _ _ valid success
  | finishLoan success => exact finishLoan_wellFormed _ _ _ _ valid success
  | idle => exact valid

theorem History.wellFormed {before after : State} (history : History before after) (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

def Held (state : State) (lease : Lease) : Prop :=
  ∃ record, state.mutex = some record ∧ record.holder = some lease

def Advances (before after : State) : Prop :=
  before.nextLease ≤ after.nextLease ∧ ∀ lease, lease.identifier < before.nextLease → Held after lease → Held before lease

theorem advances_refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ held => held⟩

theorem advances_trans {before middle after : State} (first : Advances before middle) (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro lease below held
  exact first.2 lease below (last.2 lease (by have next := first.1; omega) held)

theorem Step.advances {before after : State} (step : Step before after) (valid : WellFormed before) : Advances before after := by
  cases step with
  | register success =>
    obtain ⟨_, _, _, _, _, _, _, _, same⟩ := register_ok _ _ _ valid.1 success
    rw [same]
    refine ⟨Nat.le_refl _, ?_⟩
    rintro lease _ ⟨record, present, held⟩
    simp only [Option.some.injEq] at present
    cases present
    cases held
  | acquire success =>
    obtain ⟨record, exchanged, _, _, branches⟩ := tryAcquire_ok _ _ _ success
    rcases branches with ⟨_, same⟩ | ⟨_, same⟩
    · rw [same]
      refine ⟨Nat.le_succ _, ?_⟩
      rintro lease below ⟨current, present, held⟩
      simp only [Option.some.injEq] at present
      cases present
      have sameLease := Option.some.inj held
      have sameId := congrArg Lease.identifier sameLease
      dsimp only at sameId
      omega
    · rw [same]
      exact advances_refl _
  | store success =>
    obtain ⟨_, _, _, _, same⟩ := guardStore_ok _ _ _ _ _ success
    rw [same]
    exact advances_refl _
  | release success =>
    obtain ⟨_, _, _, _, _, _, _, same⟩ := release_ok _ _ _ _ success
    rw [same]
    refine ⟨Nat.le_refl _, ?_⟩
    rintro lease _ ⟨record, present, held⟩
    simp only [Option.some.injEq] at present
    cases present
    cases held
  | unregister success =>
    obtain ⟨_, _, _, _, same⟩ := unregister_ok _ _ _ success
    rw [same]
    exact ⟨Nat.le_refl _, by rintro _ _ ⟨record, present, _⟩; cases present⟩
  | mutate success =>
    obtain ⟨_, _, _, same⟩ := mutate_ok _ _ _ success
    rw [same]
    exact advances_refl _
  | readBorrow success =>
    obtain ⟨_, _, _, same⟩ := readBorrow_ok _ _ _ _ _ _ success
    rw [same]
    exact advances_refl _
  | finishLoan success =>
    obtain ⟨_, _, same⟩ := finishLoan_ok _ _ _ _ success
    rw [same]
    exact advances_refl _
  | idle => exact advances_refl _

theorem History.advances {before after : State} (history : History before after) (valid : WellFormed before) : Advances before after := by
  induction history with
  | refl => exact advances_refl _
  | next first _ induction => exact advances_trans (first.advances valid) (induction (first.wellFormed valid))

def Revoked (state : State) (lease : Lease) : Prop :=
  lease.identifier < state.nextLease ∧ ¬Held state lease

theorem Revoked.persists {before after : State} {lease : Lease} (revoked : Revoked before lease)
    (valid : WellFormed before) (history : History before after) : Revoked after lease := by
  have advances := history.advances valid
  exact ⟨by have lower := revoked.1; have next := advances.1; omega,
    fun held => revoked.2 (advances.2 lease revoked.1 held)⟩

theorem release_revokes (state : State) (actor : Nat) (lease : Lease) (result : State × AtomicEvent)
    (valid : WellFormed state) (success : Mutex.release state actor lease = .ok result) : Revoked result.1 lease := by
  obtain ⟨record, _, _, authorized, _, _, _, same⟩ := release_ok _ _ _ _ success
  obtain ⟨live, held, _⟩ := authorize_ok _ _ _ _ authorized
  have phase := (valid.2 _ live).phase
  rw [held] at phase
  rw [same]
  refine ⟨phase.1, ?_⟩
  rintro ⟨current, present, held⟩
  simp only [Option.some.injEq] at present
  cases present
  cases held

theorem Revoked.unauthorized {state : State} {lease : Lease} (revoked : Revoked state lease) (actor : Nat) :
    ∀ record, authorize state actor lease ≠ .ok record := by
  intro record success
  obtain ⟨present, held, _⟩ := authorize_ok _ _ _ _ success
  exact revoked.2 ⟨record, present, held⟩

theorem released_for_history {before middle after : State} (actor : Nat) (lease : Lease) (event : AtomicEvent)
    (valid : WellFormed before) (released : Mutex.release before actor lease = .ok (middle, event))
    (history : History middle after) : Revoked after lease :=
  (release_revokes before actor lease (middle, event) valid released).persists
    (release_wellFormed _ _ _ _ valid released) history

theorem Step.borrowing {before after : State} (step : Step before after) (valid : WellFormed before) : Borrowing.History before.shared after.shared := by
  cases step with
  | register success =>
    obtain ⟨_, _, _, _, _, _, _, _, same⟩ := register_ok _ _ _ valid.1 success
    rw [same]; exact .refl
  | acquire success =>
    obtain ⟨_, _, _, exchange, branches⟩ := tryAcquire_ok _ _ _ success
    rcases branches with ⟨_, same⟩ | ⟨_, same⟩ <;> rw [same]
    all_goals exact .next (.mutate (AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchange)) .refl
  | store success =>
    obtain ⟨_, _, _, stored, same⟩ := guardStore_ok _ _ _ _ _ success
    rw [same]; exact .next (.mutate stored) .refl
  | release success =>
    obtain ⟨_, _, _, _, _, _, exchange, same⟩ := release_ok _ _ _ _ success
    rw [same]; exact .next (.mutate (AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchange)) .refl
  | unregister success =>
    obtain ⟨_, _, _, _, same⟩ := unregister_ok _ _ _ success
    rw [same]; exact .refl
  | mutate success =>
    obtain ⟨_, _, changed, same⟩ := mutate_ok _ _ _ success
    rw [same]; exact .next (.mutate changed) .refl
  | readBorrow success =>
    obtain ⟨_, _, borrowed, same⟩ := readBorrow_ok _ _ _ _ _ _ success
    rw [same]; exact .next (.readBorrow borrowed) .refl
  | finishLoan success =>
    obtain ⟨_, finished, same⟩ := finishLoan_ok _ _ _ _ success
    rw [same]; exact .next (.finishLoan finished) .refl
  | idle => exact .refl

private theorem appendBorrowing {before middle after : Borrowing.State}
    (first : Borrowing.History before middle) (last : Borrowing.History middle after) : Borrowing.History before after := by
  induction first with
  | refl => exact last
  | next step _ induction => exact .next step (induction last)

theorem History.borrowing {before after : State} (history : History before after) (valid : WellFormed before) : Borrowing.History before.shared after.shared := by
  induction history with
  | refl => exact .refl
  | next first _ induction =>
    exact appendBorrowing (first.borrowing valid) (induction (first.wellFormed valid))

end EDSL.OS.Mutex
