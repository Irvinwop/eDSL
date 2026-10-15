/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Facts

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem empty_wellFormed (shared : Borrowing.State) (valid : Borrowing.WellFormed shared) :
    WellFormed (empty shared) := ⟨valid, by simp [empty]⟩

theorem NoReaders.sameLoans {before after : Borrowing.State} {config : Config}
    (valid : NoReaders before config) (same : after.loans = before.loans) : NoReaders after config := by
  intro identifier loan live
  apply valid identifier loan
  simpa only [same] using live

/-- A lock exchange preserves the protected data's independently observed value. -/
theorem exchange_data (state : State) (record : Registered) (value : BitVec 32)
    (result : Borrowing.State × BitVec 32) (valid : WellFormed state)
    (live : state.mutex = some record)
    (success : AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress value = .ok result) :
    loadDWord (toMemory result.1.resources.space) record.config.dataAddress =
      loadDWord (toMemory state.shared.resources.space) record.config.dataAddress := by
  have mutex := valid.2 _ live
  exact mutex.data.load_frame valid.1.1
    (exchange_preservesAllocation valid.1.1 success _ (Ne.symm mutex.separate))

theorem tryAcquire_wellFormed (state : State) (actor : Nat) (result : Attempt)
    (valid : WellFormed state) (success : tryAcquire state actor = .ok result) : WellFormed result.state := by
  obtain ⟨record, exchanged, live, exchange, branches⟩ := tryAcquire_ok _ _ _ success
  have mutex := valid.2 _ live
  have effect := exchange_effect exchange
  have sharedValid := AtomicExchange.exchangeWord_wellFormed _ _ _ _ _ _ valid.1 exchange
  have data := exchange_data _ _ _ _ valid live exchange
  have actual := (AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange).2.2.1
  have lockValid := effect.wordValid mutex.lock
  have dataValid := effect.wordValid mutex.data
  have readers := mutex.noReaders.sameLoans effect.loans
  rcases branches with ⟨free, same⟩ | ⟨busy, same⟩
  · rw [same]
    refine ⟨sharedValid, ?_⟩
    intro current present
    simp only [Option.some.injEq] at present
    cases present
    exact ⟨lockValid, dataValid, mutex.separate, mutex.atomic, readers, Nat.lt_succ_self _, effect.readback⟩
  · rw [same]
    refine ⟨sharedValid, ?_⟩
    intro current present
    have equal := Option.some.inj (present.symm.trans live)
    subst current
    refine ⟨lockValid, dataValid, mutex.separate, mutex.atomic, readers, ?_⟩
    cases held : record.holder with
    | none =>
      have zero := mutex.phase
      rw [held] at zero
      have sameOld := Except.ok.inj (actual.symm.trans zero.1)
      exact False.elim (busy sameOld)
    | some lease =>
      have locked := mutex.phase
      rw [held] at locked
      exact ⟨locked.1, effect.readback⟩

/-- A successful acquisition opens the invariant that was closed in the actual
pre-exchange payload; a busy attempt grants no guard and retains its 1→1 event. -/
theorem acquisition (state : State) (actor : Nat) (result : Attempt)
    (valid : WellFormed state) (success : tryAcquire state actor = .ok result) :
    (∃ lease record, result.acquired = some lease ∧ result.state.mutex = some record ∧
      record.holder = some lease ∧ lease.actor = actor ∧ lease.identifier = state.nextLease ∧
      Closed result.state.shared record.config ∧ result.event.before = 0 ∧ result.event.after = 1) ∨
    (result.acquired = none ∧ result.state.mutex = state.mutex ∧ result.event.before = 1 ∧ result.event.after = 1) := by
  obtain ⟨record, exchanged, live, exchange, branches⟩ := tryAcquire_ok _ _ _ success
  have mutex := valid.2 _ live
  have actual := (AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange).2.2.1
  have data := exchange_data _ _ _ _ valid live exchange
  rcases branches with ⟨free, same⟩ | ⟨busy, same⟩
  · have unheld : record.holder = none := by
      cases held : record.holder with
      | none => rfl
      | some lease =>
        have locked := mutex.phase
        rw [held] at locked
        have oldOne := Except.ok.inj (actual.symm.trans locked.2)
        rw [free] at oldOne
        have zeroNeOne : (0 : BitVec 32) ≠ 1 := by decide
        exact False.elim (zeroNeOne oldOne)
    have closed := mutex.phase
    rw [unheld] at closed
    obtain ⟨value, observed, invariant⟩ := closed.2
    rw [same]
    exact Or.inl ⟨⟨state.nextLease, actor⟩, { record with holder := some ⟨state.nextLease, actor⟩ },
      rfl, rfl, rfl, rfl, rfl, ⟨value, data.trans observed, invariant⟩, free, rfl⟩
  · have oldOne : exchanged.2 = 1 := by
      cases held : record.holder with
      | none =>
        have zero := mutex.phase
        rw [held] at zero
        exact False.elim (busy (Except.ok.inj (actual.symm.trans zero.1)))
      | some lease =>
        have locked := mutex.phase
        rw [held] at locked
        exact Except.ok.inj (actual.symm.trans locked.2)
    rw [same]
    exact Or.inr ⟨rfl, rfl, oldOne, rfl⟩

theorem guardStore_wellFormed (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32) (after : State)
    (valid : WellFormed state) (success : guardStore state actor lease value = .ok after) : WellFormed after := by
  obtain ⟨record, result, authorized, stored, same⟩ := guardStore_ok _ _ _ _ _ success
  obtain ⟨live, held, _⟩ := authorize_ok _ _ _ _ authorized
  have mutex := valid.2 _ live
  have output : result.2 = none := by
    obtain ⟨_, resources, changed, resultEq⟩ := Borrowing.mutate_ok _ _ _ stored
    cases actual : Ownership.storeWord state.shared.resources record.config.owner record.config.dataTicket record.config.dataAddress value with
    | error fault => simp [Ownership.Mutation.run, actual, Except.map] at changed
    | ok world =>
      simp [Ownership.Mutation.run, actual, Except.map] at changed
      subst resources
      rw [resultEq]
  have storedNone : Borrowing.mutate state.shared (.store record.config.owner record.config.dataTicket record.config.dataAddress value) = .ok (result.1, none) := by
    rw [← output]
    exact stored
  have effect := store_effect storedNone
  have lockRead := mutex.lock.load_frame valid.1.1
    (store_preservesAllocation valid.1.1 storedNone _ mutex.separate)
  rw [same]
  refine ⟨Borrowing.mutate_wellFormed _ _ _ valid.1 stored, ?_⟩
  intro current present
  have equal := Option.some.inj (present.symm.trans live)
  subst current
  refine ⟨effect.wordValid mutex.lock, effect.wordValid mutex.data, mutex.separate, mutex.atomic,
    mutex.noReaders.sameLoans effect.loans, ?_⟩
  have phase := mutex.phase
  rw [held] at phase ⊢
  exact ⟨phase.1, lockRead.trans phase.2⟩

theorem release_wellFormed (state : State) (actor : Nat) (lease : Lease) (result : State × AtomicEvent)
    (valid : WellFormed state) (success : release state actor lease = .ok result) : WellFormed result.1 := by
  obtain ⟨record, value, exchanged, authorized, observed, closed, exchange, same⟩ := release_ok _ _ _ _ success
  have live := (authorize_ok _ _ _ _ authorized).1
  have mutex := valid.2 _ live
  have effect := exchange_effect exchange
  have data := exchange_data _ _ _ _ valid live exchange
  rw [same]
  refine ⟨AtomicExchange.exchangeWord_wellFormed _ _ _ _ _ _ valid.1 exchange, ?_⟩
  intro current present
  simp only [Option.some.injEq] at present
  cases present
  exact ⟨effect.wordValid mutex.lock, effect.wordValid mutex.data, mutex.separate, mutex.atomic,
    mutex.noReaders.sameLoans effect.loans, effect.readback, value, data.trans observed, closed⟩

theorem unregister_wellFormed (state : State) (owner : Nat) (after : State)
    (valid : WellFormed state) (success : unregister state owner = .ok after) : WellFormed after := by
  obtain ⟨_, _, _, _, same⟩ := unregister_ok _ _ _ success
  rw [same]
  exact ⟨valid.1, by simp⟩

end EDSL.OS.Mutex
