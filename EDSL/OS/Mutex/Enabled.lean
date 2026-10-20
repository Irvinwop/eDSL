/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Machine

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem unborrowed (shared : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (value : BitVec 32) (readers : ∀ identifier loan, shared.loans identifier = some loan → loan.ticket.identifier ≠ ticket.identifier) :
    Borrowing.allowed shared (.store owner ticket address value) = true := by
  apply List.all_eq_true.mpr
  intro identifier _
  cases present : shared.loans identifier with
  | none => rfl
  | some loan =>
    have different := readers _ _ present
    simpa only [Ownership.Mutation.target, decide_eq_true_eq, ne_eq, Option.some.injEq] using Ne.symm different

theorem store_admitted (shared : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (value : BitVec 32) (word : WordValid shared owner ticket address)
    (readers : ∀ identifier loan, shared.loans identifier = some loan → loan.ticket.identifier ≠ ticket.identifier) :
    ∃ after, Borrowing.mutate shared (.store owner ticket address value) = .ok (after, none) := by
  obtain ⟨allocation, authorized, fits⟩ := word.authorize
  have stored := Ownership.storeWord_success _ _ _ _ value _ authorized fits word.writable
  let after := { shared with resources := { shared.resources with space := writeWordCells shared.resources.space address value } }
  exact ⟨after, by simp [Borrowing.mutate, unborrowed _ _ _ _ _ readers,
    Ownership.Mutation.run, stored, Except.map, Except.mapError, after]⟩

theorem exchange_admitted (shared : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (value : BitVec 32) (word : WordValid shared owner ticket address) (supported : atomicAddressable address = true)
    (readers : ∀ identifier loan, shared.loans identifier = some loan → loan.ticket.identifier ≠ ticket.identifier) :
    ∃ result, AtomicExchange.exchangeWord shared owner ticket address value = .ok result := by
  obtain ⟨after, stored⟩ := store_admitted shared owner ticket address value word readers
  obtain ⟨old, observed⟩ := word.load_exists
  exact ⟨(after, old), AtomicExchange.exchangeWord_success _ _ _ _ old value after stored supported word.writable observed⟩

theorem tryAcquire_enabled (state : State) (actor : Nat) (record : Registered)
    (valid : WellFormed state) (live : state.mutex = some record) : ∃ result, tryAcquire state actor = .ok result := by
  have mutex := valid.2 _ live
  obtain ⟨exchanged, exchange⟩ := exchange_admitted state.shared record.config.owner record.config.lockTicket
    record.config.lockAddress 1 mutex.lock mutex.atomic (fun identifier loan found => (mutex.noReaders identifier loan found).1)
  simp only [BitVec.ofNat_eq_ofNat] at exchange
  by_cases free : exchanged.2 = 0
  · simp only [BitVec.ofNat_eq_ofNat] at free
    exact ⟨⟨⟨exchanged.1, state.nextLease + 1, some { record with holder := some ⟨state.nextLease, actor⟩ }⟩,
      some ⟨state.nextLease, actor⟩, ⟨record.config.lockAddress, 0, 1⟩⟩,
      by simp [tryAcquire, registered, live, exchange, free, Except.mapError]⟩
  · simp only [BitVec.ofNat_eq_ofNat] at free
    exact ⟨⟨{ state with shared := exchanged.1 }, none, ⟨record.config.lockAddress, exchanged.2, 1⟩⟩,
      by simp [tryAcquire, registered, live, exchange, free, Except.mapError]⟩

theorem authorize_of_held (state : State) (actor : Nat) (lease : Lease) (record : Registered)
    (live : state.mutex = some record) (held : record.holder = some lease) (owns : lease.actor = actor) :
    authorize state actor lease = .ok record := by
  simp [authorize, registered, live, held, owns]

theorem guardLoad_enabled (state : State) (actor : Nat) (lease : Lease) (record : Registered)
    (valid : WellFormed state) (authorized : authorize state actor lease = .ok record) :
    ∃ value, guardLoad state actor lease = .ok value := by
  have live := (authorize_ok _ _ _ _ authorized).1
  obtain ⟨value, observed⟩ := (valid.2 _ live).data.load_exists
  exact ⟨value, by simp [guardLoad, authorized, observed, Except.mapError]⟩

theorem guardStore_enabled (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32) (record : Registered)
    (valid : WellFormed state) (authorized : authorize state actor lease = .ok record) :
    ∃ after, guardStore state actor lease value = .ok after := by
  have mutex := valid.2 _ (authorize_ok _ _ _ _ authorized).1
  obtain ⟨after, stored⟩ := store_admitted state.shared record.config.owner record.config.dataTicket
    record.config.dataAddress value mutex.data (fun identifier loan found => (mutex.noReaders identifier loan found).2)
  exact ⟨{ state with shared := after }, by simp [guardStore, authorized, stored, Except.mapError]⟩

theorem release_enabled (state : State) (actor : Nat) (lease : Lease) (record : Registered)
    (valid : WellFormed state) (authorized : authorize state actor lease = .ok record)
    (closed : Closed state.shared record.config) : ∃ result, release state actor lease = .ok result := by
  have mutex := valid.2 _ (authorize_ok _ _ _ _ authorized).1
  obtain ⟨value, observed, invariant⟩ := closed
  obtain ⟨result, exchange⟩ := exchange_admitted state.shared record.config.owner record.config.lockTicket
    record.config.lockAddress 0 mutex.lock mutex.atomic (fun identifier loan found => (mutex.noReaders identifier loan found).1)
  simp only [BitVec.ofNat_eq_ofNat] at exchange
  exact ⟨({ state with shared := result.1, mutex := some { record with holder := none } },
    ⟨record.config.lockAddress, result.2, 0⟩),
    by simp [release, authorized, observed, invariant, exchange, Except.mapError]⟩

/-- All releases in the valid protocol are actual 1→0 RMWs, with the invariant
closed in the final current payload and no surviving holder. -/
theorem release_result (state : State) (actor : Nat) (lease : Lease) (result : State × AtomicEvent)
    (valid : WellFormed state) (success : release state actor lease = .ok result) :
    ∃ record, result.1.mutex = some record ∧ record.holder = none ∧ Closed result.1.shared record.config ∧
      result.2.before = 1 ∧ result.2.after = 0 := by
  obtain ⟨record, value, exchanged, authorized, observed, invariant, exchange, same⟩ := release_ok _ _ _ _ success
  obtain ⟨live, held, _⟩ := authorize_ok _ _ _ _ authorized
  have phase := (valid.2 _ live).phase
  rw [held] at phase
  have actual := (AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange).2.2.1
  have old := Except.ok.inj (actual.symm.trans phase.2)
  have data := exchange_data _ _ _ _ valid live exchange
  rw [same]
  exact ⟨{ record with holder := none }, rfl, rfl, ⟨value, data.trans observed, invariant⟩, old, rfl⟩

end EDSL.OS.Mutex
