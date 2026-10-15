/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Model

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem registered_ok (state : State) (record : Registered) (success : registered state = .ok record) :
    state.mutex = some record := by
  cases present : state.mutex <;> simp [registered, present] at success
  cases success
  rfl

theorem authorize_ok (state : State) (actor : Nat) (lease : Lease) (record : Registered)
    (success : authorize state actor lease = .ok record) :
    state.mutex = some record ∧ record.holder = some lease ∧ lease.actor = actor := by
  cases selected : registered state with
  | error fault => simp [authorize, selected] at success
  | ok currentRecord =>
    by_cases owns : lease.actor = actor
    · cases held : currentRecord.holder with
      | none => simp [authorize, selected, owns, held] at success
      | some current =>
        by_cases same : current = lease
        · simp [authorize, selected, owns, held, same] at success
          cases success
          exact ⟨registered_ok _ _ selected, by simpa [same] using held, owns⟩
        · simp [authorize, selected, owns, held, same] at success
    · simp [authorize, selected, owns] at success

/-- The independently supplied actor and full guard must match the one stored
holder. Two separately authorized guards therefore cannot grant two owners. -/
theorem exclusive (state : State) (actor otherActor : Nat) (lease otherLease : Lease)
    (first second : Registered) (a : authorize state actor lease = .ok first)
    (b : authorize state otherActor otherLease = .ok second) : lease = otherLease ∧ actor = otherActor := by
  obtain ⟨firstAt, held, owner⟩ := authorize_ok _ _ _ _ a
  obtain ⟨secondAt, otherHeld, otherOwner⟩ := authorize_ok _ _ _ _ b
  have recordEq := Option.some.inj (firstAt.symm.trans secondAt)
  subst second
  have guardEq := Option.some.inj (held.symm.trans otherHeld)
  exact ⟨guardEq, owner.symm.trans ((congrArg Lease.actor guardEq).trans otherOwner)⟩

theorem tryAcquire_ok (state : State) (actor : Nat) (result : Attempt)
    (success : tryAcquire state actor = .ok result) :
    ∃ record exchanged, state.mutex = some record ∧
      AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress 1 = .ok exchanged ∧
      ((exchanged.2 = 0 ∧ result =
          ⟨⟨exchanged.1, state.nextLease + 1,
              some { record with holder := some ⟨state.nextLease, actor⟩ }⟩,
            some ⟨state.nextLease, actor⟩, ⟨record.config.lockAddress, exchanged.2, 1⟩⟩) ∨
       (exchanged.2 ≠ 0 ∧ result =
          ⟨{ state with shared := exchanged.1 }, none, ⟨record.config.lockAddress, exchanged.2, 1⟩⟩)) := by
  cases selected : registered state with
  | error fault => simp [tryAcquire, selected] at success
  | ok record =>
    cases exchanged : AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress 1 with
    | error fault =>
      simp only [BitVec.ofNat_eq_ofNat] at exchanged
      simp [tryAcquire, selected, exchanged, Except.mapError] at success
    | ok output =>
      simp only [BitVec.ofNat_eq_ofNat] at exchanged
      have present := registered_ok _ _ selected
      by_cases free : output.2 = 0
      · simp only [BitVec.ofNat_eq_ofNat] at free
        simp [tryAcquire, selected, exchanged, Except.mapError, free] at success
        exact ⟨record, output, present, exchanged, Or.inl ⟨free, by simpa only [free, BitVec.ofNat_eq_ofNat] using success.symm⟩⟩
      · simp only [BitVec.ofNat_eq_ofNat] at free
        simp [tryAcquire, selected, exchanged, Except.mapError, free] at success
        exact ⟨record, output, present, exchanged, Or.inr ⟨free, success.symm⟩⟩

theorem guardStore_ok (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32) (after : State)
    (success : guardStore state actor lease value = .ok after) :
    ∃ record result, authorize state actor lease = .ok record ∧
      Borrowing.mutate state.shared (.store record.config.owner record.config.dataTicket record.config.dataAddress value) = .ok result ∧
      after = { state with shared := result.1 } := by
  cases selected : authorize state actor lease with
  | error fault => simp [guardStore, selected] at success
  | ok record =>
    cases changed : Borrowing.mutate state.shared (.store record.config.owner record.config.dataTicket record.config.dataAddress value) with
    | error fault => simp [guardStore, selected, changed, Except.mapError] at success
    | ok result =>
      simp [guardStore, selected, changed, Except.mapError] at success
      exact ⟨record, result, rfl, changed, success.symm⟩

theorem release_ok (state : State) (actor : Nat) (lease : Lease) (result : State × AtomicEvent)
    (success : release state actor lease = .ok result) :
    ∃ record value exchanged, authorize state actor lease = .ok record ∧
      loadDWord (toMemory state.shared.resources.space) record.config.dataAddress = .ok value ∧
      record.config.invariant value = true ∧
      AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress 0 = .ok exchanged ∧
      result = ({ state with shared := exchanged.1, mutex := some { record with holder := none } },
        ⟨record.config.lockAddress, exchanged.2, 0⟩) := by
  cases selected : authorize state actor lease with
  | error fault => simp [release, selected] at success
  | ok record =>
    cases read : loadDWord (toMemory state.shared.resources.space) record.config.dataAddress with
    | error fault => simp [release, selected, read, Except.mapError] at success
    | ok value =>
      by_cases closed : record.config.invariant value = true
      · cases exchanged : AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress 0 with
        | error fault =>
          simp only [BitVec.ofNat_eq_ofNat] at exchanged
          simp [release, selected, read, closed, exchanged, Except.mapError] at success
        | ok output =>
          simp only [BitVec.ofNat_eq_ofNat] at exchanged
          simp [release, selected, read, closed, exchanged, Except.mapError] at success
          exact ⟨record, value, output, rfl, read, closed, exchanged, success.symm⟩
      · simp [release, selected, read, closed, Except.mapError] at success

theorem unregister_ok (state : State) (owner : Nat) (after : State)
    (success : unregister state owner = .ok after) :
    ∃ record, state.mutex = some record ∧ record.config.owner = owner ∧ record.holder = none ∧
      after = { state with mutex := none } := by
  cases selected : registered state with
  | error fault => simp [unregister, selected] at success
  | ok record =>
    by_cases owns : record.config.owner = owner
    · cases held : record.holder with
      | none =>
        simp [unregister, selected, owns, held] at success
        exact ⟨record, registered_ok _ _ selected, owns, held, success.symm⟩
      | some lease => simp [unregister, selected, owns, held] at success
    · simp [unregister, selected, owns] at success

theorem allowed_sound (state : State) (target : Option Nat) (record : Registered)
    (present : state.mutex = some record) (checked : allowed state target = true) :
    target ≠ some record.config.lockTicket.identifier ∧ target ≠ some record.config.dataTicket.identifier := by
  simpa [allowed, present] using checked

theorem mutate_ok (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) :
    allowed state operation.target = true ∧ ∃ shared,
      Borrowing.mutate state.shared operation = .ok shared ∧ result = ({ state with shared := shared.1 }, shared.2) := by
  by_cases gate : allowed state operation.target = true
  · cases changed : Borrowing.mutate state.shared operation with
    | error fault => simp [mutate, gate, changed, Except.mapError] at success
    | ok shared =>
      simp [mutate, gate, changed, Except.mapError] at success
      exact ⟨gate, shared, rfl, success.symm⟩
  · simp [mutate, gate] at success

theorem readBorrow_ok (state : State) (lender : Nat) (ticket : Ownership.Ticket) (borrower : Nat) (region : Region)
    (result : State × Nat) (success : readBorrow state lender ticket borrower region = .ok result) :
    allowed state (some ticket.identifier) = true ∧ ∃ shared,
      Borrowing.readBorrow state.shared lender ticket borrower region = .ok shared ∧ result = ({ state with shared := shared.1 }, shared.2) := by
  by_cases gate : allowed state (some ticket.identifier) = true
  · cases changed : Borrowing.readBorrow state.shared lender ticket borrower region with
    | error fault => simp [readBorrow, gate, changed, Except.mapError] at success
    | ok shared =>
      simp [readBorrow, gate, changed, Except.mapError] at success
      exact ⟨gate, shared, rfl, success.symm⟩
  · simp [readBorrow, gate] at success

theorem finishLoan_ok (state : State) (borrower identifier : Nat) (after : State)
    (success : finishLoan state borrower identifier = .ok after) :
    ∃ shared, Borrowing.finishLoan state.shared borrower identifier = .ok shared ∧ after = { state with shared := shared } := by
  cases changed : Borrowing.finishLoan state.shared borrower identifier with
  | error fault => simp [finishLoan, changed, Except.mapError] at success
  | ok shared =>
    simp [finishLoan, changed, Except.mapError] at success
    exact ⟨shared, rfl, success.symm⟩

end EDSL.OS.Mutex
