/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Protocol

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem targeted_mutation_rejected (state : State) (record : Registered) (operation : Ownership.Mutation)
    (live : state.mutex = some record)
    (target : operation.target = some record.config.lockTicket.identifier ∨ operation.target = some record.config.dataTicket.identifier) :
    mutate state operation = .error .reserved := by
  rcases target with lock | data <;> simp [mutate, allowed, *]

theorem protected_borrow_rejected (state : State) (record : Registered) (lender borrower : Nat)
    (ticket : Ownership.Ticket) (region : Region) (live : state.mutex = some record)
    (target : ticket.identifier = record.config.lockTicket.identifier ∨ ticket.identifier = record.config.dataTicket.identifier) :
    readBorrow state lender ticket borrower region = .error .reserved := by
  rcases target with lock | data <;> simp [readBorrow, allowed, *]

/-- The closed invariant holds for actual final payload cells after every
admitted mixed history that leaves a registered mutex unlocked. -/
theorem History.closed {before after : State} (history : History before after)
    (valid : WellFormed before) (record : Registered) (live : after.mutex = some record)
    (free : record.holder = none) : Closed after.shared record.config := by
  have phase := ((history.wellFormed valid).2 _ live).phase
  rw [free] at phase
  exact phase.2

theorem History.loan_stable {before after : State} (history : History before after)
    (valid : WellFormed before) (identifier : Nat) (below : identifier < before.shared.nextLoan)
    (loan : Borrowing.Loan) (live : after.shared.loans identifier = some loan) :
    before.shared.loans identifier = some loan ∧ ∀ address, loan.region.Contains address →
      after.shared.resources.space.cells address = before.shared.resources.space.cells address :=
  (history.borrowing valid).loan_stable valid.1 identifier below loan live

/-- An unsuccessful/reentrant attempt retains the current holder, with an
actual 1→1 exchange event rather than an omitted transition. -/
theorem busy_preserves_holder (state : State) (actor : Nat) (result : Attempt)
    (valid : WellFormed state) (success : tryAcquire state actor = .ok result) (busy : result.acquired = none) :
    result.state.mutex = state.mutex ∧ result.event.before = 1 ∧ result.event.after = 1 := by
  rcases acquisition state actor result valid success with acquired | failed
  · obtain ⟨lease, _, granted, _⟩ := acquired
    rw [busy] at granted
    cases granted
  · exact failed.2

theorem unregister_closes (state : State) (owner : Nat) (after : State)
    (valid : WellFormed state) (success : unregister state owner = .ok after) :
    ∃ record, state.mutex = some record ∧ record.config.owner = owner ∧
      Closed after.shared record.config ∧ after.shared = state.shared ∧ after.nextLease = state.nextLease := by
  obtain ⟨record, live, owns, held, same⟩ := unregister_ok _ _ _ success
  have phase := (valid.2 _ live).phase
  rw [held] at phase
  rw [same]
  exact ⟨record, live, owns, phase.2, rfl, rfl⟩

theorem idle_trace (state : State) :
    ∃ trace : Nat → State, trace 0 = state ∧ ∀ index, Step (trace index) (trace (index + 1)) :=
  ⟨fun _ => state, rfl, fun _ => .idle⟩

end EDSL.OS.Mutex
