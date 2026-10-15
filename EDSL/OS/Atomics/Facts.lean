/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Model

namespace EDSL.OS.Atomics
open X86 AddressSpace

theorem issue_ok (state : State) (owner : Nat) (ticket : Ownership.Ticket) (actor : Nat) (address : Word)
    (result : State × Nat) (success : issue state owner ticket actor address = .ok result) :
    ∃ allocation, Ownership.authorize state.shared.resources owner ticket = .ok allocation ∧
      compatible state owner ticket address = true ∧
      Borrowing.allowed state.shared (.store owner ticket address 0) = true ∧
      Ownership.containsWord allocation address = true ∧ atomicAddressable address = true ∧
      canStoreDWord (toMemory state.shared.resources.space) address = true ∧
      result = (install state ⟨owner, ticket, actor, address⟩, state.nextHandle) := by
  cases authorized : Ownership.authorize state.shared.resources owner ticket with
  | error fault => simp [issue, authorized, Except.mapError] at success
  | ok allocation =>
    by_cases collision : (state.handles state.nextHandle).isSome = true
    · simp [issue, authorized, Except.mapError, collision] at success
    · by_cases compatibleCheck : compatible state owner ticket address = true
      · by_cases borrowCheck : Borrowing.allowed state.shared (.store owner ticket address 0) = true
        · simp only [BitVec.ofNat_eq_ofNat] at borrowCheck
          by_cases fits : Ownership.containsWord allocation address = true
          · by_cases supported : atomicAddressable address = true
            · by_cases writable : canStoreDWord (toMemory state.shared.resources.space) address = true
              · simp [issue, authorized, Except.mapError, collision, compatibleCheck, borrowCheck,
                  fits, supported, writable] at success
                exact ⟨allocation, rfl, compatibleCheck, borrowCheck, fits, supported, writable, success.symm⟩
              · simp [issue, authorized, Except.mapError, collision, compatibleCheck, borrowCheck,
                  fits, supported, writable] at success
            · simp [issue, authorized, Except.mapError, collision, compatibleCheck, borrowCheck, fits, supported] at success
          · simp [issue, authorized, Except.mapError, collision, compatibleCheck, borrowCheck, fits] at success
        · simp only [BitVec.ofNat_eq_ofNat] at borrowCheck
          simp [issue, authorized, Except.mapError, collision, compatibleCheck, borrowCheck] at success
      · simp [issue, authorized, Except.mapError, collision, compatibleCheck] at success

theorem close_ok (state : State) (actor identifier : Nat) (after : State)
    (success : close state actor identifier = .ok after) :
    ∃ handle, authorize state actor identifier = .ok handle ∧
      after = { state with handles := fun query => if query = identifier then none else state.handles query } := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [close, authorized] at success
  | ok handle =>
    simp [close, authorized] at success
    exact ⟨handle, rfl, success.symm⟩

theorem issue_success (state : State) (owner : Nat) (ticket : Ownership.Ticket) (actor : Nat) (address : Word)
    (allocation : Ownership.Allocation) (valid : WellFormed state)
    (authorized : Ownership.authorize state.shared.resources owner ticket = .ok allocation)
    (sameCell : compatible state owner ticket address = true)
    (unborrowed : Borrowing.allowed state.shared (.store owner ticket address 0) = true)
    (fits : Ownership.containsWord allocation address = true)
    (supported : atomicAddressable address = true)
    (writable : canStoreDWord (toMemory state.shared.resources.space) address = true) :
    issue state owner ticket actor address = .ok (install state ⟨owner, ticket, actor, address⟩, state.nextHandle) := by
  simp only [BitVec.ofNat_eq_ofNat] at unborrowed
  simp [issue, authorized, Except.mapError, fresh_identity state valid, sameCell, unborrowed, fits, supported, writable]

theorem mutate_ok (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) :
    allowed state operation = true ∧ ∃ shared,
      Borrowing.mutate state.shared operation = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  by_cases checked : allowed state operation = true
  · cases changed : Borrowing.mutate state.shared operation with
    | error fault => simp [mutate, checked, changed, Except.mapError] at success
    | ok shared =>
      simp [mutate, checked, changed, Except.mapError] at success
      exact ⟨checked, shared, rfl, success.symm⟩
  · simp [mutate, checked] at success

theorem readBorrow_ok (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat)
    (success : readBorrow state lender ticket borrower region = .ok result) :
    reserved state ticket.identifier = false ∧ ∃ shared,
      Borrowing.readBorrow state.shared lender ticket borrower region = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  cases checked : reserved state ticket.identifier with
  | true => simp [readBorrow, checked] at success
  | false =>
    cases borrowed : Borrowing.readBorrow state.shared lender ticket borrower region with
    | error fault => simp [readBorrow, checked, borrowed, Except.mapError] at success
    | ok shared =>
      simp [readBorrow, checked, borrowed, Except.mapError] at success
      exact ⟨rfl, shared, rfl, success.symm⟩

theorem finishLoan_ok (state : State) (borrower identifier : Nat) (after : State)
    (success : finishLoan state borrower identifier = .ok after) :
    ∃ shared, Borrowing.finishLoan state.shared borrower identifier = .ok shared ∧
      after = { state with shared := shared } := by
  cases finished : Borrowing.finishLoan state.shared borrower identifier with
  | error fault => simp [finishLoan, finished, Except.mapError] at success
  | ok shared =>
    simp [finishLoan, finished, Except.mapError] at success
    exact ⟨shared, rfl, success.symm⟩

theorem exchange_ok (state : State) (actor identifier : Nat) (value : BitVec 32)
    (result : State × BitVec 32) (success : exchange state actor identifier value = .ok result) :
    ∃ handle shared, authorize state actor identifier = .ok handle ∧
      AtomicExchange.exchangeWord state.shared handle.owner handle.ticket handle.address value = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [exchange, authorized] at success
  | ok handle =>
    cases exchanged : AtomicExchange.exchangeWord state.shared handle.owner handle.ticket handle.address value with
    | error fault => simp [exchange, authorized, exchanged, Except.mapError] at success
    | ok shared =>
      simp [exchange, authorized, exchanged, Except.mapError] at success
      exact ⟨handle, shared, rfl, exchanged, success.symm⟩

theorem issue_wellFormed (state : State) (owner : Nat) (ticket : Ownership.Ticket) (actor : Nat) (address : Word)
    (result : State × Nat) (valid : WellFormed state)
    (success : issue state owner ticket actor address = .ok result) :
    WellFormed result.1 ∧ result.1.handles result.2 = some ⟨owner, ticket, actor, address⟩ := by
  obtain ⟨allocation, authorized, compatibleCheck, borrowCheck, fits, supported, writable, same⟩ :=
    issue_ok _ _ _ _ _ _ success
  obtain ⟨found, owns, epoch⟩ := Ownership.authorize_ok _ _ _ _ authorized
  subst result
  refine ⟨⟨valid.shared, ?_, ?_, ?_⟩, by simp [install]⟩
  · intro identifier handle live
    by_cases new : identifier = state.nextHandle
    · subst identifier
      simp [install] at live
      cases live
      exact ⟨by simp [install], allocation, found, owns, epoch, fits, supported, writable⟩
    · have old : state.handles identifier = some handle := by simpa [install, new] using live
      exact ⟨by have below := (valid.handles _ _ old).1; simp only [install]; omega,
        (valid.handles _ _ old).2⟩
  · intro identifier handle live loanId loan reader
    by_cases new : identifier = state.nextHandle
    · subst identifier
      simp [install] at live
      cases live
      have blocked := Borrowing.allowed_sound _ _ valid.shared borrowCheck loanId loan reader
      simpa [Ownership.Mutation.target, eq_comm] using blocked
    · exact valid.noReaders identifier handle (by simpa [install, new] using live) loanId loan reader
  · intro left a right b atLeft atRight sameAllocation
    by_cases newLeft : left = state.nextHandle
    · subst left
      simp [install] at atLeft
      cases atLeft
      by_cases newRight : right = state.nextHandle
      · subst right
        simp [install] at atRight
        cases atRight
        exact ⟨rfl, rfl, rfl⟩
      · have old : state.handles right = some b := by simpa [install, newRight] using atRight
        have agreement := compatible_sound state owner ticket address valid compatibleCheck right b old sameAllocation.symm
        exact ⟨agreement.1.symm, agreement.2.1.symm, agreement.2.2.symm⟩
    · have oldLeft : state.handles left = some a := by simpa [install, newLeft] using atLeft
      by_cases newRight : right = state.nextHandle
      · subst right
        simp [install] at atRight
        cases atRight
        exact compatible_sound state owner ticket address valid compatibleCheck left a oldLeft sameAllocation
      · exact valid.agreement left a right b oldLeft (by simpa [install, newRight] using atRight) sameAllocation

theorem close_wellFormed (state : State) (actor identifier : Nat) (after : State)
    (valid : WellFormed state) (success : close state actor identifier = .ok after) : WellFormed after := by
  obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
  subst after
  have old : ∀ query handle,
      (if query = identifier then none else state.handles query) = some handle →
      state.handles query = some handle := by
    intro query handle live
    by_cases removed : query = identifier
    · simp [removed] at live
    · simpa [removed] using live
  exact ⟨valid.shared, fun query handle live => valid.handles query handle (old _ _ live),
    fun query handle live => valid.noReaders query handle (old _ _ live),
    fun left a right b atLeft atRight => valid.agreement left a right b (old _ _ atLeft) (old _ _ atRight)⟩

end EDSL.OS.Atomics
