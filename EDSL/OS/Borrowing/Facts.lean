/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Model

namespace EDSL.OS.Borrowing
open X86 AddressSpace

theorem readBorrow_ok (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat)
    (success : readBorrow state lender ticket borrower region = .ok result) :
    ∃ allocation, Ownership.authorize state.resources lender ticket = .ok allocation ∧
      region.valid = true ∧ Subregion region allocation.region ∧
      allReadable state.resources.space region = true ∧
      result = (installLoan state ⟨ticket, lender, borrower, region⟩, state.nextLoan) := by
  cases authorized : Ownership.authorize state.resources lender ticket with
  | error fault => simp [readBorrow, authorized, Except.mapError] at success
  | ok allocation =>
    by_cases collision : (state.loans state.nextLoan).isSome = true
    · simp [readBorrow, authorized, Except.mapError, collision] at success
    · by_cases valid : region.valid = true
      · by_cases fits : Subregion region allocation.region
        · by_cases readable : allReadable state.resources.space region = true
          · simp [readBorrow, authorized, Except.mapError, collision, valid, fits, readable] at success
            exact ⟨allocation, rfl, valid, fits, readable, success.symm⟩
          · simp [readBorrow, authorized, Except.mapError, collision, valid, fits, readable] at success
        · simp [readBorrow, authorized, Except.mapError, collision, valid, fits] at success
      · simp [readBorrow, authorized, Except.mapError, collision, valid] at success

theorem fresh_identity (state : State) (valid : WellFormed state) : state.loans state.nextLoan = none := by
  cases found : state.loans state.nextLoan with
  | none => rfl
  | some loan => have below := (valid.2 _ _ found).1; omega

theorem readBorrow_success (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (allocation : Ownership.Allocation)
    (valid : WellFormed state)
    (authorized : Ownership.authorize state.resources lender ticket = .ok allocation)
    (regionValid : region.valid = true) (fits : Subregion region allocation.region)
    (readable : allReadable state.resources.space region = true) :
    readBorrow state lender ticket borrower region =
      .ok (installLoan state ⟨ticket, lender, borrower, region⟩, state.nextLoan) := by
  simp [readBorrow, authorized, Except.mapError, fresh_identity state valid, regionValid, fits, readable]

theorem readBorrow_wellFormed (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat) (valid : WellFormed state)
    (success : readBorrow state lender ticket borrower region = .ok result) :
    WellFormed result.1 ∧ result.1.loans result.2 = some ⟨ticket, lender, borrower, region⟩ := by
  obtain ⟨allocation, authorized, regionValid, fits, readable, same⟩ := readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨found, owns, epoch⟩ := Ownership.authorize_ok _ _ _ _ authorized
  subst result
  refine ⟨⟨valid.1, ?_⟩, by simp [installLoan]⟩
  intro identifier loan live
  by_cases new : identifier = state.nextLoan
  · subst identifier
    simp [installLoan] at live
    cases live
    refine ⟨by simp [installLoan], allocation, found, owns, epoch, fits, regionValid, ?_⟩
    exact allReadable_inside state.resources.space region readable
  · have old : state.loans identifier = some loan := by simpa [installLoan, new] using live
    have facts := valid.2 _ _ old
    exact ⟨by simp only [installLoan]; have below := facts.1; omega, facts.2⟩

theorem finishLoan_ok (state : State) (borrower identifier : Nat) (result : State)
    (success : finishLoan state borrower identifier = .ok result) :
    ∃ loan, authorize state borrower identifier = .ok loan ∧
      result = { state with loans := fun query => if query = identifier then none else state.loans query } := by
  cases authorized : authorize state borrower identifier with
  | error fault => simp [finishLoan, authorized] at success
  | ok loan =>
    simp [finishLoan, authorized] at success
    exact ⟨loan, rfl, success.symm⟩

theorem finishLoan_wellFormed (state : State) (borrower identifier : Nat) (result : State)
    (valid : WellFormed state) (success : finishLoan state borrower identifier = .ok result) :
    WellFormed result ∧ result.loans identifier = none := by
  obtain ⟨_, _, same⟩ := finishLoan_ok _ _ _ _ success
  subst result
  refine ⟨⟨valid.1, ?_⟩, by simp⟩
  intro query loan live
  by_cases removed : query = identifier
  · simp [removed] at live
  · exact valid.2 _ _ (by simpa [removed] using live)

theorem mutate_ok (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (success : mutate state operation = .ok result) :
    allowed state operation = true ∧ ∃ resources,
      operation.run state.resources = .ok resources ∧
      result = ({ state with resources := resources.1 }, resources.2) := by
  by_cases checked : allowed state operation = true
  · cases changed : operation.run state.resources with
    | error fault => simp [mutate, checked, changed, Except.mapError] at success
    | ok resources =>
      simp [mutate, checked, changed, Except.mapError] at success
      exact ⟨checked, resources, rfl, success.symm⟩
  · simp [mutate, checked] at success

theorem ValidLoan.frame {before after : Ownership.World} {loan : Loan}
    (valid : ValidLoan before loan)
    (frame : Ownership.PreservesAllocation before after loan.ticket.identifier) :
    ValidLoan after loan := by
  obtain ⟨allocation, found, owns, epoch, fits, regionValid, readable⟩ := valid
  obtain ⟨preserved, cells⟩ := frame allocation found
  refine ⟨allocation, preserved, owns, epoch, fits, regionValid, ?_⟩
  intro address inside
  obtain ⟨cell, stored, canRead⟩ := readable address inside
  exact ⟨cell, (cells address (subregion_inside fits inside)).trans stored, canRead⟩

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (valid : WellFormed state)
    (success : mutate state operation = .ok result) : WellFormed result.1 := by
  obtain ⟨checked, resources, changed, same⟩ := mutate_ok _ _ _ success
  subst result
  refine ⟨operation.run_wellFormed _ _ valid.1 changed, ?_⟩
  intro identifier loan live
  obtain ⟨below, loanValid⟩ := valid.2 identifier loan live
  exact ⟨below, loanValid.frame (operation.run_preserves _ _ _ valid.1 changed
    (allowed_sound state operation valid checked identifier loan live))⟩

end EDSL.OS.Borrowing
