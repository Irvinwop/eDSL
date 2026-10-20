/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Facts

namespace EDSL.OS.Atomics
open X86 AddressSpace

theorem canStore_permissions {before after : Space}
    (same : ∀ query, (after.cells query).map Cell.permissions = (before.cells query).map Cell.permissions)
    (address : Word) : canStoreDWord (toMemory after) address = canStoreDWord (toMemory before) address := by
  have point : ∀ query,
      (toMemory after).writable query = (toMemory before).writable query ∧
      ((toMemory after).read query).isSome = ((toMemory before).read query).isSome := by
    intro query
    have observed := same query
    cases old : before.cells query with
    | none =>
      cases new : after.cells query with
      | none => simp [toMemory, old, new]
      | some cell => simp [old, new] at observed
    | some oldCell =>
      cases new : after.cells query with
      | none => simp [old, new] at observed
      | some newCell =>
        simp only [old, new, Option.map_some, Option.some.injEq] at observed
        cases readable : oldCell.permissions.readable <;>
          simp [toMemory, old, new, observed, readable]
  simp only [canStoreDWord, dwordWritable, (point _).1, (point _).2]

theorem ValidHandle.frame {before after : Ownership.World} {handle : Handle}
    (validWorld : Ownership.WellFormed before)
    (valid : ValidHandle ⟨before, 0, fun _ => none⟩ handle)
    (frame : Ownership.PreservesAllocation before after handle.ticket.identifier) :
    ValidHandle ⟨after, 0, fun _ => none⟩ handle := by
  obtain ⟨allocation, found, owns, epoch, fits, supported, writable⟩ := valid
  obtain ⟨preserved, cells⟩ := frame allocation found
  refine ⟨allocation, preserved, owns, epoch, fits, supported, ?_⟩
  let loan : Borrowing.Loan := ⟨handle.ticket, handle.owner, handle.actor, allocation.region⟩
  have regionValid := (validWorld.1 _ _ found).2.1
  have subregion : Borrowing.Subregion (wordRegion handle.address) loan.region := of_decide_eq_true fits
  have point (offset : Nat) (bound : offset < 4) :
      after.space.cells (handle.address + BitVec.ofNat 64 offset) =
        before.space.cells (handle.address + BitVec.ofNat 64 offset) :=
    cells _ (Borrowing.word_inside loan regionValid handle.address subregion offset bound)
  have c0 := point 0 (by decide)
  have c1 := point 1 (by decide)
  have c2 := point 2 (by decide)
  have c3 := point 3 (by decide)
  simp only [BitVec.add_zero] at c0
  change after.space.cells (handle.address + 1) = before.space.cells (handle.address + 1) at c1
  change after.space.cells (handle.address + 2) = before.space.cells (handle.address + 2) at c2
  change after.space.cells (handle.address + 3) = before.space.cells (handle.address + 3) at c3
  simp only [canStoreDWord, dwordWritable, toMemory]
  rw [c0, c1, c2, c3]
  exact writable

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (valid : WellFormed state)
    (success : mutate state operation = .ok result) : WellFormed result.1 := by
  obtain ⟨checked, shared, changed, same⟩ := mutate_ok _ _ _ success
  subst result
  obtain ⟨_, resources, mutation, sharedEq⟩ := Borrowing.mutate_ok _ _ _ changed
  refine ⟨Borrowing.mutate_wellFormed _ _ _ valid.shared changed, ?_, ?_, valid.agreement⟩
  · intro identifier handle live
    obtain ⟨below, handleValid⟩ := valid.handles identifier handle live
    have framed := handleValid.frame valid.shared.1
      (operation.run_preserves _ _ _ valid.shared.1 mutation (allowed_sound state operation valid checked identifier handle live))
    rw [sharedEq]
    exact ⟨below, framed⟩
  · intro identifier handle live loanId loan reader
    apply valid.noReaders identifier handle live loanId loan
    simpa only [sharedEq] using reader

theorem readBorrow_wellFormed (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat) (valid : WellFormed state)
    (success : readBorrow state lender ticket borrower region = .ok result) : WellFormed result.1 := by
  obtain ⟨unreserved, shared, borrowed, same⟩ := readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, _, _, _, sharedEq⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ borrowed
  subst result
  refine ⟨(Borrowing.readBorrow_wellFormed _ _ _ _ _ _ valid.shared borrowed).1, ?_, ?_, valid.agreement⟩
  · intro identifier handle live
    rw [sharedEq]
    exact valid.handles identifier handle live
  · intro identifier handle live loanId loan reader
    rw [sharedEq] at reader
    by_cases newLoan : loanId = state.shared.nextLoan
    · subst loanId
      simp [Borrowing.installLoan] at reader
      cases reader
      intro sameAllocation
      have pinned := reserved_of_live state valid identifier handle live
      rw [sameAllocation] at unreserved
      rw [pinned] at unreserved
      cases unreserved
    · exact valid.noReaders identifier handle live loanId loan
        (by simpa [Borrowing.installLoan, newLoan] using reader)

theorem finishLoan_wellFormed (state : State) (borrower identifier : Nat) (after : State)
    (valid : WellFormed state) (success : finishLoan state borrower identifier = .ok after) : WellFormed after := by
  obtain ⟨shared, finished, same⟩ := finishLoan_ok _ _ _ _ success
  obtain ⟨_, _, sharedEq⟩ := Borrowing.finishLoan_ok _ _ _ _ finished
  subst after
  refine ⟨(Borrowing.finishLoan_wellFormed _ _ _ _ valid.shared finished).1, ?_, ?_, valid.agreement⟩
  · intro query handle live
    rw [sharedEq]
    exact valid.handles query handle live
  · intro query handle live loanId loan reader
    rw [sharedEq] at reader
    by_cases removed : loanId = identifier
    · simp [removed] at reader
    · exact valid.noReaders query handle live loanId loan (by simpa [removed] using reader)

theorem exchange_wellFormed (state : State) (actor identifier : Nat) (value : BitVec 32)
    (result : State × BitVec 32) (valid : WellFormed state)
    (success : exchange state actor identifier value = .ok result) : WellFormed result.1 := by
  obtain ⟨selected, shared, _, exchanged, same⟩ := exchange_ok _ _ _ _ _ success
  have gate := AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchanged
  obtain ⟨_, resources, mutation, sharedEq⟩ := Borrowing.mutate_ok _ _ _ gate
  cases stored : Ownership.storeWord state.shared.resources selected.owner selected.ticket selected.address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at mutation
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at mutation
    subst resources
    have sharedState : shared.1 = { state.shared with resources := world } := congrArg Prod.fst sharedEq
    have storedFacts := Ownership.storeWord_wellFormed _ _ _ _ _ _ valid.shared.1 stored
    subst result
    refine ⟨AtomicExchange.exchangeWord_wellFormed _ _ _ _ _ _ valid.shared exchanged, ?_, ?_, valid.agreement⟩
    · intro query handle live
      obtain ⟨below, allocation, found, owns, epoch, fits, supported, writable⟩ := valid.handles query handle live
      rw [sharedState]
      refine ⟨below, allocation, ?_, owns, epoch, fits, supported, ?_⟩
      · rw [storedFacts.2.2.1]
        exact found
      · rw [canStore_permissions storedFacts.2.2.2.2.2.2.1]
        exact writable
    · intro query handle live loanId loan reader
      apply valid.noReaders query handle live loanId loan
      simpa only [sharedState] using reader

end EDSL.OS.Atomics
