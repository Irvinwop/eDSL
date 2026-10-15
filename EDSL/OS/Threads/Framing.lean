/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Model

namespace EDSL.OS.Threads
open X86 AddressSpace

/-- Endpoints retain a worker's three exact internal loans. -/
def Retains (before after : Borrowing.State) (worker : Worker) : Prop :=
  ∀ loanId, loanId = worker.dataLoan ∨ loanId = worker.codeLoan ∨ loanId = worker.stackLoan →
    after.loans loanId = before.loans loanId

theorem HasLoan.frame {before after : Borrowing.State} {identifier loanId : Nat} {region : Region}
    (loan : HasLoan before identifier loanId region) (valid : Borrowing.WellFormed before)
    (history : Borrowing.History before after) (kept : after.loans loanId = before.loans loanId) :
    HasLoan after identifier loanId region ∧ AgreesOn after.resources.space before.resources.space region.base region.length := by
  obtain ⟨record, live, borrower, sameRegion⟩ := loan
  have finalLive := kept.trans live
  obtain ⟨below, _, _, _, _, _, regionValid, _⟩ := valid.2 loanId record live
  obtain ⟨_, cells⟩ := history.loan_stable valid loanId below record finalLive
  refine ⟨⟨record, finalLive, borrower, sameRegion⟩, ?_⟩
  intro offset bound
  subst region
  apply cells
  apply Ownership.addresses_inside record.region regionValid
  exact List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩

theorem WorkerValid.frame {before after : Borrowing.State} {identifier : Nat} {worker : Worker}
    (workerValid : WorkerValid before identifier worker) (valid : Borrowing.WellFormed before)
    (history : Borrowing.History before after) (kept : Retains before after worker) :
    WorkerValid after identifier worker := by
  obtain ⟨parent, data, code, stack, dc, ds, cs, executable, value, target, canonical, phase⟩ := workerValid
  obtain ⟨dataAfter, dataCells⟩ := data.frame valid history (kept _ (Or.inl rfl))
  obtain ⟨codeAfter, codeCells⟩ := code.frame valid history (kept _ (Or.inr (Or.inl rfl)))
  obtain ⟨stackAfter, stackCells⟩ := stack.frame valid history (kept _ (Or.inr (Or.inr rfl)))
  refine ⟨parent, dataAfter, codeAfter, stackAfter, dc, ds, cs, ?_, ?_, ?_, canonical, phase⟩
  · exact agrees_code _ _ _ _ codeCells executable
  · exact (loadDWord_congr _ _ _ (agrees_read _ _ _ _ dataCells)).trans value
  · exact (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans target

theorem HasLoan.different {shared : Borrowing.State} {left right a b : Nat} {ra rb : Region}
    (first : HasLoan shared left a ra) (second : HasLoan shared right b rb) (different : left ≠ right) : a ≠ b := by
  intro equal
  subst b
  obtain ⟨loan, atLoan, owner, _⟩ := first
  obtain ⟨other, atOther, ownerOther, _⟩ := second
  have same := Option.some.inj (atLoan.symm.trans atOther)
  cases same
  have principals := owner.symm.trans ownerOther
  simp only [principal] at principals
  exact different (Nat.add_right_cancel principals)

theorem readBorrow_resources {before : Borrowing.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Borrowing.State × Nat}
    (success : Borrowing.readBorrow before lender ticket borrower region = .ok result) :
    result.1.resources = before.resources := by
  obtain ⟨_, _, _, _, _, same⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  rfl

theorem readBorrow_advances {before : Borrowing.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Borrowing.State × Nat}
    (success : Borrowing.readBorrow before lender ticket borrower region = .ok result) :
    result.2 = before.nextLoan ∧ result.1.nextLoan = before.nextLoan + 1 := by
  obtain ⟨_, _, _, _, _, same⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact ⟨rfl, rfl⟩

theorem readBorrow_preserves {before : Borrowing.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Borrowing.State × Nat} (valid : Borrowing.WellFormed before)
    (success : Borrowing.readBorrow before lender ticket borrower region = .ok result) :
    ∀ identifier loan, before.loans identifier = some loan → result.1.loans identifier = some loan := by
  obtain ⟨_, _, _, _, _, same⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  intro identifier loan live
  have below := (valid.2 _ _ live).1
  have old : identifier ≠ before.nextLoan := by omega
  simpa [Borrowing.installLoan, old] using live

theorem finishLoan_resources {before after : Borrowing.State} {borrower identifier : Nat}
    (success : Borrowing.finishLoan before borrower identifier = .ok after) : after.resources = before.resources := by
  obtain ⟨_, _, same⟩ := Borrowing.finishLoan_ok _ _ _ _ success
  rw [same]

theorem finishLoan_other {before after : Borrowing.State} {borrower identifier query : Nat}
    (success : Borrowing.finishLoan before borrower identifier = .ok after) (different : query ≠ identifier) :
    after.loans query = before.loans query := by
  obtain ⟨_, _, same⟩ := Borrowing.finishLoan_ok _ _ _ _ success
  rw [same]
  simp [different]

end EDSL.OS.Threads
