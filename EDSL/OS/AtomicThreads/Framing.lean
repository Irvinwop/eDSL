/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Model

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

def Retains (before after : Atomics.State) (worker : Worker) : Prop :=
  after.handles worker.handle = before.handles worker.handle ∧
    after.shared.loans worker.codeLoan = before.shared.loans worker.codeLoan ∧
    after.shared.loans worker.stackLoan = before.shared.loans worker.stackLoan

theorem WorkerValid.frame {before after : Atomics.State} {identifier : Nat} {worker : Worker}
    (workerValid : WorkerValid before identifier worker) (valid : Atomics.WellFormed before)
    (history : Atomics.History before after) (kept : Retains before after worker) :
    WorkerValid after identifier worker := by
  obtain ⟨parent, handle, code, stack, distinct, executable, target, canonical, phase⟩ := workerValid
  obtain ⟨record, live, actor, address⟩ := handle
  obtain ⟨codeAfter, codeCells⟩ := code.frame valid.shared history.borrowing kept.2.1
  obtain ⟨stackAfter, stackCells⟩ := stack.frame valid.shared history.borrowing kept.2.2
  exact ⟨parent, ⟨record, kept.1.trans live, actor, address⟩, codeAfter, stackAfter, distinct,
    agrees_code _ _ _ _ codeCells executable,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans target, canonical, phase⟩

theorem HasHandle.different {shared : Atomics.State} {left right a b : Nat} {aa ab : Word}
    (first : HasHandle shared left a aa) (second : HasHandle shared right b ab) (different : left ≠ right) : a ≠ b := by
  intro equal
  subst b
  obtain ⟨handle, atHandle, actor, _⟩ := first
  obtain ⟨other, atOther, actorOther, _⟩ := second
  have same := Option.some.inj (atHandle.symm.trans atOther)
  cases same
  have principals := actor.symm.trans actorOther
  simp only [principal, Threads.principal] at principals
  exact different (Nat.add_right_cancel principals)

theorem readBorrow_resources {before : Atomics.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Atomics.State × Nat}
    (success : Atomics.readBorrow before lender ticket borrower region = .ok result) :
    result.1.shared.resources = before.shared.resources := by
  obtain ⟨_, shared, borrowed, same⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact Threads.readBorrow_resources borrowed

theorem readBorrow_handles {before : Atomics.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Atomics.State × Nat}
    (success : Atomics.readBorrow before lender ticket borrower region = .ok result) :
    result.1.handles = before.handles := by
  obtain ⟨_, _, _, same⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ success
  rw [same]

theorem readBorrow_advances {before : Atomics.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Atomics.State × Nat}
    (success : Atomics.readBorrow before lender ticket borrower region = .ok result) :
    result.2 = before.shared.nextLoan ∧ result.1.shared.nextLoan = before.shared.nextLoan + 1 := by
  obtain ⟨_, _, borrowed, same⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact Threads.readBorrow_advances borrowed

theorem readBorrow_loan {before : Atomics.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Atomics.State × Nat}
    (success : Atomics.readBorrow before lender ticket borrower region = .ok result) :
    result.1.shared.loans result.2 = some ⟨ticket, lender, borrower, region⟩ := by
  obtain ⟨_, _, borrowed, same⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, _, _, _, shape⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ borrowed
  rw [same, shape]
  simp [Borrowing.installLoan]

theorem readBorrow_preserves {before : Atomics.State} {lender borrower : Nat} {ticket : Ownership.Ticket}
    {region : Region} {result : Atomics.State × Nat} (valid : Atomics.WellFormed before)
    (success : Atomics.readBorrow before lender ticket borrower region = .ok result) :
    ∀ identifier loan, before.shared.loans identifier = some loan → result.1.shared.loans identifier = some loan := by
  obtain ⟨_, _, borrowed, same⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact Threads.readBorrow_preserves valid.shared borrowed

theorem issue_shared {before : Atomics.State} {owner actor : Nat} {ticket : Ownership.Ticket}
    {address : Word} {result : Atomics.State × Nat}
    (success : Atomics.issue before owner ticket actor address = .ok result) : result.1.shared = before.shared := by
  obtain ⟨_, _, _, _, _, _, _, same⟩ := Atomics.issue_ok _ _ _ _ _ _ success
  rw [same]
  rfl

theorem issue_preserves {before : Atomics.State} {owner actor : Nat} {ticket : Ownership.Ticket}
    {address : Word} {result : Atomics.State × Nat} (valid : Atomics.WellFormed before)
    (success : Atomics.issue before owner ticket actor address = .ok result) :
    ∀ identifier handle, before.handles identifier = some handle → result.1.handles identifier = some handle := by
  obtain ⟨_, _, _, _, _, _, _, same⟩ := Atomics.issue_ok _ _ _ _ _ _ success
  rw [same]
  intro identifier handle live
  have different : identifier ≠ before.nextHandle := by have below := (valid.handles _ _ live).1; omega
  simpa [Atomics.install, different] using live

theorem close_shared {before after : Atomics.State} {actor identifier : Nat}
    (success : Atomics.close before actor identifier = .ok after) : after.shared = before.shared := by
  obtain ⟨_, _, same⟩ := Atomics.close_ok _ _ _ _ success
  rw [same]

theorem close_other {before after : Atomics.State} {actor identifier query : Nat}
    (success : Atomics.close before actor identifier = .ok after) (different : query ≠ identifier) :
    after.handles query = before.handles query := by
  obtain ⟨_, _, same⟩ := Atomics.close_ok _ _ _ _ success
  rw [same]
  simp [different]

theorem finishLoan_resources {before after : Atomics.State} {borrower identifier : Nat}
    (success : Atomics.finishLoan before borrower identifier = .ok after) :
    after.shared.resources = before.shared.resources := by
  obtain ⟨_, finished, same⟩ := Atomics.finishLoan_ok _ _ _ _ success
  rw [same]
  exact Threads.finishLoan_resources finished

theorem finishLoan_handles {before after : Atomics.State} {borrower identifier : Nat}
    (success : Atomics.finishLoan before borrower identifier = .ok after) : after.handles = before.handles := by
  obtain ⟨_, _, same⟩ := Atomics.finishLoan_ok _ _ _ _ success
  rw [same]

theorem finishLoan_other {before after : Atomics.State} {borrower identifier query : Nat}
    (success : Atomics.finishLoan before borrower identifier = .ok after) (different : query ≠ identifier) :
    after.shared.loans query = before.shared.loans query := by
  obtain ⟨_, finished, same⟩ := Atomics.finishLoan_ok _ _ _ _ success
  rw [same]
  exact Threads.finishLoan_other finished different

theorem exchange_keeps {before : Atomics.State} {actor identifier : Nat} {value : BitVec 32}
    {result : Atomics.State × BitVec 32} (success : Atomics.exchange before actor identifier value = .ok result) :
    result.1.handles = before.handles ∧ result.1.shared.loans = before.shared.loans := by
  obtain ⟨_, _, _, exchanged, same⟩ := Atomics.exchange_ok _ _ _ _ _ success
  have gate := AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ exchanged
  obtain ⟨_, _, _, sharedEq⟩ := Borrowing.mutate_ok _ _ _ gate
  have loansEq := congrArg (fun result : Borrowing.State × Option Ownership.Ticket => result.1.loans) sharedEq
  rw [same]
  exact ⟨rfl, loansEq⟩

theorem finishLoan_revokes {before after : Atomics.State} {borrower identifier : Nat}
    (valid : Atomics.WellFormed before) (success : Atomics.finishLoan before borrower identifier = .ok after) :
    Borrowing.Revoked after.shared identifier := by
  obtain ⟨_, finished, same⟩ := Atomics.finishLoan_ok _ _ _ _ success
  rw [same]
  exact Borrowing.finishLoan_revokes _ _ _ _ valid.shared finished

end EDSL.OS.AtomicThreads
