/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Model

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Internal proof evidence about exact checked operations, never an exposed
managed-history admission rule. Retention includes the persistent cell. -/
def Retains (before after : Atomics64.State) (worker : Worker) : Prop :=
  after.handles worker.handle = before.handles worker.handle ∧
    after.cells worker.cell = before.cells worker.cell ∧
    after.legacy.shared.loans worker.codeLoan = before.legacy.shared.loans worker.codeLoan ∧
    after.legacy.shared.loans worker.stackLoan = before.legacy.shared.loans worker.stackLoan

theorem WorkerValid.frame {before after : Atomics64.State} {identifier : Nat} {worker : Worker}
    {labels : List (Option Atomics64.Event)}
    (workerValid : WorkerValid before identifier worker) (valid : Atomics64.WellFormed before)
    (history : Atomics64.History before labels after) (kept : Retains before after worker) :
    WorkerValid after identifier worker := by
  obtain ⟨parent, handle, code, stack, distinct, executable, target, canonical, phase⟩ := workerValid
  obtain ⟨record, cell, live, actor, link, atCell, address⟩ := handle
  obtain ⟨codeAfter, codeCells⟩ := code.frame valid.legacy.shared history.borrowing kept.2.2.1
  obtain ⟨stackAfter, stackCells⟩ := stack.frame valid.legacy.shared history.borrowing kept.2.2.2
  exact ⟨parent, ⟨record, cell, kept.1.trans live, actor, link, kept.2.1.trans atCell, address⟩,
    codeAfter, stackAfter, distinct, agrees_code _ _ _ _ codeCells executable,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans target, canonical, phase⟩

theorem HasHandle.different {shared : Atomics64.State} {left right : Nat}
    {a b : Atomics64.HandleId64} {ca cb : Atomics64.CellId64} {aa ab : Word}
    (first : HasHandle shared left a ca aa) (second : HasHandle shared right b cb ab)
    (different : left ≠ right) : a ≠ b := by
  intro equal
  subst b
  obtain ⟨handle, _, atHandle, actor, _⟩ := first
  obtain ⟨other, _, atOther, actorOther, _⟩ := second
  have same := Option.some.inj (atHandle.symm.trans atOther)
  cases same
  have principals := actor.symm.trans actorOther
  simp only [principal, Threads.principal] at principals
  exact different (Nat.add_right_cancel principals)

theorem readBorrow_resources {before : Atomics64.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before lender ticket borrower region = .ok result) :
    result.1.legacy.shared.resources = before.legacy.shared.resources := by
  obtain ⟨_, legacy, borrowed, same⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, checked, legacyEq⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ borrowed
  rw [same, legacyEq]
  exact Threads.readBorrow_resources checked

theorem readBorrow_registry {before : Atomics64.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before lender ticket borrower region = .ok result) :
    result.1.handles = before.handles ∧ result.1.cells = before.cells := by
  obtain ⟨_, _, _, same⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact ⟨rfl, rfl⟩

theorem readBorrow_advances {before : Atomics64.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before lender ticket borrower region = .ok result) :
    result.2 = before.legacy.shared.nextLoan ∧
      result.1.legacy.shared.nextLoan = before.legacy.shared.nextLoan + 1 := by
  obtain ⟨_, _, borrowed, same⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, checked, legacyEq⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ borrowed
  rw [same, legacyEq]
  exact Threads.readBorrow_advances checked

theorem readBorrow_loan {before : Atomics64.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before lender ticket borrower region = .ok result) :
    result.1.legacy.shared.loans result.2 = some ⟨ticket, lender, borrower, region⟩ := by
  obtain ⟨_, _, borrowed, same⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, checked, legacyEq⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ borrowed
  obtain ⟨_, _, _, _, _, sharedEq⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ checked
  rw [same, legacyEq, sharedEq]
  simp [Borrowing.installLoan]

theorem readBorrow_preserves {before : Atomics64.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (valid : Atomics64.WellFormed before)
    (success : Atomics64.readBorrow before lender ticket borrower region = .ok result) :
    ∀ identifier loan, before.legacy.shared.loans identifier = some loan →
      result.1.legacy.shared.loans identifier = some loan := by
  obtain ⟨_, _, borrowed, same⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, checked, legacyEq⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ borrowed
  rw [same, legacyEq]
  exact Threads.readBorrow_preserves valid.legacy.shared checked

theorem issue_legacy {before : Atomics64.State} {owner actor : Nat} {cell : Atomics64.CellId64}
    {result : Atomics64.State × Atomics64.HandleId64}
    (success : Atomics64.issue before owner cell actor = .ok result) :
    result.1.legacy = before.legacy ∧ result.1.cells = before.cells := by
  obtain ⟨_, _, same⟩ := Atomics64.issue_ok _ _ _ _ _ success
  rw [same]
  exact ⟨rfl, rfl⟩

theorem issue_preserves {before : Atomics64.State} {owner actor : Nat} {cell : Atomics64.CellId64}
    {result : Atomics64.State × Atomics64.HandleId64} (valid : Atomics64.WellFormed before)
    (success : Atomics64.issue before owner cell actor = .ok result) :
    ∀ identifier handle, before.handles identifier = some handle →
      result.1.handles identifier = some handle := by
  obtain ⟨_, _, same⟩ := Atomics64.issue_ok _ _ _ _ _ success
  rw [same]
  intro identifier handle live
  have different : identifier ≠ ⟨before.nextHandle⟩ := by
    intro same
    have below := (valid.handles _ _ live).1
    rw [same] at below
    exact Nat.lt_irrefl _ below
  simpa [Atomics64.installHandle, different] using live

theorem close_frames {before after : Atomics64.State} {actor : Nat} {identifier : Atomics64.HandleId64}
    (success : Atomics64.close before actor identifier = .ok after) :
    after.legacy = before.legacy ∧ after.cells = before.cells := by
  obtain ⟨_, _, same⟩ := Atomics64.close_ok _ _ _ _ success
  rw [same]
  exact ⟨rfl, rfl⟩

theorem close_other {before after : Atomics64.State} {actor : Nat}
    {identifier query : Atomics64.HandleId64}
    (success : Atomics64.close before actor identifier = .ok after) (different : query ≠ identifier) :
    after.handles query = before.handles query := by
  obtain ⟨_, _, same⟩ := Atomics64.close_ok _ _ _ _ success
  rw [same]
  simp [Atomics64.removeHandle, different]

theorem finishLoan_frames {before after : Atomics64.State} {borrower identifier : Nat}
    (success : Atomics64.finishLoan before borrower identifier = .ok after) :
    after.handles = before.handles ∧ after.cells = before.cells ∧
      after.legacy.shared.resources = before.legacy.shared.resources := by
  obtain ⟨_, finished, same⟩ := Atomics64.finishLoan_ok _ _ _ _ success
  obtain ⟨_, checked, legacyEq⟩ := Atomics.finishLoan_ok _ _ _ _ finished
  rw [same, legacyEq]
  exact ⟨rfl, rfl, Threads.finishLoan_resources checked⟩

theorem finishLoan_other {before after : Atomics64.State} {borrower identifier query : Nat}
    (success : Atomics64.finishLoan before borrower identifier = .ok after) (different : query ≠ identifier) :
    after.legacy.shared.loans query = before.legacy.shared.loans query := by
  obtain ⟨_, finished, same⟩ := Atomics64.finishLoan_ok _ _ _ _ success
  obtain ⟨_, checked, legacyEq⟩ := Atomics.finishLoan_ok _ _ _ _ finished
  rw [same, legacyEq]
  exact Threads.finishLoan_other checked different

end EDSL.OS.AtomicThreads64
