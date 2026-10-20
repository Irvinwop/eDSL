/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Model
import EDSL.OS.AtomicThreads64.Join
import EDSL.OS.Atomics64.LogicalPreservation

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

/-- The lower resource history is operation-neutral. In particular AND and
XOR are projected through the checked borrowing store rather than fabricated
as OR-labelled `Atomics64.History` steps. -/
theorem logicalUpdate_borrowing (op : Sequential.LogicalOp) (before : Atomics64.State)
    (actor : Nat) (identifier : Atomics64.HandleId64) (mask : Word)
    (result : Atomics64.State × Atomics64.Event)
    (success : Atomics64.logicalUpdate op before actor identifier mask = .ok result) :
    Borrowing.History before.legacy.shared result.1.legacy.shared := by
  obtain ⟨_, _, _, _, stored⟩ := Atomics64.logicalUpdate_guarded _ _ _ _ _ _ success
  exact .next (.mutate (Atomics64.legacy_store64_guarded stored)) .refl

/-- A current resource certificate constructively enables the exact guarded
full64 wrapper, including its legacy32 reservation gate. -/
theorem BorrowReady.enabled {state : Atomics64.State}
    {ticket : Ownership.Ticket} {region : Region} (ready : BorrowReady state ticket region)
    (valid : Atomics64.WellFormed state) (borrower : Nat) :
    ∃ result, Atomics64.readBorrow state 0 ticket borrower region = .ok result := by
  obtain ⟨allocation, authorized, regionValid, contained, readable, unreserved, legacyUnreserved⟩ := ready
  let borrowed := Borrowing.installLoan state.legacy.shared ⟨ticket, 0, borrower, region⟩
  have checked := Borrowing.readBorrow_success state.legacy.shared 0 ticket borrower region
    allocation valid.legacy.shared authorized regionValid contained readable
  refine ⟨({ state with legacy := { state.legacy with shared := borrowed } },
    state.legacy.shared.nextLoan), ?_⟩
  simp [Atomics64.readBorrow, unreserved, Atomics.readBorrow, legacyUnreserved,
    checked, Except.mapError, borrowed]

/-- Read borrowing does not change any admission fact for a second read
borrow, even when the two regions use the same allocation. -/
theorem BorrowReady.after_readBorrow {before : Atomics64.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Atomics64.State × Nat}
    (success : Atomics64.readBorrow before lender ticket borrower region = .ok result)
    {nextTicket : Ownership.Ticket} {nextRegion : Region}
    (ready : BorrowReady before nextTicket nextRegion) :
    BorrowReady result.1 nextTicket nextRegion := by
  obtain ⟨allocation, authorized, regionValid, contained, readable, unreserved, legacyUnreserved⟩ := ready
  have resources := AtomicThreads64.readBorrow_resources success
  obtain ⟨_, legacy, checked, same⟩ := Atomics64.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, _, legacyEq⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ checked
  refine ⟨allocation, ?_, regionValid, contained, ?_, ?_, ?_⟩
  · rw [resources]; exact authorized
  · rw [resources]; exact readable
  · rw [same, legacyEq]; exact unreserved
  · rw [same, legacyEq]; exact legacyUnreserved

/-- This evidence is private to checked wrapper proofs. Both live and
completed workers retain their exact authority records and immutable loans. -/
def Retains (before after : Atomics64.State) (worker : Worker) : Prop :=
  after.handles worker.handle = before.handles worker.handle ∧
    after.cells worker.cell = before.cells worker.cell ∧
    after.legacy.shared.loans worker.codeLoan = before.legacy.shared.loans worker.codeLoan ∧
    after.legacy.shared.loans worker.stackLoan = before.legacy.shared.loans worker.stackLoan

/-- Generic worker framing uses only borrowing history and retained records.
It consequently applies to AND/XOR updates without erasing their actual tags. -/
theorem WorkerValid.frame {before after : Atomics64.State} {identifier : Nat} {worker : Worker}
    (workerValid : WorkerValid before identifier worker) (valid : Atomics64.WellFormed before)
    (history : Borrowing.History before.legacy.shared after.legacy.shared)
    (kept : Retains before after worker) : WorkerValid after identifier worker := by
  obtain ⟨parent, handle, code, stack, distinct, layout, executable, target, canonical,
    stackBound, postStackCanonical, captured, phase⟩ := workerValid
  obtain ⟨record, cell, live, actor, link, atCell, address⟩ := handle
  obtain ⟨codeAfter, codeCells⟩ := code.frame valid.legacy.shared history kept.2.2.1
  obtain ⟨stackAfter, stackCells⟩ := stack.frame valid.legacy.shared history kept.2.2.2
  exact ⟨parent, ⟨record, cell, kept.1.trans live, actor, link, kept.2.1.trans atCell, address⟩,
    codeAfter, stackAfter, distinct, layout, agrees_code _ _ _ _ codeCells executable,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans target, canonical,
    stackBound, postStackCanonical, captured, phase⟩

theorem logicalUpdate_retains (op : Sequential.LogicalOp) (before : Atomics64.State)
    (actor : Nat) (identifier : Atomics64.HandleId64) (mask : Word)
    (result : Atomics64.State × Atomics64.Event)
    (success : Atomics64.logicalUpdate op before actor identifier mask = .ok result)
    (worker : Worker) : Retains before result.1 worker := by
  have effect := Atomics64.logicalUpdate_effect _ _ _ _ _ _ success
  exact ⟨congrFun effect.handles _, congrFun effect.cells _,
    congrFun effect.shared.loans _, congrFun effect.shared.loans _⟩

theorem WorkerValid.after_logicalUpdate {before : Atomics64.State} {identifier : Nat}
    {worker : Worker} (workerValid : WorkerValid before identifier worker)
    (valid : Atomics64.WellFormed before) (op : Sequential.LogicalOp) (actor : Nat)
    (handle : Atomics64.HandleId64) (mask : Word) (result : Atomics64.State × Atomics64.Event)
    (success : Atomics64.logicalUpdate op before actor handle mask = .ok result) :
    WorkerValid result.1 identifier worker :=
  workerValid.frame valid (logicalUpdate_borrowing _ _ _ _ _ _ success)
    (logicalUpdate_retains _ _ _ _ _ _ success worker)

/-- A generic logical update cannot recycle a closed handle identity. -/
theorem handle_revoked_after_logicalUpdate {before : Atomics64.State}
    {identifier : Atomics64.HandleId64} (revoked : Atomics64.HandleRevoked before identifier)
    (op : Sequential.LogicalOp) (actor : Nat) (handle : Atomics64.HandleId64) (mask : Word)
    (result : Atomics64.State × Atomics64.Event)
    (success : Atomics64.logicalUpdate op before actor handle mask = .ok result) :
    Atomics64.HandleRevoked result.1 identifier :=
  revoked.persists (Atomics64.logicalUpdate_advances _ _ _ _ _ _ success)

/-- Borrowing's monotone frontier carries finished-loan revocation across all
three operations, without manufacturing an OR-only history. -/
theorem loan_revoked_after_logicalUpdate {before : Atomics64.State} {identifier : Nat}
    (valid : Atomics64.WellFormed before)
    (revoked : Borrowing.Revoked before.legacy.shared identifier)
    (op : Sequential.LogicalOp) (actor : Nat) (handle : Atomics64.HandleId64) (mask : Word)
    (result : Atomics64.State × Atomics64.Event)
    (success : Atomics64.logicalUpdate op before actor handle mask = .ok result) :
    Borrowing.Revoked result.1.legacy.shared identifier :=
  revoked.persists valid.legacy.shared (logicalUpdate_borrowing _ _ _ _ _ _ success)

end EDSL.OS.AtomicSetThreads64
