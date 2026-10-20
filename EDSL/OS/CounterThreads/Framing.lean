/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Model

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

export AtomicThreads (readBorrow_resources readBorrow_handles readBorrow_advances readBorrow_loan
  readBorrow_preserves issue_shared issue_preserves close_shared close_other finishLoan_resources
  finishLoan_handles finishLoan_other exchange_keeps finishLoan_revokes)

def Retains (before after : Atomics.State) (worker : Worker) : Prop :=
  after.handles worker.handle = before.handles worker.handle ∧
    after.shared.loans worker.codeLoan = before.shared.loans worker.codeLoan ∧
    after.shared.loans worker.stackLoan = before.shared.loans worker.stackLoan

theorem WorkerValid.frame {before after : Atomics.State} {identifier : Nat} {worker : Worker}
    (workerValid : WorkerValid before identifier worker) (valid : Atomics.WellFormed before)
    (history : Atomics.History before after) (kept : Retains before after worker) :
    WorkerValid after identifier worker := by
  obtain ⟨parent, handle, code, stack, distinct, executable, target, canonical, privateContext⟩ := workerValid
  obtain ⟨record, live, actor, address⟩ := handle
  obtain ⟨codeAfter, codeCells⟩ := code.frame valid.shared history.borrowing kept.2.1
  obtain ⟨stackAfter, stackCells⟩ := stack.frame valid.shared history.borrowing kept.2.2
  exact ⟨parent, ⟨record, kept.1.trans live, actor, address⟩, codeAfter, stackAfter, distinct,
    agrees_code _ _ _ _ codeCells executable,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans target, canonical, privateContext⟩

theorem WorkerValid.authorized {shared : Atomics.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) :
    ∃ handle, Atomics.authorize shared (principal identifier) worker.handle = .ok handle ∧
      handle.address = worker.entry.registers .rdi := by
  obtain ⟨handle, live, actor, address⟩ := valid.handle
  exact ⟨handle, by simp [Atomics.authorize, live, actor], address⟩

theorem fetchAdd_keeps {before : Atomics.State} {actor identifier : Nat} {delta : BitVec 32}
    {result : Atomics.State × BitVec 32} (success : Atomics.fetchAdd before actor identifier delta = .ok result) :
    result.1.handles = before.handles ∧ result.1.shared.loans = before.shared.loans := by
  obtain ⟨_, _, _, exchanged⟩ := Atomics.fetchAdd_ok _ _ _ _ _ success
  exact exchange_keeps exchanged

end EDSL.OS.CounterThreads
