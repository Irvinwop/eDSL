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

end EDSL.OS.Threads
