/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Loans

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- Concrete executable bytes and the saved return word, protected by the
actual stored read loans. These are initial execution facts, not a premise
about the success or final result of a future dispatch. -/
structure WorkerExecutionReady (shared : Borrowing.State) (identifier : Nat) (worker : Worker) : Prop where
  loans : WorkerLoanReady shared identifier worker
  code : CodeAt (toMemory shared.resources.space) worker.entry.rip bytes
  stack : readWord (toMemory shared.resources.space) (worker.entry.registers .rsp) = .ok worker.returnAddress
  canonical : X86.canonical worker.returnAddress = true

def ExecutionReady (state : State) : Prop :=
  ∀ identifier worker, state.workers[identifier]? = some worker → WorkerExecutionReady state.shared.shared identifier worker

end EDSL.OS.MutexReplay
