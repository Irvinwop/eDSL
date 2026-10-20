/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientProjection
import EDSL.OS.Futex.LoanFrames
import EDSL.OS.Futex.ClientFrames
import EDSL.Audit

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

/-- Current immutable code and the complete saved return word are resources
of a selected program, independently of its control-flow representation. -/
structure CodeBinding where
  subject : Nat
  codeLoan : Nat
  stackLoan : Nat
  entry : Threads.Context
  bytes : List Byte
  returnTarget : Word

/-- Exact present loans, code, stack and original-byte frames. This contract
contains no instruction/service enabledness or future successful trace. -/
def CodeBinding.Protected (binding : CodeBinding) (seed : Space) (state : Futex.State) : Prop :=
  Threads.HasLoan state.authority.shared binding.subject binding.codeLoan
    ⟨binding.entry.rip, binding.bytes.length⟩ ∧
  Threads.HasLoan state.authority.shared binding.subject binding.stackLoan
    ⟨binding.entry.registers .rsp, 8⟩ ∧
  CodeAt state.suspended.machine.memory binding.entry.rip binding.bytes ∧
  readWord state.suspended.machine.memory (binding.entry.registers .rsp) = .ok binding.returnTarget ∧
  canonical binding.returnTarget = true ∧
  AgreesOn state.authority.shared.resources.space seed binding.entry.rip binding.bytes.length ∧
  AgreesOn state.authority.shared.resources.space seed (binding.entry.registers .rsp) 8

/-- Actual authorized FIFO entries cannot overlap the current complete return
loan. Forwarding therefore retains the saved word, even for a nonempty FIFO. -/
theorem CodeBinding.Protected.stackView {binding : CodeBinding} {seed : Space}
    {state : Futex.State} {buffer : StoreBuffer.Buffer}
    (protection : binding.Protected seed state) (valid : Atomics.WellFormed state.authority)
    (fifo : ∀ store ∈ buffer, ∃ grant : Storage.Grant,
      grant.Valid state.authority ∧ grant.address = store.address) :
    readWord (StoreBuffer.view state.suspended.machine.memory buffer)
      (binding.entry.registers .rsp) = .ok binding.returnTarget := by
  have separate : ∀ store ∈ buffer,
      DWordDisjoint store.address (binding.entry.registers .rsp) 8 := by
    intro store queued
    obtain ⟨grant, authorized, address⟩ := fifo store queued
    rw [← address]
    exact authorized.disjoint_hasLoan valid protection.2.1
  exact (StoreBuffer.view_readWord_frame _ _ _ separate).trans protection.2.2.2.1

/-- Actual managed transitions preserve these present obligations through the
loan registry and resource history, including across unrelated peer effects. -/
theorem CodeBinding.Protected.step {binding : CodeBinding} {seed : Space}
    {profile : Physical.Profile} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (runtime : Runtime.Invariant profile state) (protection : binding.Protected seed state)
    (actual : Runtime.step profile state action = .ok result) : binding.Protected seed result.1 := by
  obtain ⟨codeLoan, stackLoan, code, stack, target, codeSeed, stackSeed⟩ := protection
  have after := (Runtime.step_invariant runtime actual).1
  have memoryFrame := Runtime.step_memory_frame runtime actual
  have history := (Runtime.step_invariant runtime actual).2
  have sameLoans := Runtime.step_loans actual
  have codeFrame := codeLoan.frame runtime.service.authority.shared history.borrowing
    (congrFun sameLoans binding.codeLoan)
  have stackFrame := stackLoan.frame runtime.service.authority.shared history.borrowing
    (congrFun sameLoans binding.stackLoan)
  refine ⟨codeFrame.1, stackFrame.1, memoryFrame.codeAt code, ?_, target, ?_, ?_⟩
  · rw [← runtime.memory] at stack
    rw [← after.memory]
    exact (readWord_congr _ _ _ (agrees_read _ _ _ _ stackFrame.2)).trans stack
  · intro offset bound
    exact (codeFrame.2 offset bound).trans (codeSeed offset bound)
  · intro offset bound
    exact (stackFrame.2 offset bound).trans (stackSeed offset bound)

theorem CodeBinding.Protected.trace {binding : CodeBinding} {seed : Space}
    {profile : Physical.Profile} {before after : Futex.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (protection : binding.Protected seed before) (runtime : Runtime.Invariant profile before)
    (actual : Runtime.Trace profile before actions observations after) : binding.Protected seed after := by
  induction actual with
  | nil => exact protection
  | cons first tail ih => exact ih (protection.step runtime first) (Runtime.step_invariant runtime first).1

end EDSL.OS.Futex.Predicate

#audit_edsl
