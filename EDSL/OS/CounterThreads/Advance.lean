/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Machine

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

def evolved (worker : Worker) (context : Context) : Worker :=
  { worker with phase := nextPhase worker.phase context, context := context }

theorem advance_entry (state : State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid state.shared identifier worker) (phase : worker.phase = .entry) :
    advance state identifier worker = .ok ⟨state.shared, evolved worker (entryContext worker.context), none⟩ := by
  have decoded := decode_expected state.shared identifier worker (.jrcxz 0x0b) valid (by simp [expected, phase])
  have actual := entry_step state.shared identifier worker valid phase
  have checked := checkedAdvance_success state.shared worker (entryContext worker.context) none
    (entry_private worker valid.privateContext phase)
  simp [advance, expected, phase, decoded, actual, checked, evolved, Except.mapError]

theorem advance_preparing (state : State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid state.shared identifier worker) (phase : worker.phase = .preparing) :
    advance state identifier worker = .ok ⟨state.shared, evolved worker (immediateContext worker.context 1), none⟩ := by
  have decoded := decode_expected state.shared identifier worker (.mov32 .rax 1) valid (by simp [expected, phase])
  have actual := immediate_step state.shared identifier worker 1 valid (by simp [expected, phase])
  have checked := checkedAdvance_success state.shared worker (immediateContext worker.context 1) none
    (preparing_private worker valid.privateContext phase)
  simp only [BitVec.ofNat_eq_ofNat] at checked
  simp [advance, expected, phase, decoded, actual, checked, evolved, Except.mapError]

theorem advance_adding (state : State) (identifier : Nat) (worker : Worker) (result : Atomics.State × BitVec 32)
    (valid : WorkerValid state.shared identifier worker) (phase : worker.phase = .adding)
    (success : Atomics.fetchAdd state.shared (principal identifier) worker.handle 1 = .ok result) :
    advance state identifier worker = .ok ⟨result.1, evolved worker (addedContext worker.context result.2),
      some ⟨worker.entry.registers .rdi, result.2, result.2 + 1⟩⟩ := by
  have decoded := decode_expected state.shared identifier worker .fetchAddEaxRdi valid (by simp [expected, phase])
  have actual := adding_step state.shared identifier worker result valid phase success
  obtain ⟨handle, authorized, address⟩ := valid.authorized
  have p := valid.privateContext
  simp only [PrivateValid, phase] at p
  have operand := p.1.trans address.symm
  have replacement : (worker.context.registers .rax).setWidth 32 = 1 := by rw [p.2.2.2.2.2]; rfl
  have checked := checkedAdvance_success result.1 worker (addedContext worker.context result.2)
    (some ⟨worker.entry.registers .rdi, result.2, result.2 + 1⟩) (adding_private worker result.2 valid.privateContext phase)
  simp only [BitVec.ofNat_eq_ofNat] at checked success replacement
  simp [advance, expected, phase, decoded, actual, authorized, operand, replacement, success, checked, evolved, Except.mapError]

theorem advance_backedge (state : State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid state.shared identifier worker) (phase : worker.phase = .backedge) :
    advance state identifier worker = .ok ⟨state.shared, evolved worker (loopContext worker.context), none⟩ := by
  have decoded := decode_expected state.shared identifier worker (.loopRcx 0xf5) valid (by simp [expected, phase])
  have actual := loop_step state.shared identifier worker valid phase
  have checked := checkedAdvance_success state.shared worker (loopContext worker.context) none
    (backedge_private worker valid.privateContext phase)
  simp [advance, expected, phase, decoded, actual, checked, evolved, Except.mapError]

theorem advance_finishing (state : State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid state.shared identifier worker) (phase : worker.phase = .finishing) :
    advance state identifier worker = .ok ⟨state.shared, evolved worker (immediateContext worker.context 0), none⟩ := by
  have decoded := decode_expected state.shared identifier worker (.mov32 .rax 0) valid (by simp [expected, phase])
  have actual := immediate_step state.shared identifier worker 0 valid (by simp [expected, phase])
  have checked := checkedAdvance_success state.shared worker (immediateContext worker.context 0) none
    (finishing_private worker valid.privateContext phase)
  simp only [BitVec.ofNat_eq_ofNat] at checked
  simp [advance, expected, phase, decoded, actual, checked, evolved, Except.mapError]

theorem advance_returning (state : State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid state.shared identifier worker) (phase : worker.phase = .returning) :
    advance state identifier worker = .ok ⟨state.shared, evolved worker (returnedContext worker.context worker.returnAddress), none⟩ := by
  have decoded := decode_expected state.shared identifier worker .ret valid (by simp [expected, phase])
  have actual := return_step state.shared identifier worker valid phase
  have checked := checkedAdvance_success state.shared worker (returnedContext worker.context worker.returnAddress) none
    (returning_private worker valid.privateContext phase)
  simp [advance, expected, phase, decoded, actual, checked, evolved, Except.mapError]

/-- Inversion of actual checked instruction execution. The only case that can
change shared memory retains its successful authorized fetch-add operation. -/
inductive AdvanceEffect (state : State) (identifier : Nat) (worker : Worker) : Advance → Prop where
  | entry (phase : worker.phase = .entry) : AdvanceEffect state identifier worker
      ⟨state.shared, evolved worker (entryContext worker.context), none⟩
  | preparing (phase : worker.phase = .preparing) : AdvanceEffect state identifier worker
      ⟨state.shared, evolved worker (immediateContext worker.context 1), none⟩
  | adding {result} (phase : worker.phase = .adding)
      (success : Atomics.fetchAdd state.shared (principal identifier) worker.handle 1 = .ok result) :
      AdvanceEffect state identifier worker ⟨result.1, evolved worker (addedContext worker.context result.2),
        some ⟨worker.entry.registers .rdi, result.2, result.2 + 1⟩⟩
  | backedge (phase : worker.phase = .backedge) : AdvanceEffect state identifier worker
      ⟨state.shared, evolved worker (loopContext worker.context), none⟩
  | finishing (phase : worker.phase = .finishing) : AdvanceEffect state identifier worker
      ⟨state.shared, evolved worker (immediateContext worker.context 0), none⟩
  | returning (phase : worker.phase = .returning) : AdvanceEffect state identifier worker
      ⟨state.shared, evolved worker (returnedContext worker.context worker.returnAddress), none⟩

theorem advance_effect (state : State) (identifier : Nat) (worker : Worker) (result : Advance)
    (sharedValid : Atomics.WellFormed state.shared) (valid : WorkerValid state.shared identifier worker)
    (success : advance state identifier worker = .ok result) : AdvanceEffect state identifier worker result := by
  cases phase : worker.phase with
  | completed => simp [advance, expected, phase] at success
  | entry =>
    have same := Except.ok.inj (success.symm.trans (advance_entry state identifier worker valid phase))
    rw [same]
    exact .entry phase
  | preparing =>
    have same := Except.ok.inj (success.symm.trans (advance_preparing state identifier worker valid phase))
    rw [same]
    exact .preparing phase
  | backedge =>
    have same := Except.ok.inj (success.symm.trans (advance_backedge state identifier worker valid phase))
    rw [same]
    exact .backedge phase
  | finishing =>
    have same := Except.ok.inj (success.symm.trans (advance_finishing state identifier worker valid phase))
    rw [same]
    exact .finishing phase
  | returning =>
    have same := Except.ok.inj (success.symm.trans (advance_returning state identifier worker valid phase))
    rw [same]
    exact .returning phase
  | adding =>
    obtain ⟨handle, authorized, _⟩ := valid.authorized
    obtain ⟨added, addedOk⟩ := Atomics.fetchAdd_enabled state.shared (principal identifier) worker.handle handle 1 sharedValid authorized
    have same := Except.ok.inj (success.symm.trans (advance_adding state identifier worker added valid phase addedOk))
    rw [same]
    exact .adding phase addedOk

theorem advance_enabled (state : State) (identifier : Nat) (worker : Worker)
    (sharedValid : Atomics.WellFormed state.shared) (valid : WorkerValid state.shared identifier worker)
    (unfinished : worker.phase ≠ .completed) : ∃ result, advance state identifier worker = .ok result := by
  cases phase : worker.phase with
  | completed => exact False.elim (unfinished phase)
  | entry => exact ⟨_, advance_entry state identifier worker valid phase⟩
  | preparing => exact ⟨_, advance_preparing state identifier worker valid phase⟩
  | backedge => exact ⟨_, advance_backedge state identifier worker valid phase⟩
  | finishing => exact ⟨_, advance_finishing state identifier worker valid phase⟩
  | returning => exact ⟨_, advance_returning state identifier worker valid phase⟩
  | adding =>
    obtain ⟨handle, authorized, _⟩ := valid.authorized
    obtain ⟨added, addedOk⟩ := Atomics.fetchAdd_enabled state.shared (principal identifier) worker.handle handle 1 sharedValid authorized
    exact ⟨_, advance_adding state identifier worker added valid phase addedOk⟩

end EDSL.OS.CounterThreads
