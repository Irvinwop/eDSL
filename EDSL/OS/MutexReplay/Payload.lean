/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Invariant
import EDSL.OS.MutexReplay.Control

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

private theorem bind_ok {first : Except ε α} {next : α → Except ε β} {value : β} :
    (first >>= next) = .ok value ↔
      ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp

private theorem mapError_ok {first : Except ε α} {map : ε → ε'} {value : α} :
    first.mapError map = .ok value ↔ first = .ok value := by
  cases first <;> simp [Except.mapError]

private theorem plain_ok (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (instruction : Plain) (result : Result)
    (success : perform shared identifier worker (.plain instruction) = .ok result) :
    result.shared = shared ∧ result.guard = worker.guard ∧
      runNext shared worker.context instruction.instruction = .ok result.context := by
  cases ran : runNext shared worker.context instruction.instruction with
  | error fault => simp [perform, ran] at success
  | ok context =>
    simp [perform, ran] at success
    subst result
    exact ⟨rfl, rfl, rfl⟩

/-- The actual LEA increments EAX modulo 2^32, including wraparound. -/
theorem runNext_increment_accumulator (shared : Mutex.State) (before after : Context)
    (success : runNext shared before (.leaEaxRaxDisp8 1) = .ok after) :
    (after.registers .rax).setWidth 32 = (before.registers .rax).setWidth 32 + 1 := by
  obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ success
  simp [X86.step, decoded] at stepped
  subst output
  simp only [same, Threads.Context.ofState, executeLeaRax, X86.State.writeRegister,
    Threads.Context.snapshot, ↓reduceIte]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_eq]
  rw [BitVec.setWidth_add _ _ (by decide)]
  rfl

private theorem acquire_ok (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (result : Result) (success : perform shared identifier worker .acquire = .ok result) :
    ∃ attempt, Mutex.tryAcquire shared (principal identifier) = .ok attempt ∧
      result.shared = attempt.state ∧ result.guard = attempt.acquired := by
  simp only [perform, bind_ok, mapError_ok] at success
  obtain ⟨record, _, success⟩ := success
  split at success
  · simp_all
  · simp only [bind_ok, mapError_ok] at success
    obtain ⟨attempt, acquired, context, _, same⟩ := success
    simp only [pure_ok, Except.ok.injEq] at same
    subst result
    exact ⟨attempt, acquired, rfl, rfl⟩

private theorem load_ok (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (lease : Mutex.Lease) (result : Result)
    (success : perform shared identifier worker (.load lease) = .ok result) :
    ∃ record value, Mutex.authorize shared (principal identifier) lease = .ok record ∧
      worker.context.registers .rsi = record.config.dataAddress ∧
      Mutex.guardLoad shared (principal identifier) lease = .ok value ∧
      runNext shared worker.context .loadEaxRsi = .ok result.context ∧
      result.shared = shared ∧ result.guard = worker.guard := by
  simp only [perform, bind_ok, mapError_ok] at success
  obtain ⟨record, authorized, success⟩ := success
  split at success
  · simp_all
  · rename_i operand
    simp only [bind_ok, mapError_ok] at success
    obtain ⟨value, loaded, context, ran, same⟩ := success
    simp only [pure_ok, Except.ok.injEq] at same
    subst result
    exact ⟨record, value, authorized, Classical.not_not.mp operand, loaded, ran, rfl, rfl⟩

private theorem store_ok (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (lease : Mutex.Lease) (result : Result)
    (success : perform shared identifier worker (.store lease) = .ok result) :
    ∃ record, Mutex.authorize shared (principal identifier) lease = .ok record ∧
      worker.context.registers .rsi = record.config.dataAddress ∧
      Mutex.guardStore shared (principal identifier) lease (accumulator worker) = .ok result.shared ∧
      runNext shared worker.context .storeEaxRsi = .ok result.context ∧
      result.guard = worker.guard := by
  simp only [perform, bind_ok, mapError_ok] at success
  obtain ⟨record, authorized, success⟩ := success
  split at success
  · simp_all
  · rename_i operand
    simp only [bind_ok, mapError_ok] at success
    obtain ⟨after, stored, context, ran, same⟩ := success
    simp only [pure_ok, Except.ok.injEq] at same
    subst result
    exact ⟨record, authorized, Classical.not_not.mp operand, stored, ran, rfl⟩

private theorem store_accumulator (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (lease : Mutex.Lease) (result : Result) (record : Mutex.Registered)
    (authorized : Mutex.authorize shared (principal identifier) lease = .ok record)
    (operand : worker.context.registers .rsi = record.config.dataAddress)
    (stored : Mutex.guardStore shared (principal identifier) lease (accumulator worker) = .ok result.shared)
    (ran : runNext shared worker.context .storeEaxRsi = .ok result.context) :
    accumulator (evolved worker result) = accumulator worker := by
  obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ ran
  have bridge := Mutex.guardStore_step shared (principal identifier) lease _ result.shared record
    (worker.context.snapshot shared.shared.resources.space) stored authorized rfl operand rfl decoded
  have equal := X86.StepResult.next.inj (Except.ok.inj (stepped.symm.trans bridge))
  simp only [accumulator, evolved, same, equal, Threads.Context.ofState, Mutex.afterStore,
    Threads.Context.snapshot]

private theorem authorized_config (shared : Mutex.State) (config : Mutex.Config)
    (identifier : Nat) (worker : Worker) (lease : Mutex.Lease) (record : Mutex.Registered)
    (privateInv : WorkerInvariant shared config identifier worker)
    (held : worker.guard = some lease)
    (authorized : Mutex.authorize shared (principal identifier) lease = .ok record) :
    record.config = config := by
  obtain ⟨current, authority, same⟩ := privateInv.authority lease held
  have equal := Except.ok.inj (authorized.symm.trans authority)
  simpa only [equal] using same

private theorem acquired_config (shared : Mutex.State) (config : Mutex.Config)
    (identifier : Nat) (attempt : Mutex.Attempt) (record : Mutex.Registered)
    (registered : Registered shared config)
    (acquired : Mutex.tryAcquire shared (principal identifier) = .ok attempt)
    (present : attempt.state.mutex = some record) : record.config = config := by
  obtain ⟨original, live, configEq⟩ := registered
  obtain ⟨current, exchanged, found, _, branches⟩ := Mutex.tryAcquire_ok _ _ _ acquired
  have equal := Option.some.inj (found.symm.trans live)
  subst current
  rcases branches with ⟨_, same⟩ | ⟨_, same⟩
  · rw [same] at present
    simp only [Option.some.injEq] at present
    cases present
    exact configEq
  · rw [same] at present
    have equal := Option.some.inj (live.symm.trans present)
    subst record
    exact configEq

private theorem load_accumulator (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (lease : Mutex.Lease) (result : Result) (record : Mutex.Registered) (value : BitVec 32)
    (authorized : Mutex.authorize shared (principal identifier) lease = .ok record)
    (operand : worker.context.registers .rsi = record.config.dataAddress)
    (loaded : Mutex.guardLoad shared (principal identifier) lease = .ok value)
    (ran : runNext shared worker.context .loadEaxRsi = .ok result.context) :
    accumulator (evolved worker result) = value := by
  obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ ran
  have bridge := Mutex.guardLoad_step shared (principal identifier) lease value record
    (worker.context.snapshot shared.shared.resources.space) loaded authorized rfl operand decoded
  have equal := X86.StepResult.next.inj (Except.ok.inj (stepped.symm.trans bridge))
  simp only [accumulator, evolved, same, equal, Threads.Context.ofState, Mutex.afterLoad,
    Threads.Context.snapshot, X86.State.writeRegister, ↓reduceIte]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Each successful selected instruction preserves the payload obligation of
its actual resulting phase. The final store closes the invariant using only
the independently supplied closure under addition by two. -/
theorem advance_payload (state : State) (identifier : Nat) (worker : Worker)
    (result : Result) (config : Mutex.Config)
    (valid : Mutex.WellFormed state.shared) (registered : Registered state.shared config)
    (privateInv : WorkerInvariant state.shared config identifier worker)
    (closed : ClosedUnderTwo config)
    (success : advance state identifier worker = .ok result) :
    ∀ lease, (evolved worker result).guard = some lease →
      Payload result.shared config (evolved worker result) := by
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ success
  cases phase : worker.phase with
  | entry | releasing | finishing | returning | completed =>
    simp [Payload, evolved, nextPhase, phase]
  | acquiring =>
    have control : worker.guard = none ∧ worker.context.registers .rax = 1 := by
      simpa only [Control, phase] using privateInv.control
    have free := control.1
    simp [action, phase, free] at selected
    subst operation
    obtain ⟨attempt, acquired, sharedEq, guardEq⟩ := acquire_ok _ _ _ _ performed
    intro lease held
    have granted : attempt.acquired = some lease := by simpa only [evolved, guardEq] using held
    rcases Mutex.acquisition _ _ _ valid acquired with opened | busy
    · obtain ⟨actualLease, record, _, present, _, _, _, payload, _, _⟩ := opened
      have configEq := acquired_config _ _ _ _ _ registered acquired present
      simpa only [Payload, evolved, nextPhase, phase, sharedEq, configEq] using payload
    · rw [busy.1] at granted
      cases granted
  | comparing =>
    simp [action, phase] at selected
    subst operation
    obtain ⟨sharedEq, guardEq, _⟩ := plain_ok _ _ _ _ _ performed
    intro lease held
    have beforeHeld : worker.guard = some lease := by simpa only [evolved, guardEq] using held
    have payload := privateInv.payload lease beforeHeld
    simpa only [Payload, evolved, nextPhase, phase, sharedEq] using payload
  | branching =>
    simp [action, phase] at selected
    subst operation
    obtain ⟨sharedEq, guardEq, _⟩ := plain_ok _ _ _ _ _ performed
    intro lease held
    have beforeHeld : worker.guard = some lease := by simpa only [evolved, guardEq] using held
    have payload : Mutex.Closed state.shared.shared config := by
      simpa only [Payload, phase] using privateInv.payload lease beforeHeld
    by_cases retry : result.context.rip = worker.entry.rip
    · simp [Payload, evolved, nextPhase, phase, retry]
    · simpa only [Payload, evolved, nextPhase, phase, retry, ↓reduceIte, sharedEq] using payload
  | loading =>
    cases guardAt : worker.guard with
    | none => simp [action, phase, guardAt] at selected
    | some guard =>
      simp [action, phase, guardAt] at selected
      subst operation
      obtain ⟨record, value, authorized, operand, loaded, ran, sharedEq, _⟩ := load_ok _ _ _ _ _ performed
      have configEq := authorized_config _ _ _ _ _ _ privateInv guardAt authorized
      have observed : loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress = .ok value := by
        simpa only [Mutex.guardLoad, authorized, ok_bind, mapError_ok, configEq] using loaded
      have valueEq := load_accumulator _ _ _ _ _ _ _ authorized operand loaded ran
      simp only [accumulator, evolved] at valueEq
      have payload : Mutex.Closed state.shared.shared config := by
        simpa only [Payload, phase] using privateInv.payload guard guardAt
      obtain ⟨base, beforeRead, invariant⟩ := payload
      have equal := Except.ok.inj (beforeRead.symm.trans observed)
      subst base
      intro lease held
      simpa only [Payload, evolved, nextPhase, phase, sharedEq, accumulator, valueEq] using
        And.intro observed invariant
  | incrementingFirst =>
    simp [action, phase] at selected
    subst operation
    obtain ⟨sharedEq, guardEq, ran⟩ := plain_ok _ _ _ _ _ performed
    have valueEq : accumulator (evolved worker result) = accumulator worker + 1 :=
      runNext_increment_accumulator _ _ _ ran
    simp only [accumulator, evolved] at valueEq
    intro lease held
    have beforeHeld : worker.guard = some lease := by simpa only [evolved, guardEq] using held
    have payload := privateInv.payload lease beforeHeld
    simpa only [Payload, evolved, nextPhase, phase, sharedEq, accumulator, valueEq,
      BitVec.add_sub_cancel] using payload
  | storingFirst =>
    cases guardAt : worker.guard with
    | none => simp [action, phase, guardAt] at selected
    | some guard =>
      simp [action, phase, guardAt] at selected
      subst operation
      obtain ⟨record, authorized, operand, stored, ran, _⟩ := store_ok _ _ _ _ _ performed
      have configEq := authorized_config _ _ _ _ _ _ privateInv guardAt authorized
      have observed := Mutex.guardStore_value _ _ _ _ _ _ authorized stored
      rw [configEq] at observed
      have valueEq := store_accumulator _ _ _ _ _ _ authorized operand stored ran
      simp only [accumulator, evolved] at valueEq
      have payload := privateInv.payload guard guardAt
      simp only [Payload, phase] at payload
      intro lease held
      simpa only [Payload, evolved, nextPhase, phase, accumulator, valueEq] using
        And.intro observed payload.2
  | incrementingSecond =>
    simp [action, phase] at selected
    subst operation
    obtain ⟨sharedEq, guardEq, ran⟩ := plain_ok _ _ _ _ _ performed
    have valueEq : accumulator (evolved worker result) = accumulator worker + 1 :=
      runNext_increment_accumulator _ _ _ ran
    simp only [accumulator, evolved] at valueEq
    have subtract (value : BitVec 32) : value + 1 - 2 = value - 1 := by
      rw [show (2 : BitVec 32) = 1 + 1 by decide, ← BitVec.sub_sub, BitVec.add_sub_cancel]
    intro lease held
    have beforeHeld : worker.guard = some lease := by simpa only [evolved, guardEq] using held
    have payload := privateInv.payload lease beforeHeld
    simpa only [Payload, evolved, nextPhase, phase, sharedEq, accumulator, valueEq,
      BitVec.add_sub_cancel, subtract] using payload
  | storingSecond =>
    cases guardAt : worker.guard with
    | none => simp [action, phase, guardAt] at selected
    | some guard =>
      simp [action, phase, guardAt] at selected
      subst operation
      obtain ⟨record, authorized, operand, stored, ran, _⟩ := store_ok _ _ _ _ _ performed
      have configEq := authorized_config _ _ _ _ _ _ privateInv guardAt authorized
      have observed := Mutex.guardStore_value _ _ _ _ _ _ authorized stored
      rw [configEq] at observed
      have valueEq := store_accumulator _ _ _ _ _ _ authorized operand stored ran
      simp only [accumulator, evolved] at valueEq
      have payload := privateInv.payload guard guardAt
      simp only [Payload, phase] at payload
      have invariant := closed (accumulator worker - 2) payload.2
      rw [BitVec.sub_add_cancel] at invariant
      intro lease held
      simpa only [Payload, evolved, nextPhase, phase, accumulator, valueEq] using
        And.intro observed invariant
  | preparingRelease =>
    simp [action, phase] at selected
    subst operation
    obtain ⟨sharedEq, guardEq, _⟩ := plain_ok _ _ _ _ _ performed
    intro lease held
    have beforeHeld : worker.guard = some lease := by simpa only [evolved, guardEq] using held
    have payload := privateInv.payload lease beforeHeld
    simp only [Payload, phase] at payload
    simpa only [Payload, evolved, nextPhase, phase, sharedEq] using
      (show Mutex.Closed state.shared.shared config from ⟨accumulator worker, payload⟩)

end EDSL.OS.MutexReplay
