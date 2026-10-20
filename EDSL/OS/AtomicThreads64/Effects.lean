/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Mutation

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Inversion retains the actual checked OS operation and the precise AF choice
used by the selected CPU instruction. No independent RMW label is admitted. -/
inductive DispatchEffect (state : State) (identifier : Nat) (af : Bool) (worker : Worker) :
    State × Option Atomics64.Event → Prop where
  | applying {context result} (phase : worker.phase = .applying context)
      (success : Atomics64.logicalDiscard state.shared (principal identifier) worker.handle
        (worker.entry.registers .rsi) = .ok result) :
      DispatchEffect state identifier af worker
        ({ replace state identifier (some { worker with phase := .returning result.2 (applied worker.entry result.2.logical.event.after af) }) with
          shared := result.1 }, some result.2)
  | returning {event context} (phase : worker.phase = .returning event context) :
      DispatchEffect state identifier af worker (replace state identifier
        (some { worker with phase := .completed event (returned context worker.returnAddress) }), none)

theorem dispatch_effect (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧ DispatchEffect state identifier af worker result := by
  cases found : state.workers identifier with
  | none => simp [dispatch, found] at success
  | some worker =>
    have workerValid := (valid.2 _ _ found).2
    refine ⟨worker, rfl, ?_⟩
    cases phase : worker.phase with
    | returning event context =>
      have same := Except.ok.inj (success.symm.trans (dispatch_returning _ _ _ _ _ _ found workerValid phase))
      rw [same]
      exact .returning phase
    | completed event context => rw [dispatch_completed _ _ _ _ _ _ found phase] at success; cases success
    | applying context =>
      obtain ⟨handle, cell, authorized, _, _⟩ := workerValid.authorized valid.1
      obtain ⟨shared, changed⟩ := Atomics64.logicalDiscard_enabled _ _ _
        (worker.entry.registers .rsi) handle cell valid.1 authorized
      have same := Except.ok.inj (success.symm.trans (dispatch_applying _ _ _ _ _ _ found valid phase changed))
      rw [same]
      exact .applying phase changed

/-- This projects managed dispatch to lower-level proof evidence. It does NOT
admit arbitrary lower-level histories into the managed scheduler. -/
theorem dispatch_history (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    Atomics64.History state.shared [result.2] result.1.shared := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ => exact .next .idle .refl
  | applying _ changed => exact .next (.logicalDiscard changed) .refl

theorem dispatch_frame (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    result.1.nextThread = state.nextThread ∧
      ∀ query, query ≠ identifier → result.1.workers query = state.workers query := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect <;> exact ⟨rfl, fun query different => by simp [replace, different]⟩

theorem dispatch_keeps (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.cells = state.shared.cells ∧
      result.1.shared.legacy.shared.loans = state.shared.legacy.shared.loans := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ => exact ⟨rfl, rfl, rfl⟩
  | applying _ changed =>
    have effect := Atomics64.logicalDiscard_effect _ _ _ _ _ changed
    exact ⟨effect.handles, effect.cells, effect.shared.loans⟩

/-- A returning selection leaves the complete CURRENT shared state untouched,
including every peer update since this worker's atomic selection. -/
theorem dispatch_return_ram (state : State) (identifier : Nat) (af : Bool) (after : State)
    (valid : WellFormed state) (success : dispatch state identifier af = .ok (after, none)) :
    after.shared = state.shared := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect
  rfl

/-- Every emitted event is the actual authorized operation result. -/
theorem dispatch_atomic_operation (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker, state.workers identifier = some worker ∧
      Atomics64.logicalDiscard state.shared (principal identifier) worker.handle
        (worker.entry.registers .rsi) = .ok (after.shared, event) := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | applying phase changed => exact ⟨worker, live, changed⟩

/-- Current-before/readback, operation, mask, actor and persistent cell identity
are obtained from real dispatch. Full event retention is separate from RAX. -/
theorem dispatch_atomic_spec (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker current, state.workers identifier = some worker ∧ after.workers identifier = some current ∧
      event.actor = principal identifier ∧ event.handle = worker.handle ∧ event.cell = worker.cell ∧
      event.logical.op = .bor ∧ event.logical.mask = worker.entry.registers .rsi ∧
      event.logical.event.address = worker.entry.registers .rdi ∧
      event.logical.event.after = event.logical.event.before ||| worker.entry.registers .rsi ∧
      loadQWord (toMemory state.shared.legacy.shared.resources.space) event.logical.event.address =
        .ok event.logical.event.before ∧
      loadQWord (toMemory after.shared.legacy.shared.resources.space) event.logical.event.address =
        .ok event.logical.event.after ∧ current.captured = some event := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | @applying context result phase changed =>
    have sound := Atomics64.logicalDiscard_sound _ _ _ _ _ changed
    obtain ⟨handle, cell, authorized, address, link⟩ := ((valid.2 _ _ live).2).authorized valid.1
    have identity := Atomics64.logicalDiscard_identity _ _ _ _ _ _ _ changed authorized
    refine ⟨worker, { worker with phase := .returning result.2 (applied worker.entry result.2.logical.event.after af) },
      live, by simp [replace], sound.2.2.2.2.1, sound.2.2.2.2.2,
      identity.1.trans link, sound.2.1, sound.2.2.1, identity.2.trans address,
      sound.2.2.2.1, sound.1.2.2.1, sound.1.readback, rfl⟩

/-- The selected actual CPU step emits the exact logical label and installs
exactly the checked OS operation's CURRENT resulting RAM. -/
theorem dispatch_atomic_machine (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker, state.workers identifier = some worker ∧
      LockedLogical64.step af (worker.entry.snapshot state.shared.legacy.shared.resources.space) =
        .ok ⟨.atomic64 event.logical (LockedLogical64.afterOr
          (worker.entry.snapshot state.shared.legacy.shared.resources.space)
          (toMemory after.shared.legacy.shared.resources.space) event.logical.event.after af),
          [.rmw8 (worker.entry.registers .rdi)]⟩ := by
  obtain ⟨worker, live, changed⟩ := dispatch_atomic_operation _ _ _ _ _ valid success
  obtain ⟨handle, cell, authorized, address, _⟩ := ((valid.2 _ _ live).2).authorized valid.1
  refine ⟨worker, live, ?_⟩
  simpa only [address] using Atomics64.logicalDiscard_step _ _ _ _ _ _ _ _ af changed authorized rfl
    address.symm rfl (applying_decode _ _ ((valid.2 _ _ live).2).executable)

/-- RET is also an actual current-memory instruction. Its CPU memory is the
unchanged current shared RAM, never the RAM from this worker's earlier RMW. -/
theorem dispatch_return_machine (state : State) (identifier : Nat) (af : Bool) (after : State)
    (valid : WellFormed state) (success : dispatch state identifier af = .ok (after, none)) :
    ∃ worker event context, state.workers identifier = some worker ∧
      worker.phase = .returning event context ∧
      after.workers identifier = some { worker with phase := .completed event (returned context worker.returnAddress) } ∧
      LockedLogical64.step af (context.snapshot state.shared.legacy.shared.resources.space) =
        .ok ⟨.returned ((returned context worker.returnAddress).snapshot state.shared.legacy.shared.resources.space),
          [.stack8 (context.registers .rsp)]⟩ := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | @returning event context phase =>
    have workerValid := (valid.2 _ _ live).2
    refine ⟨worker, event, context, live, phase, by simp [replace], ?_⟩
    have shape := workerValid.phase
    rw [phase] at shape
    obtain ⟨chosen, shape⟩ := shape
    cases shape
    exact returning_step _ _ _ _ _ _ workerValid.executable workerValid.target workerValid.canonical

end EDSL.OS.AtomicThreads64
