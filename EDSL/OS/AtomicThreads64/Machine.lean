/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Framing

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Code admission certifies precisely the actual five fetched bytes. -/
theorem codeMatches_sound (space : Space) (entry : Word) (checked : codeMatches space entry = true) :
    CodeAt (toMemory space) entry Atomics64.Routine.bytes := by
  simp only [codeMatches, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨bound, a⟩, b⟩, c⟩, d⟩, e⟩ := checked
  refine ⟨bound, ?_⟩
  intro offset byte present
  match offset with
  | 0 =>
    simp [Atomics64.Routine.bytes] at present
    subst byte
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using Threads.byteMatches_sound _ _ _ a
  | 1 =>
    simp [Atomics64.Routine.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ b
  | 2 =>
    simp [Atomics64.Routine.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ c
  | 3 =>
    simp [Atomics64.Routine.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ d
  | 4 =>
    simp [Atomics64.Routine.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ e
  | offset + 5 => simp [Atomics64.Routine.bytes] at present

theorem applying_decode (entry : Context) (space : Space)
    (code : CodeAt (toMemory space) entry.rip Atomics64.Routine.bytes) :
    LockedLogical64.decodeAt (entry.snapshot space) = .ok .orRdiRsi :=
  LockedLogical64.decodeAt_of_code .orRdiRsi (Atomics64.Routine.first_code code)

theorem returning_decode (entry : Context) (space : Space) (value : Word) (chosen : Bool)
    (code : CodeAt (toMemory space) entry.rip Atomics64.Routine.bytes) :
    LockedLogical64.decodeAt ((applied entry value chosen).snapshot space) = .ok .ret :=
  LockedLogical64.decodeAt_of_code .ret (Atomics64.Routine.return_code code)

theorem apply_context (entry : Context) (before after : Space) (value : Word) (af : Bool) :
    Threads.Context.ofState (LockedLogical64.afterOr (entry.snapshot before) (toMemory after) value af) =
      applied entry value af := rfl

/-- RET reads current RAM, keeps its peer's latest data and ignores the new AF
choice. Only its current private RSP is advanced. -/
theorem returning_step (entry : Context) (space : Space) (value : Word) (chosen af : Bool)
    (target : Word) (code : CodeAt (toMemory space) entry.rip Atomics64.Routine.bytes)
    (stack : readWord (toMemory space) (entry.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    LockedLogical64.step af ((applied entry value chosen).snapshot space) =
      .ok ⟨.returned ((returned (applied entry value chosen) target).snapshot space),
        [.stack8 (entry.registers .rsp)]⟩ := by
  rw [LockedLogical64.step_eq_execute af (returning_decode entry space value chosen code)]
  simpa [returned, applied, Threads.Context.snapshot, X86.State.writeRegister] using
    LockedLogical64.execute_ret_context ((applied entry value chosen).snapshot space)
      target af stack canonical

theorem WorkerValid.completed_result {shared : Atomics64.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) {event : Atomics64.Event} {context : Context}
    (completed : worker.phase = .completed event context) :
    context.registers .rax = worker.entry.registers .rax ∧
      context.registers .rsp = worker.entry.registers .rsp + 8 ∧ context.rip = worker.returnAddress ∧
      ∀ register, register ≠ .rsp → context.registers register = worker.entry.registers register := by
  have phase := valid.phase
  rw [completed] at phase
  obtain ⟨af, shape⟩ := phase
  rw [shape]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro register different
  simp [returned, applied, different]

theorem WorkerValid.authorized {shared : Atomics64.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (sharedValid : Atomics64.WellFormed shared) :
    ∃ handle cell, Atomics64.authorize shared (principal identifier) worker.handle = .ok (handle, cell) ∧
      cell.address = worker.entry.registers .rdi ∧ handle.cell = worker.cell := by
  obtain ⟨handle, cell, live, actor, link, registered, address⟩ := valid.handle
  exact ⟨handle, cell, Atomics64.authorize_success _ _ _ _ _ sharedValid live actor
    (by rw [link]; exact registered), address, link⟩

end EDSL.OS.AtomicThreads64
