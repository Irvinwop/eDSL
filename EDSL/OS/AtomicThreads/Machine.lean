/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Framing
import EDSL.OS.Threads.Machine

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

theorem codeMatches_sound (space : Space) (entry : Word) (checked : codeMatches space entry = true) :
    CodeAt (toMemory space) entry Examples.Compiler.Exchange.bytes := by
  simp only [codeMatches, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨bound, a⟩, b⟩, c⟩, d⟩, e⟩ := checked
  refine ⟨bound, ?_⟩
  intro offset byte present
  match offset with
  | 0 =>
    simp [Examples.Compiler.Exchange.bytes] at present
    subst byte
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using Threads.byteMatches_sound _ _ _ a
  | 1 =>
    simp [Examples.Compiler.Exchange.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ b
  | 2 =>
    simp [Examples.Compiler.Exchange.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ c
  | 3 =>
    simp [Examples.Compiler.Exchange.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ d
  | 4 =>
    simp [Examples.Compiler.Exchange.bytes] at present
    subst byte
    exact Threads.byteMatches_sound _ _ _ e
  | offset + 5 => simp [Examples.Compiler.Exchange.bytes] at present

theorem preparing_decode (entry : Context) (space : Space)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.Exchange.bytes) :
    decodeAt (entry.snapshot space) = .ok .movEaxEsi := by
  have b0 := code.2 0 0x89 (by decide)
  have b1 := code.2 1 0xf0 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1
  simp [decodeAt, Threads.Context.snapshot, b0, b1]

theorem exchanging_decode (entry : Context) (space : Space)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.Exchange.bytes) :
    decodeAt ((prepared entry).snapshot space) = .ok .exchangeEaxRdi := by
  have b2 := code.2 2 0x87 (by decide)
  have b3 := code.2 3 0x07 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at b2 b3
  simp [decodeAt, Threads.Context.snapshot, prepared, b2, BitVec.add_assoc, b3]

theorem returning_decode (entry : Context) (space : Space) (old : BitVec 32)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.Exchange.bytes) :
    decodeAt ((exchanged entry old).snapshot space) = .ok .ret := by
  have b4 := code.2 4 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at b4
  simp [decodeAt, Threads.Context.snapshot, exchanged, b4]

theorem preparing_step (entry : Context) (space : Space)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.Exchange.bytes) :
    X86.step (entry.snapshot space) = .ok (.next ((prepared entry).snapshot space)) := by
  simp only [X86.step, preparing_decode entry space code, ok_bind, pure_ok]
  rfl

@[simp] theorem prepared_rdi (entry : Context) : (prepared entry).registers .rdi = entry.registers .rdi := by
  simp [prepared]

@[simp] theorem prepared_replacement (entry : Context) :
    ((prepared entry).registers .rax).setWidth 32 = (entry.registers .rsi).setWidth 32 := by
  simp [prepared]

theorem exchange_context (entry : Context) (before after : Space) (old : BitVec 32) :
    Threads.Context.ofState (Atomics.afterExchange ((prepared entry).snapshot before) after old) = exchanged entry old := by
  simp [Threads.Context.ofState, Atomics.afterExchange, Threads.Context.snapshot, prepared, exchanged,
    X86.State.writeRegister, BitVec.add_assoc]
  funext register
  by_cases same : register = .rax <;> simp [same]

theorem returning_step (entry : Context) (space : Space) (old : BitVec 32) (target : Word)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.Exchange.bytes)
    (stack : readWord (toMemory space) (entry.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    X86.step ((exchanged entry old).snapshot space) =
      .ok (.returned ((entry.returned old target).snapshot space)) := by
  simp only [X86.step, returning_decode entry space old code, ok_bind, pure_ok]
  simp [executeRet, stack, canonical,
    Threads.Context.snapshot, Threads.Context.returned, exchanged, X86.State.writeRegister]

theorem WorkerValid.completed_result {shared : Atomics.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) {old : BitVec 32} {context : Context}
    (completed : worker.phase = .completed old context) : context.registers .rax = old.setWidth 64 := by
  have phase := valid.phase
  rw [completed] at phase
  change context = worker.entry.returned old worker.returnAddress at phase
  rw [phase]
  simp [Threads.Context.returned]

end EDSL.OS.AtomicThreads
