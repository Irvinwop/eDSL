/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Framing

namespace EDSL.OS.Threads
open X86 AddressSpace

theorem byteMatches_sound (memory : Memory) (address : Word) (byte : Byte)
    (checked : byteMatches memory address byte = true) : fetchByte memory address = .ok byte := by
  cases observed : fetchByte memory address with
  | error fault => simp [byteMatches, observed] at checked
  | ok actual =>
    have same : actual = byte := by simpa [byteMatches, observed] using checked
    cases same
    rfl

theorem codeMatches_sound (space : Space) (entry : Word) (checked : codeMatches space entry = true) :
    CodeAt (toMemory space) entry Examples.Compiler.MemoryOps.loadBytes := by
  simp only [codeMatches, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨bound, a⟩, b⟩, c⟩ := checked
  refine ⟨bound, ?_⟩
  intro offset byte present
  match offset with
  | 0 =>
    simp [Examples.Compiler.MemoryOps.loadBytes] at present
    subst byte
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using byteMatches_sound _ _ _ a
  | 1 =>
    simp [Examples.Compiler.MemoryOps.loadBytes] at present
    subst byte
    exact byteMatches_sound _ _ _ b
  | 2 =>
    simp [Examples.Compiler.MemoryOps.loadBytes] at present
    subst byte
    exact byteMatches_sound _ _ _ c
  | offset + 3 => simp [Examples.Compiler.MemoryOps.loadBytes] at present

theorem loading_decode (entry : Context) (space : Space)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.MemoryOps.loadBytes) :
    decodeAt (entry.snapshot space) = .ok .loadEaxRdi := by
  have b0 := code.2 0 0x8b (by decide)
  have b1 := code.2 1 0x07 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1
  simp [decodeAt, Context.snapshot, b0, b1]

theorem returning_decode (entry : Context) (space : Space) (value : BitVec 32)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.MemoryOps.loadBytes) :
    decodeAt ((entry.loaded value).snapshot space) = .ok .ret := by
  have b2 := code.2 2 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at b2
  simp [decodeAt, Context.snapshot, Context.loaded, b2]

theorem loading_step (entry : Context) (space : Space) (value : BitVec 32)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.MemoryOps.loadBytes)
    (data : loadDWord (toMemory space) (entry.registers .rdi) = .ok value) :
    X86.step (entry.snapshot space) = .ok (.next ((entry.loaded value).snapshot space)) := by
  have b0 := code.2 0 0x8b (by decide)
  have b1 := code.2 1 0x07 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1
  simp [X86.step, decodeAt, Context.snapshot, b0, b1, executeLoad, data,
    X86.State.writeRegister, Context.loaded]

theorem returning_step (entry : Context) (space : Space) (value : BitVec 32) (target : Word)
    (code : CodeAt (toMemory space) entry.rip Examples.Compiler.MemoryOps.loadBytes)
    (stack : readWord (toMemory space) (entry.registers .rsp) = .ok target)
    (canonical : X86.canonical target = true) :
    X86.step ((entry.loaded value).snapshot space) =
      .ok (.returned ((entry.returned value target).snapshot space)) := by
  have b2 := code.2 2 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at b2
  simp [X86.step, decodeAt, Context.snapshot, Context.loaded, b2, executeRet, stack,
    canonical, X86.State.writeRegister, Context.returned]

@[simp] theorem snapshot_context (context : Context) (space : Space) :
    Context.ofState (context.snapshot space) = context := rfl

theorem WorkerValid.completed_result {shared : Borrowing.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) {context : Context}
    (completed : worker.phase = .completed context) : context.registers .rax = worker.value.setWidth 64 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, phase⟩ := valid
  rw [completed] at phase
  rw [phase]
  simp [Context.returned]

end EDSL.OS.Threads
