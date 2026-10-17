/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.GCC

set_option warningAsError true

namespace EDSL.CountedStore64.Common
open EDSL X86 X86.Sequential

variable {program : List Byte}

/-- The current pre-return frame permits changes only to RAX/RDX, arithmetic
flags and the owned target's eight bytes. The complete code and caller slot
remain current across every actual store. -/
structure Frame (program : List Byte) (input : Input) (initial state : State) : Prop where
  code : CodeAt state.memory initial.rip program
  writable : canStoreQWord state.memory input.address = true
  stackRead : readWord state.memory (initial.registers .rsp) = .ok input.returnAddress
  outside : ∀ query, 8 ≤ (query - input.address).toNat →
    state.memory.read query = initial.memory.read query
  writableMap : state.memory.writable = initial.memory.writable
  executableMap : state.memory.executable = initial.memory.executable
  registers : ∀ register, register ≠ .rax → register ≠ .rdx →
    state.registers register = initial.registers register
  flags : state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.initial {input initial} (pre : Pre program input initial) :
    Frame program input initial initial :=
  ⟨pre.memory.code, pre.memory.writable, pre.memory.stack, fun _ _ => rfl,
    rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem Frame.sameMemory {input initial before after}
    (frame : Frame program input initial before) (memory : after.memory = before.memory)
    (registers : ∀ register, register ≠ .rax → register ≠ .rdx →
      after.registers register = before.registers register)
    (flags : after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask) :
    Frame program input initial after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, flags.trans frame.flags⟩
  · rw [memory]; exact frame.code
  · rw [memory]; exact frame.writable
  · rw [memory]; exact frame.stackRead
  · intro query outside; rw [memory]; exact frame.outside query outside
  · rw [memory]; exact frame.writableMap
  · rw [memory]; exact frame.executableMap
  · intro register a d
    exact (registers register a d).trans (frame.registers register a d)

theorem Frame.move {input initial state} (frame : Frame program input initial state) :
    Frame program input initial (GCC.move state) :=
  frame.sameMemory rfl (by intros; simp_all [CountedStore64.GCC.move, State.writeRegister]) rfl

theorem Frame.test {input initial state} (frame : Frame program input initial state) (af : Bool) :
    Frame program input initial (GCC.test state af) :=
  frame.sameMemory rfl (by intros; rfl) (logicalFlags64_preserves ..)

theorem Frame.atPC {input initial state} (frame : Frame program input initial state) (pc : Word) :
    Frame program input initial (GCC.atPC state pc) :=
  frame.sameMemory rfl (by intros; rfl) rfl

theorem Frame.increment {input initial state} (frame : Frame program input initial state) :
    Frame program input initial (GCC.increment state) :=
  frame.sameMemory rfl (by intros; simp_all [CountedStore64.GCC.increment, State.writeRegister])
    (incFlags64_preserves ..)

theorem Frame.decrement {input initial state} (frame : Frame program input initial state) :
    Frame program input initial (GCC.decrement state) :=
  frame.sameMemory rfl (by intros; simp_all [CountedStore64.GCC.decrement, State.writeRegister])
    (decFlags64_preserves ..)

theorem Frame.pointer {input initial state} (frame : Frame program input initial state)
    (pre : Pre program input initial) : state.registers .rdi = input.address :=
  (frame.registers .rdi (by decide) (by decide)).trans pre.memory.pointer

theorem Frame.store {input initial state} (frame : Frame program input initial state)
    (pre : Pre program input initial) : Frame program input initial (GCC.store state) := by
  have pointer := frame.pointer pre
  refine ⟨?_, ?_, ?_, ?_, frame.writableMap, frame.executableMap,
    frame.registers, frame.flags⟩
  · apply writeQWord_preserves_code _ _ _ _ _ frame.code
    simpa only [pointer] using pre.memory.codeDisjoint
  · simpa only [CountedStore64.GCC.store, pointer] using
      canStoreQWord_after_write state.memory input.address (state.registers .rax) frame.writable
  · apply (readWord_congr _ _ _ (writeQWord_agrees _ _ _ _ 8 ?_)).trans frame.stackRead
    simpa only [pointer] using pre.memory.stackDisjoint
  · intro query outside
    exact (writeQWord_frame state.memory _ query _
      (by simpa only [pointer] using outside)).trans (frame.outside query outside)


end EDSL.CountedStore64.Common
