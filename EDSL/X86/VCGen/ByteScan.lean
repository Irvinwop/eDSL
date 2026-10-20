/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.BufferCall
import EDSL.Grading.ByteScan

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.ByteScan
open Sequential Grading.ByteScan

/-- Common frame for scans using RAX/RDX as scratch. In particular RDI, RSI,
the original caller slot, all callee saves and nonarithmetic flags survive.
RAM equality includes all permission maps; no disjointness is assumed. -/
structure CommonFrame (initial state : State) : Prop where
  memory : state.memory = initial.memory
  registers : ∀ register, register ≠ .rax → register ≠ .rdx →
    state.registers register = initial.registers register
  flags : state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem commonFrame_iff (initial state : State) : CommonFrame initial state ↔
    state.memory = initial.memory ∧
    (∀ register, register ≠ .rax → register ≠ .rdx →
      state.registers register = initial.registers register) ∧
    state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask :=
  ⟨fun frame => ⟨frame.memory, frame.registers, frame.flags⟩, fun ⟨m, r, f⟩ => ⟨m, r, f⟩⟩

theorem CommonFrame.refl (initial : State) : CommonFrame initial initial :=
  ⟨rfl, fun _ _ _ => rfl, rfl⟩

theorem CommonFrame.rsp {initial state : State} (frame : CommonFrame initial state) :
    state.registers .rsp = initial.registers .rsp := frame.registers .rsp (by decide) (by decide)

theorem CommonFrame.rdi {initial state : State} (frame : CommonFrame initial state) :
    state.registers .rdi = initial.registers .rdi := frame.registers .rdi (by decide) (by decide)

theorem CommonFrame.rsi {initial state : State} (frame : CommonFrame initial state) :
    state.registers .rsi = initial.registers .rsi := frame.registers .rsi (by decide) (by decide)

theorem saved_different (register : Register) (saved : register ∈ PureCall.calleeSaved) :
    register ≠ .rsp ∧ register ≠ .rax ∧ register ≠ .rdx := by
  simp only [PureCall.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Discharge the common return contract once, from a pre-RET frame and the
independent mathematical result. The caller target is the original one. -/
theorem CommonFrame.return_post {input : BufferCall.Invocation spec} {initial state : State}
    (frame : CommonFrame initial state)
    (correct : BoundedNulLength input.value.values (state.registers .rax).toNat) :
    BufferCall.Post spec input initial
      { state.writeRegister .rsp (state.registers .rsp + 8) with rip := input.returnAddress } := by
  refine ⟨correct, frame.memory, rfl, ?_, ?_, frame.flags⟩
  · simpa only [State.writeRegister, ite_true] using congrArg (· + (8 : Word)) frame.rsp
  · intro register saved
    have different : register ≠ .rsp ∧ register ≠ .rax ∧ register ≠ .rdx := by
      simp only [PureCall.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at saved
      rcases saved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [State.writeRegister, different.1, ite_false] using
      frame.registers register different.2.1 different.2.2

variable {bytes : List Byte} {input : BufferCall.Invocation spec} {initial state : State}

theorem count_small (pre : BufferCall.Pre spec bytes input initial) :
    input.value.values.length < 2^64 := pre.domain

theorem count_nat (pre : BufferCall.Pre spec bytes input initial) :
    (BitVec.ofNat 64 input.value.values.length).toNat = input.value.values.length := by
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (count_small pre)]

theorem base_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rdi = input.value.base := pre.arguments 0 (.word64 input.value.base) rfl

theorem count_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rsi = BitVec.ofNat 64 input.value.values.length :=
  pre.arguments 1 (.word64 (BitVec.ofNat 64 input.value.values.length)) rfl

/-- One real byte read and its full positive span authority, at any valid
natural index. There is deliberately no such obligation at an empty input. -/
theorem read_byte (pre : BufferCall.Pre spec bytes input initial)
    (frame : CommonFrame initial state) {index : Nat} (inside : index < input.value.values.length) :
    ∃ byte, input.value.values[index]? = some byte ∧
      readDataByte state.memory (input.value.base + BitVec.ofNat 64 index) = .ok byte ∧
      BufferCall.RawRead spec input initial
        ⟨.data, input.value.base + BitVec.ofNat 64 index, 1⟩ := by
  let buffer : BufferCall.Buffer := ⟨input.value.base, input.value.values⟩
  have member : buffer ∈ spec.buffers input.value := by simp [spec, buffer]
  have snapshot := pre.buffers buffer member
  have present : input.value.values[index]? = some input.value.values[index] :=
    List.getElem?_eq_getElem inside
  refine ⟨_, present, ?_, Or.inr ⟨rfl, buffer, member, ?_⟩⟩
  · rw [frame.memory]
    exact snapshot.2 index _ present
  · change 0 < 1 ∧ _ ≤ _ ∧ _ + 1 ≤ _
    rw [BufferCall.Buffer.offset_address snapshot inside]
    dsimp only [buffer]
    exact ⟨by decide, by omega, by omega⟩

/-- Full-width increment cannot wrap before the admitted mathematical bound. -/
theorem next_nat {count : Nat} {index : Word} (small : count < 2^64)
    (inside : index.toNat < count) : (index + 1).toNat = index.toNat + 1 := by
  have sum : index.toNat + 1 < 2^64 := by omega
  rw [BitVec.toNat_add]
  change (index.toNat + 1) % 2^64 = index.toNat + 1
  exact Nat.mod_eq_of_lt sum

theorem next_rank {count : Nat} {index : Word} (small : count < 2^64)
    (inside : index.toNat < count) : count - (index + 1).toNat < count - index.toNat := by
  rw [next_nat small inside]
  omega

/-- Reuse the spec's prefix step at the exact machine increment. -/
theorem advance {values : List Byte} {index : Word} {byte : Byte}
    (small : values.length < 2^64) (inside : index.toNat < values.length)
    (scanned : NonzeroPrefix values index.toNat) (present : values[index.toNat]? = some byte)
    (nonzero : byte ≠ 0) : NonzeroPrefix values (index + 1).toNat := by
  rw [next_nat small inside]
  exact scanned.advance present nonzero

end EDSL.X86.VCGen.ByteScan
