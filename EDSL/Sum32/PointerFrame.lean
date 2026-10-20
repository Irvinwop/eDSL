/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.LoopContract

namespace EDSL.Sum32.PointerProof
open X86

/-- The frame of a loop block before RET, including the unchanged stack pointer. -/
structure Frame (initial final : State) : Prop where
  memory : final.memory = initial.memory
  stack : final.registers .rsp = initial.registers .rsp
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.refl (state : State) : Frame state state := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem Frame.trans {first middle final : State} (left : Frame first middle)
    (right : Frame middle final) : Frame first final :=
  ⟨right.memory.trans left.memory, right.stack.trans left.stack,
    fun r h => (right.preserved r h).trans (left.preserved r h), right.flags.trans left.flags⟩

def atPC (state : State) (pc : Word) : State := { state with rip := pc }

def test (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := Sequential.logicalFlags64 state.flags (state.registers .rsi &&& state.registers .rsi) af }

def load (state : State) (value : BitVec 32) : State :=
  { state.writeRegister .rax (((state.registers .rax).setWidth 32 + value).setWidth 64) with
    rip := state.rip + 2,
    flags := addFlags32 state.flags ((state.registers .rax).setWidth 32) value }

def decrement (state : State) : State :=
  { state.writeRegister .rsi (state.registers .rsi - 1) with
    rip := state.rip + 3, flags := Sequential.decFlags64 state.flags (state.registers .rsi) }

def advance (state : State) : State :=
  { state.writeRegister .rdi (state.registers .rdi + 4) with
    rip := state.rip + 4, flags := Sequential.addFlags64 state.flags (state.registers .rdi) 4 }

theorem frame_atPC (state : State) (pc : Word) : Frame state (atPC state pc) :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem frame_test (state : State) (af : Bool) : Frame state (test state af) :=
  ⟨rfl, rfl, fun _ _ => rfl, Sequential.logicalFlags64_preserves ..⟩

theorem frame_load (state : State) (value : BitVec 32) : Frame state (load state value) := by
  refine ⟨rfl, ?_, ?_, addFlags32_preserves ..⟩
  · simp [load, State.writeRegister]
  · intro register allowed
    have different : register ≠ .rax := by intro same; subst register; simp [clobbers] at allowed
    simp [load, State.writeRegister, different]

theorem frame_decrement (state : State) : Frame state (decrement state) := by
  refine ⟨rfl, ?_, ?_, Sequential.decFlags64_preserves ..⟩
  · simp [decrement, State.writeRegister]
  · intro register allowed
    have different : register ≠ .rsi := by intro same; subst register; simp [clobbers] at allowed
    simp [decrement, State.writeRegister, different]

theorem frame_advance (state : State) : Frame state (advance state) := by
  refine ⟨rfl, ?_, ?_, Sequential.addFlags64_preserves ..⟩
  · simp [advance, State.writeRegister]
  · intro register allowed
    have different : register ≠ .rdi := by intro same; subst register; simp [clobbers] at allowed
    simp [advance, State.writeRegister, different]

/-- The checked shape and contiguity give two real update nodes, in either order. -/
theorem update_layout {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    (mode : plan.mode = .pointerCount) :
    ∃ first second, plan.updates = [first, second] ∧
      first.offset = plan.load + 2 ∧
      second.offset = first.offset + first.instruction.length ∧
      plan.back.offset = second.offset + second.instruction.length ∧
      ((first.instruction = .dec64 .rsi ∧ second.instruction = .addImm64 .rdi 4) ∨
        (first.instruction = .addImm64 .rdi 4 ∧ second.instruction = .dec64 .rsi)) := by
  have updatesValid := (Bool.and_eq_true_iff.mp valid.shape).2
  have length : plan.updates.length = 2 := by
    simpa only [mode] using Plan.updates_length updatesValid
  have selected : plan.updates.map Node.instruction = [.dec64 .rsi, .addImm64 .rdi 4] ∨
      plan.updates.map Node.instruction = [.addImm64 .rdi 4, .dec64 .rsi] := by
    exact of_decide_eq_true (by simpa only [Plan.updatesValid, mode] using updatesValid)
  cases updates : plan.updates with
  | nil => simp [updates] at length
  | cons first rest =>
    cases rest with
    | nil => simp [updates] at length
    | cons second rest =>
      cases rest with
      | cons third rest => simp [updates] at length
      | nil =>
        have linear := valid.updates
        simp only [updates, mode, Mode.load, Sequential.Instruction.length] at linear
        obtain ⟨firstPC, tail⟩ := linearFrom_cons linear
        obtain ⟨secondPC, finish⟩ := linearFrom_cons tail
        have backPC : plan.load + 2 + first.instruction.length + second.instruction.length =
            plan.back.offset := of_decide_eq_true finish
        refine ⟨first, second, rfl, firstPC, ?_, ?_, ?_⟩
        · simpa only [firstPC] using secondPC
        · rw [secondPC]; exact backPC.symm
        · simpa only [updates, List.map_cons, List.map_nil, List.cons.injEq,
            and_true] using selected

theorem count_nonzero (values : List (BitVec 32)) (value : BitVec 32)
    (bound : (value :: values).length < 2^64) :
    BitVec.ofNat 64 (value :: values).length ≠ 0 := by
  intro zero
  have natural := congrArg BitVec.toNat zero
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at natural
  simp at natural

theorem count_decrement (values : List (BitVec 32)) (value : BitVec 32) :
    BitVec.ofNat 64 (value :: values).length - 1 = BitVec.ofNat 64 values.length := by
  simp only [List.length_cons, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

end EDSL.Sum32.PointerProof
