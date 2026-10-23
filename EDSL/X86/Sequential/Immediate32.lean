/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- The unsigned representation of an imm8 sign-extended to width32, stated
without a bitvector extension operation on the right-hand side. -/
theorem signExtend8_toNat32 (immediate : Byte) :
    (immediate.signExtend 32).toNat =
      if immediate.toNat < 128 then immediate.toNat else 2^32 - 256 + immediate.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
  by_cases nonnegative : immediate.toNat < 128
  · have notHigh : ¬128 ≤ immediate.toNat := by omega
    simp [BitVec.msb_eq_decide, nonnegative, notHigh]
  · have high : 128 ≤ immediate.toNat := by omega
    simp [BitVec.msb_eq_decide, nonnegative, high, Nat.add_comm]

theorem execute_subImm32 (state : State) (destination : Register) (immediate : Byte)
    (prefixed af : Bool) :
    execute state (.subImm32 destination immediate prefixed) af =
      .ok ⟨.next { state.writeRegister destination
          ((((state.registers destination).setWidth 32) - immediate.signExtend 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.subImm32 destination immediate prefixed).length
        flags := cmpFlags32 state.flags ((state.registers destination).setWidth 32)
          (immediate.signExtend 32) }, []⟩ := rfl

theorem execute_cmpImm32 (state : State) (left : Register) (immediate : Byte)
    (prefixed af : Bool) :
    execute state (.cmpImm32 left immediate prefixed) af =
      .ok ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpImm32 left immediate prefixed).length
        flags := cmpFlags32 state.flags ((state.registers left).setWidth 32)
          (immediate.signExtend 32) }, []⟩ := rfl

theorem step_subImm32 {state : State} {destination : Register} {immediate : Byte} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.subImm32 destination immediate prefixed)) (af : Bool) :
    step af state = execute state (.subImm32 destination immediate prefixed) af :=
  step_eq_execute af decoded

theorem step_cmpImm32 {state : State} {left : Register} {immediate : Byte} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.cmpImm32 left immediate prefixed)) (af : Bool) :
    step af state = execute state (.cmpImm32 left immediate prefixed) af :=
  step_eq_execute af decoded

/-- Width32 modular subtraction, destination zero extension, every other GPR
and the complete memory/permission frame, for arbitrary prestate high halves.
The Nat operand is the signed byte's width32 unsigned representative. -/
theorem execute_subImm32_context (state : State) (destination : Register) (immediate : Byte)
    (prefixed af : Bool) :
    ∃ final, execute state (.subImm32 destination immediate prefixed) af = .ok ⟨.next final, []⟩ ∧
      (final.registers destination).toNat =
        (2^32 - (if immediate.toNat < 128 then immediate.toNat
          else 2^32 - 256 + immediate.toNat) + (state.registers destination).toNat % 2^32) % 2^32 ∧
      (final.registers destination).toNat < 2^32 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = cmpFlags32 state.flags ((state.registers destination).setWidth 32)
        (immediate.signExtend 32) ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, cmpFlags32_preserves .., rfl⟩
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), BitVec.toNat_sub,
      signExtend8_toNat32, BitVec.toNat_setWidth]
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    exact (((state.registers destination).setWidth 32) - immediate.signExtend 32).isLt
  · intro register other
    simp [State.writeRegister, other]

/-- CMP preserves the entire register file, including its arbitrary upper
halves, RAM and permissions. Only the six subtraction flags and RIP change. -/
theorem execute_cmpImm32_context (state : State) (left : Register) (immediate : Byte)
    (prefixed af : Bool) :
    ∃ final, execute state (.cmpImm32 left immediate prefixed) af = .ok ⟨.next final, []⟩ ∧
      final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags = cmpFlags32 state.flags ((state.registers left).setWidth 32)
        (immediate.signExtend 32) ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) :=
  ⟨_, rfl, rfl, rfl, rfl, cmpFlags32_preserves .., rfl⟩

/-- Signed modular result uses the mathematical signed byte, without
interpreting the sign-extended immediate as an unsigned positive integer. -/
theorem execute_subImm32_signed {state final : State} {destination : Register}
    {immediate : Byte} {prefixed af : Bool} {reads : List Read}
    (success : execute state (.subImm32 destination immediate prefixed) af = .ok ⟨.next final, reads⟩) :
    ((final.registers destination).setWidth 32).toInt =
      (((state.registers destination).setWidth 32).toInt - immediate.toInt).bmod (2^32) := by
  cases success
  simp only [State.writeRegister, ↓reduceIte,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
    BitVec.toInt_sub, BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32)]

/-- Complete defined arithmetic flags: unsigned borrow, low-byte parity,
nibble borrow, zero, sign and mathematical signed overflow at width32. -/
theorem execute_subImm32_flags {state final : State} {destination : Register}
    {immediate : Byte} {prefixed af : Bool} {reads : List Read}
    (success : execute state (.subImm32 destination immediate prefixed) af = .ok ⟨.next final, reads⟩) :
    let left := (state.registers destination).setWidth 32
    let right := immediate.signExtend 32
    (final.flags.getLsbD 0 = true ↔ left.toNat < right.toNat) ∧
    (final.flags.getLsbD 2 = evenParity ((left - right).setWidth 8)) ∧
    (final.flags.getLsbD 4 = true ↔ left.toNat % 16 < right.toNat % 16) ∧
    (final.flags.getLsbD 6 = (left == right)) ∧
    (final.flags.getLsbD 7 = (left - right).msb) ∧
    (final.flags.getLsbD 11 = true ↔
      left.toInt - immediate.toInt < -(2^31 : Int) ∨ 2^31 ≤ left.toInt - immediate.toInt) := by
  cases success
  refine ⟨cmpFlags32_borrow .., (cmpFlags32_bits ..).2.1, cmpFlags32_auxiliary ..,
    cmpFlags32_zero .., (cmpFlags32_bits ..).2.2.2.2.1, ?_⟩
  simpa only [BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32)] using
    cmpFlags32_overflow state.flags ((state.registers destination).setWidth 32) (immediate.signExtend 32)

theorem execute_cmpImm32_flags {state final : State} {left : Register}
    {immediate : Byte} {prefixed af : Bool} {reads : List Read}
    (success : execute state (.cmpImm32 left immediate prefixed) af = .ok ⟨.next final, reads⟩) :
    let value := (state.registers left).setWidth 32
    let right := immediate.signExtend 32
    (final.flags.getLsbD 0 = true ↔ value.toNat < right.toNat) ∧
    (final.flags.getLsbD 2 = evenParity ((value - right).setWidth 8)) ∧
    (final.flags.getLsbD 4 = true ↔ value.toNat % 16 < right.toNat % 16) ∧
    (final.flags.getLsbD 6 = (value == right)) ∧
    (final.flags.getLsbD 7 = (value - right).msb) ∧
    (final.flags.getLsbD 11 = true ↔
      value.toInt - immediate.toInt < -(2^31 : Int) ∨ 2^31 ≤ value.toInt - immediate.toInt) := by
  cases success
  refine ⟨cmpFlags32_borrow .., (cmpFlags32_bits ..).2.1, cmpFlags32_auxiliary ..,
    cmpFlags32_zero .., (cmpFlags32_bits ..).2.2.2.2.1, ?_⟩
  simpa only [BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32)] using
    cmpFlags32_overflow state.flags ((state.registers left).setWidth 32) (immediate.signExtend 32)

theorem execute_subImm32_choice_independent (state : State) (destination : Register)
    (immediate : Byte) (prefixed left right : Bool) :
    execute state (.subImm32 destination immediate prefixed) left =
      execute state (.subImm32 destination immediate prefixed) right := rfl

theorem execute_cmpImm32_choice_independent (state : State) (operand : Register)
    (immediate : Byte) (prefixed left right : Bool) :
    execute state (.cmpImm32 operand immediate prefixed) left =
      execute state (.cmpImm32 operand immediate prefixed) right := rfl

end EDSL.X86.Sequential
