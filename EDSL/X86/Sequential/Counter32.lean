/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- Register counter addition uses the old low32 value and a signed immediate.
The complete destination is zero extended; this is not a full64 addition. -/
theorem execute_addImm32 (state : State) (destination : Register) (immediate : Byte)
    (prefixed af : Bool) :
    execute state (.addImm32 destination immediate prefixed) af =
      .ok ⟨.next { state.writeRegister destination
          ((((state.registers destination).setWidth 32) + immediate.signExtend 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.addImm32 destination immediate prefixed).length
        flags := addFlags32 state.flags ((state.registers destination).setWidth 32)
          (immediate.signExtend 32) }, []⟩ := rfl

theorem execute_inc32 (state : State) (destination : Register) (prefixed af : Bool) :
    execute state (.inc32 destination prefixed) af =
      .ok ⟨.next { state.writeRegister destination
          ((((state.registers destination).setWidth 32) + 1).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.inc32 destination prefixed).length
        flags := incFlags32 state.flags ((state.registers destination).setWidth 32) }, []⟩ := rfl

theorem step_addImm32 {state : State} {destination : Register} {immediate : Byte} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.addImm32 destination immediate prefixed)) (af : Bool) :
    step af state = execute state (.addImm32 destination immediate prefixed) af :=
  step_eq_execute af decoded

theorem step_inc32 {state : State} {destination : Register} {prefixed : Bool}
    (decoded : decodeAt state = .ok (.inc32 destination prefixed)) (af : Bool) :
    step af state = execute state (.inc32 destination prefixed) af := step_eq_execute af decoded

/-- Entire memory/permission maps and all nondestination GPRs survive, including
RSP and upper-bank destinations. No implicit ABI promise is made for RSP. -/
theorem execute_addImm32_context (state : State) (destination : Register) (immediate : Byte)
    (prefixed af : Bool) :
    ∃ final, execute state (.addImm32 destination immediate prefixed) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination =
        (((state.registers destination).setWidth 32 + immediate.signExtend 32).setWidth 64) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = addFlags32 state.flags ((state.registers destination).setWidth 32)
        (immediate.signExtend 32) ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.addImm32 destination immediate prefixed).length := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

theorem execute_inc32_context (state : State) (destination : Register) (prefixed af : Bool) :
    ∃ final, execute state (.inc32 destination prefixed) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = (((state.registers destination).setWidth 32 + 1).setWidth 64) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = incFlags32 state.flags ((state.registers destination).setWidth 32) ∧
      final.flags.getLsbD 0 = state.flags.getLsbD 0 ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.inc32 destination prefixed).length := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, incFlags32_carry .., rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- The defined INC overflow flag is mathematical signed overflow at width32. -/
theorem incFlags32_overflow (old : Word) (value : BitVec 32) :
    (incFlags32 old value).getLsbD 11 = true ↔
      value.toInt + 1 < -(2^31 : Int) ∨ 2^31 ≤ value.toInt + 1 := by
  rw [(incFlags32_bits ..).2.2.2.2.2]
  simp [BitVec.saddOverflow, or_comm]

theorem incFlags32_auxiliary (old : Word) (value : BitVec 32) :
    (incFlags32 old value).getLsbD 4 = true ↔ value.toNat % 16 = 15 := by
  rw [(incFlags32_bits ..).2.2.1]
  change decide (16 ≤ value.toNat % 16 + 1) = true ↔ value.toNat % 16 = 15
  rw [decide_eq_true_eq]
  have small := Nat.mod_lt value.toNat (by decide : 0 < 16)
  omega

/-- Bounded natural counters refine width32 increment without an input high-half
restriction. This links independent Nat loop invariants to both ADD32(1)/INC32. -/
theorem counter32_increment_nat (value : Word) (count : Nat)
    (matching : (value.setWidth 32).toNat = count) (bound : count + 1 < 2^32) :
    (((value.setWidth 32 + 1).setWidth 64).toNat) = count + 1 := by
  have addition : (value.setWidth 32 + 1).toNat = count + 1 := by
    rw [BitVec.toNat_add, matching]
    change (count + 1) % 2^32 = count + 1
    exact Nat.mod_eq_of_lt bound
  rw [BitVec.toNat_setWidth, addition, Nat.mod_eq_of_lt]
  omega

/-- Upper32 clearing is observable independently of the arithmetic result. -/
theorem execute_inc32_zero_extended {state final : State} {destination : Register}
    {prefixed af : Bool} {reads : List Read}
    (actual : execute state (.inc32 destination prefixed) af = .ok ⟨.next final, reads⟩) :
    (final.registers destination).toNat < 2^32 := by
  cases actual
  simp only [State.writeRegister, ↓reduceIte]
  rw [BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le ..) (BitVec.isLt _)

theorem execute_addImm32_zero_extended {state final : State} {destination : Register}
    {immediate : Byte} {prefixed af : Bool} {reads : List Read}
    (actual : execute state (.addImm32 destination immediate prefixed) af = .ok ⟨.next final, reads⟩) :
    (final.registers destination).toNat < 2^32 := by
  cases actual
  simp only [State.writeRegister, ↓reduceIte]
  rw [BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le ..) (BitVec.isLt _)

theorem execute_addImm32_af_independent (state : State) (destination : Register)
    (immediate : Byte) (prefixed left right : Bool) :
    execute state (.addImm32 destination immediate prefixed) left =
      execute state (.addImm32 destination immediate prefixed) right := rfl

theorem execute_inc32_af_independent (state : State) (destination : Register)
    (prefixed left right : Bool) :
    execute state (.inc32 destination prefixed) left = execute state (.inc32 destination prefixed) right := rfl

end EDSL.X86.Sequential
