/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Flags
import EDSL.X86.Sequential.FlagChoices
import EDSL.WordMath.Multiplication

set_option autoImplicit false
set_option warningAsError true

/-!
Pure full64 two-operand signed multiplication infrastructure. The destination
receives the low64 product; CF and OF report signed overflow. PF/AF/ZF/SF
are independent choices, including for zero products and products that fit.

The flag contract follows Intel SDM 253666-082US (December 2023), PDF
pages 610–612, two-operand REX.W IMUL. The state transformer advances RIP
by four bytes without fetching or decoding an instruction. It establishes
no opcode support, prefix/LOCK validation, or hardware correspondence.
-/

namespace EDSL.X86.Sequential

/-- CF and OF are the same signed-overflow bit. The other four arithmetic
status bits are independently undefined; all remaining flags are retained. -/
def imulFlags64 (old left right : Word) (choices : FlagChoices) : Word :=
  let signedOverflow := left.smulOverflow right
  statusFlags old signedOverflow choices.pf choices.af choices.zf choices.sf signedOverflow

theorem imulFlags64_bits (old left right : Word) (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 0 = left.smulOverflow right ∧
    (imulFlags64 old left right choices).getLsbD 2 = choices.pf ∧
    (imulFlags64 old left right choices).getLsbD 4 = choices.af ∧
    (imulFlags64 old left right choices).getLsbD 6 = choices.zf ∧
    (imulFlags64 old left right choices).getLsbD 7 = choices.sf ∧
    (imulFlags64 old left right choices).getLsbD 11 = left.smulOverflow right :=
  statusFlags_bits ..

theorem imulFlags64_preserves (old left right : Word) (choices : FlagChoices) :
    imulFlags64 old left right choices &&& ~~~arithmeticFlagMask =
      old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem imulFlags64_carry_eq_overflow (old left right : Word) (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 0 =
      (imulFlags64 old left right choices).getLsbD 11 := by
  have bits := imulFlags64_bits old left right choices
  exact bits.1.trans bits.2.2.2.2.2.symm

/-- CF detects failure of the independent signed integer range contract,
not unsigned carry from the low64 multiplication. -/
theorem imulFlags64_carry (old left right : Word) (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 0 = true ↔
      (2^63 : Int) ≤ left.toInt * right.toInt ∨
      left.toInt * right.toInt < -(2^63 : Int) := by
  rw [(imulFlags64_bits old left right choices).1]
  exact EDSL.WordMath.smulOverflow_eq_true_iff left right

theorem imulFlags64_overflow (old left right : Word) (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 11 = true ↔
      (2^63 : Int) ≤ left.toInt * right.toInt ∨
      left.toInt * right.toInt < -(2^63 : Int) := by
  rw [(imulFlags64_bits old left right choices).2.2.2.2.2]
  exact EDSL.WordMath.smulOverflow_eq_true_iff left right

theorem imulFlags64_carry_clear (old left right : Word) (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 0 = false ↔
      -(2^63 : Int) ≤ left.toInt * right.toInt ∧
      left.toInt * right.toInt < (2^63 : Int) := by
  rw [(imulFlags64_bits old left right choices).1]
  exact EDSL.WordMath.smulOverflow_eq_false_iff left right

theorem imulFlags64_overflow_clear (old left right : Word) (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 11 = false ↔
      -(2^63 : Int) ≤ left.toInt * right.toInt ∧
      left.toInt * right.toInt < (2^63 : Int) := by
  rw [(imulFlags64_bits old left right choices).2.2.2.2.2]
  exact EDSL.WordMath.smulOverflow_eq_false_iff left right

/-- Interpreting the truncated result as a signed integer is exactly the
mathematical comparison made by sign-extending that result. -/
theorem imulFlags64_overflow_iff_truncated_ne (old left right : Word)
    (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 11 = true ↔
      (left * right).toInt ≠ left.toInt * right.toInt := by
  rw [(imulFlags64_bits old left right choices).2.2.2.2.2]
  exact EDSL.WordMath.smulOverflow_eq_true_iff_toInt_mul_ne left right

theorem imulFlags64_overflow_clear_iff_exact (old left right : Word)
    (choices : FlagChoices) :
    (imulFlags64 old left right choices).getLsbD 11 = false ↔
      (left * right).toInt = left.toInt * right.toInt := by
  rw [(imulFlags64_bits old left right choices).2.2.2.2.2]
  exact EDSL.WordMath.smulOverflow_eq_false_iff_toInt_mul left right

/-- Only the four declared undefined bits are consulted. In particular the
CF/OF fields of the choice vector cannot override signed overflow. -/
theorem imulFlags64_eq_of_agreement (old left right : Word) (first second : FlagChoices)
    (agree : FlagChoices.Agreement [.pf, .af, .zf, .sf] first second) :
    imulFlags64 old left right first = imulFlags64 old left right second := by
  have parity : first.pf = second.pf := agree .pf (by simp)
  have auxiliary : first.af = second.af := agree .af (by simp)
  have zero : first.zf = second.zf := agree .zf (by simp)
  have sign : first.sf = second.sf := agree .sf (by simp)
  simp only [imulFlags64, parity, auxiliary, zero, sign]

/-- Every four-bit pattern occurs in the abstract choice domain for these
fixed operands and old flags, with CF/OF fixed. There is no nonzero-product
or overflow premise, and no claim that hardware realizes every pattern. -/
theorem imulFlags64_patterns (old left right : Word) (pf af zf sf : Bool) :
    ∃ choices ∈ FlagChoices.representatives [.pf, .af, .zf, .sf],
      (imulFlags64 old left right choices).getLsbD 0 = left.smulOverflow right ∧
      (imulFlags64 old left right choices).getLsbD 2 = pf ∧
      (imulFlags64 old left right choices).getLsbD 4 = af ∧
      (imulFlags64 old left right choices).getLsbD 6 = zf ∧
      (imulFlags64 old left right choices).getLsbD 7 = sf ∧
      (imulFlags64 old left right choices).getLsbD 11 = left.smulOverflow right := by
  obtain ⟨choices, member, parity, auxiliary, zero, sign⟩ :=
    FlagChoices.four_status_patterns pf af zf sf
  have bits := imulFlags64_bits old left right choices
  exact ⟨choices, member, bits.1, bits.2.1.trans parity, bits.2.2.1.trans auxiliary,
    bits.2.2.2.1.trans zero, bits.2.2.2.2.1.trans sign, bits.2.2.2.2.2⟩

/-- Both full64 operands and the old flags are captured from `state` before
writing the destination, including aliases. This pure transformer uses a
fixed four-byte RIP increment and performs no instruction or operand fetch. -/
def imulReg64State (state : State) (destination source : Register)
    (choices : FlagChoices) : State :=
  let left := state.registers destination
  let right := state.registers source
  { state.writeRegister destination (left * right) with
    rip := state.rip + 4
    flags := imulFlags64 state.flags left right choices }

theorem imulReg64State_destination (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).registers destination =
      state.registers destination * state.registers source := by
  simp [imulReg64State, State.writeRegister]

/-- The result meets a contract defined solely by unbounded natural arithmetic. -/
theorem imulReg64State_modulo (state : State) (destination source : Register)
    (choices : FlagChoices) :
    EDSL.WordMath.MulModulo (state.registers destination) (state.registers source)
      ((imulReg64State state destination source choices).registers destination) := by
  rw [imulReg64State_destination]
  exact EDSL.WordMath.mulModulo_mul _ _

theorem imulReg64State_result (state : State) (destination source : Register)
    (choices : FlagChoices) :
    ((imulReg64State state destination source choices).registers destination).toNat =
      ((state.registers destination).toNat * (state.registers source).toNat) % 2^64 :=
  imulReg64State_modulo state destination source choices

theorem imulReg64State_other_register (state : State) (destination source register : Register)
    (choices : FlagChoices) (different : register ≠ destination) :
    (imulReg64State state destination source choices).registers register =
      state.registers register := by
  simp [imulReg64State, State.writeRegister, different]

/-- Equality retains the complete byte map and both permission maps. -/
theorem imulReg64State_memory (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).memory = state.memory := rfl

theorem imulReg64State_permissions (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).memory.executable = state.memory.executable ∧
    (imulReg64State state destination source choices).memory.writable = state.memory.writable :=
  ⟨rfl, rfl⟩

theorem imulReg64State_flags (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).flags =
      imulFlags64 state.flags (state.registers destination) (state.registers source) choices := rfl

theorem imulReg64State_preserves_flags (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).flags &&& ~~~arithmeticFlagMask =
      state.flags &&& ~~~arithmeticFlagMask :=
  imulFlags64_preserves state.flags (state.registers destination) (state.registers source) choices

theorem imulReg64State_rip (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).rip = state.rip + 4 := rfl

/-- A self-alias squares the old operand, and overflow also uses that old
operand twice rather than reading the newly written destination. -/
theorem imulReg64State_self (state : State) (destination : Register) (choices : FlagChoices) :
    (imulReg64State state destination destination choices).registers destination =
      state.registers destination * state.registers destination ∧
    (imulReg64State state destination destination choices).flags =
      imulFlags64 state.flags (state.registers destination) (state.registers destination) choices :=
  ⟨imulReg64State_destination state destination destination choices, rfl⟩

/-- An independent signed-product comparison for the actual destination.
CF is equal to OF by `imulFlags64_carry_eq_overflow` and the flags equation. -/
theorem imulReg64State_overflow_iff_result_ne (state : State) (destination source : Register)
    (choices : FlagChoices) :
    (imulReg64State state destination source choices).flags.getLsbD 11 = true ↔
      ((imulReg64State state destination source choices).registers destination).toInt ≠
        (state.registers destination).toInt * (state.registers source).toInt := by
  rw [imulReg64State_flags, imulReg64State_destination]
  exact imulFlags64_overflow_iff_truncated_ne state.flags
    (state.registers destination) (state.registers source) choices

theorem imulReg64State_eq_of_agreement (state : State) (destination source : Register)
    (first second : FlagChoices)
    (agree : FlagChoices.Agreement [.pf, .af, .zf, .sf] first second) :
    imulReg64State state destination source first =
      imulReg64State state destination source second := by
  simp only [imulReg64State, imulFlags64_eq_of_agreement state.flags
    (state.registers destination) (state.registers source) first second agree]

end EDSL.X86.Sequential
