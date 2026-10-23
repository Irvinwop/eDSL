/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Flags
import EDSL.X86.Sequential.FlagChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Pure low32 right-shift semantics, separate from decoding and execution. The
masked count is explicit; SAR uses signed floor division, including negatives.
AF is undefined for every nonzero count and OF is independently undefined for
counts greater than one. No choice changes a defined result or status flag.

Intel SDM Volume 2B, SAL/SAR/SHL/SHR, Flags Affected:
https://cdrdv2-public.intel.com/782151/253667-sdm-vol-2b.pdf
This transformer establishes no decoder or physical-machine correspondence.
-/

namespace EDSL.X86.Sequential

/-- A low32 shift masks the immediate to five bits. -/
def shiftCount32 (immediate : Byte) : Nat := immediate.toNat % 32

theorem shiftCount32_lt (immediate : Byte) : shiftCount32 immediate < 32 :=
  Nat.mod_lt _ (by decide)

/-- Logical right shift fills with zero; arithmetic right shift fills with
the old sign. The count parameter remains general for reuse by other encodings. -/
def shiftRightResult32 (operation : ShiftRightOp) (value : BitVec 32) (count : Nat) :
    BitVec 32 :=
  match operation with
  | .logical => value >>> count
  | .arithmetic => value.sshiftRight count

theorem shiftRightResult32_logical_toNat (value : BitVec 32) (count : Nat) :
    (shiftRightResult32 .logical value count).toNat = value.toNat / 2^count := by
  simp only [shiftRightResult32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Signed floor division, rather than truncation toward zero, characterizes
SAR for arbitrary counts and inputs, including the minimum signed value. -/
theorem shiftRightResult32_arithmetic_toInt (value : BitVec 32) (count : Nat) :
    (shiftRightResult32 .arithmetic value count).toInt = value.toInt / 2^count := by
  change (value.sshiftRight count).toInt = _
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  exact congrArg (fun denominator : Int => value.toInt / denominator) (Int.natCast_pow 2 count)

/-- The zero case has no undefined flags. It is kept total here even though
the first decoder scope deliberately rejects effective count zero. -/
def shiftRightUndefinedFlags32 (immediate : Byte) : List StatusFlag :=
  if shiftCount32 immediate = 0 then []
  else if shiftCount32 immediate = 1 then [.af] else [.af, .of]

/-- Count-one SHR reports the old sign in OF, while count-one SAR clears OF.
Only larger counts consult the independent OF choice. -/
def shiftRightOF32 (operation : ShiftRightOp) (value : BitVec 32) (count : Nat)
    (choices : FlagChoices) : Bool :=
  if count = 1 then
    match operation with
    | .logical => value.msb
    | .arithmetic => false
  else choices.of

/-- Every nonarithmetic flag survives. The carry bit is the last shifted-out
old bit; parity, zero and sign are defined by the low32 result. -/
def shiftRightFlags32 (old : Word) (operation : ShiftRightOp) (value : BitVec 32)
    (immediate : Byte) (choices : FlagChoices) : Word :=
  let count := shiftCount32 immediate
  if count = 0 then old else
    let result := shiftRightResult32 operation value count
    statusFlags old (value.getLsbD (count - 1)) (evenParity (result.setWidth 8)) choices.af
      (result == 0) result.msb (shiftRightOF32 operation value count choices)

theorem shiftRightFlags32_bits (old : Word) (operation : ShiftRightOp) (value : BitVec 32)
    (immediate : Byte) (choices : FlagChoices) (nonzero : shiftCount32 immediate ≠ 0) :
    (shiftRightFlags32 old operation value immediate choices).getLsbD 0 =
      value.getLsbD (shiftCount32 immediate - 1) ∧
    (shiftRightFlags32 old operation value immediate choices).getLsbD 2 =
      evenParity ((shiftRightResult32 operation value (shiftCount32 immediate)).setWidth 8) ∧
    (shiftRightFlags32 old operation value immediate choices).getLsbD 4 = choices.af ∧
    (shiftRightFlags32 old operation value immediate choices).getLsbD 6 =
      (shiftRightResult32 operation value (shiftCount32 immediate) == 0) ∧
    (shiftRightFlags32 old operation value immediate choices).getLsbD 7 =
      (shiftRightResult32 operation value (shiftCount32 immediate)).msb ∧
    (shiftRightFlags32 old operation value immediate choices).getLsbD 11 =
      shiftRightOF32 operation value (shiftCount32 immediate) choices := by
  simpa only [shiftRightFlags32, nonzero, ↓reduceIte] using
    statusFlags_bits old (value.getLsbD (shiftCount32 immediate - 1))
      (evenParity ((shiftRightResult32 operation value (shiftCount32 immediate)).setWidth 8))
      choices.af (shiftRightResult32 operation value (shiftCount32 immediate) == 0)
      (shiftRightResult32 operation value (shiftCount32 immediate)).msb
      (shiftRightOF32 operation value (shiftCount32 immediate) choices)

theorem shiftRightFlags32_preserves (old : Word) (operation : ShiftRightOp)
    (value : BitVec 32) (immediate : Byte) (choices : FlagChoices) :
    shiftRightFlags32 old operation value immediate choices &&& ~~~arithmeticFlagMask =
      old &&& ~~~arithmeticFlagMask := by
  dsimp only [shiftRightFlags32]
  split
  · rfl
  · exact statusFlags_preserves ..

theorem shiftRightFlags32_eq_of_agreement (old : Word) (operation : ShiftRightOp)
    (value : BitVec 32) (immediate : Byte) (first second : FlagChoices)
    (agree : FlagChoices.Agreement (shiftRightUndefinedFlags32 immediate) first second) :
    shiftRightFlags32 old operation value immediate first =
      shiftRightFlags32 old operation value immediate second := by
  by_cases zero : shiftCount32 immediate = 0
  · simp only [shiftRightFlags32, zero, ↓reduceIte]
  · have auxiliary : first.af = second.af := agree .af (by
      by_cases single : shiftCount32 immediate = 1 <;>
        simp [shiftRightUndefinedFlags32, zero, single])
    by_cases single : shiftCount32 immediate = 1
    · simp only [shiftRightFlags32, ↓reduceIte, shiftRightOF32, single, auxiliary]
    · have overflow : first.of = second.of := agree .of (by
        simp [shiftRightUndefinedFlags32, zero, single])
      simp only [shiftRightFlags32, zero, ↓reduceIte, shiftRightOF32, single,
        auxiliary, overflow]

/-- For counts greater than one all four AF/OF combinations occur, while
holding the operand and incoming flags fixed. The model does not predict
which undefined pattern any physical processor will produce. -/
theorem shiftRightFlags32_patterns (old : Word) (operation : ShiftRightOp)
    (value : BitVec 32) (immediate : Byte) (large : 1 < shiftCount32 immediate)
    (af of : Bool) :
    ∃ choices ∈ FlagChoices.representatives (shiftRightUndefinedFlags32 immediate),
      (shiftRightFlags32 old operation value immediate choices).getLsbD 4 = af ∧
      (shiftRightFlags32 old operation value immediate choices).getLsbD 11 = of := by
  have nonzero : shiftCount32 immediate ≠ 0 := by omega
  have notSingle : shiftCount32 immediate ≠ 1 := by omega
  let desired : FlagChoices := ⟨false, false, af, false, false, of⟩
  obtain ⟨choices, member, agree⟩ :=
    FlagChoices.representatives_complete (shiftRightUndefinedFlags32 immediate) desired
  have auxiliary : choices.af = af :=
    (agree .af (by simp [shiftRightUndefinedFlags32, nonzero, notSingle])).symm
  have overflow : choices.of = of :=
    (agree .of (by simp [shiftRightUndefinedFlags32, nonzero, notSingle])).symm
  have bits := shiftRightFlags32_bits old operation value immediate choices nonzero
  refine ⟨choices, member, bits.2.2.1.trans auxiliary, ?_⟩
  simpa only [shiftRightOF32, notSingle, ↓reduceIte, overflow] using bits.2.2.2.2.2

/-- The operand and old flags are captured before writing. Nonzero counts
zero-extend the low32 result into the entire destination, even RSP. Effective
zero preserves the entire destination and flags. This total pure transformer
performs no instruction or operand fetch and advances by the encoded length. -/
def shiftRightImm32State (state : State) (operation : ShiftRightOp) (destination : Register)
    (immediate : Byte) (prefixed : Bool) (choices : FlagChoices) : State :=
  let value := (state.registers destination).setWidth 32
  let count := shiftCount32 immediate
  let result := if count = 0 then state.registers destination
    else (shiftRightResult32 operation value count).setWidth 64
  { state.writeRegister destination result with
    rip := state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3)
    flags := shiftRightFlags32 state.flags operation value immediate choices }

theorem shiftRightImm32State_destination (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices)
    (nonzero : shiftCount32 immediate ≠ 0) :
    (shiftRightImm32State state operation destination immediate prefixed choices).registers
      destination =
      (shiftRightResult32 operation ((state.registers destination).setWidth 32)
        (shiftCount32 immediate)).setWidth 64 := by
  simp [shiftRightImm32State, State.writeRegister, nonzero]

/-- A low32 destination write always clears the entire high half, regardless
of the incoming high bits or choice vector. -/
theorem shiftRightImm32State_zero_extends (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices)
    (nonzero : shiftCount32 immediate ≠ 0) :
    ((shiftRightImm32State state operation destination immediate prefixed choices).registers
      destination).toNat < 2^32 := by
  rw [shiftRightImm32State_destination state operation destination immediate prefixed choices nonzero,
    BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  exact (shiftRightResult32 operation ((state.registers destination).setWidth 32)
    (shiftCount32 immediate)).isLt

/-- The actual full destination of SHR satisfies unsigned division of the
old low32 value, not of the incoming full64 register. -/
theorem shiftRightImm32State_logical_division (state : State) (destination : Register)
    (immediate : Byte) (prefixed : Bool) (choices : FlagChoices)
    (nonzero : shiftCount32 immediate ≠ 0) :
    ((shiftRightImm32State state .logical destination immediate prefixed choices).registers
      destination).toNat =
      ((state.registers destination).toNat % 2^32) / 2^(shiftCount32 immediate) := by
  rw [shiftRightImm32State_destination state .logical destination immediate prefixed choices nonzero,
    BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), shiftRightResult32_logical_toNat,
    BitVec.toNat_setWidth]

/-- Interpreting the actual low32 SAR destination as signed gives floor
rather than truncating division. The complete register remains zero-extended. -/
theorem shiftRightImm32State_arithmetic_division (state : State) (destination : Register)
    (immediate : Byte) (prefixed : Bool) (choices : FlagChoices)
    (nonzero : shiftCount32 immediate ≠ 0) :
    (((shiftRightImm32State state .arithmetic destination immediate prefixed choices).registers
      destination).setWidth 32).toInt =
      ((state.registers destination).setWidth 32).toInt / 2^(shiftCount32 immediate) := by
  rw [shiftRightImm32State_destination state .arithmetic destination immediate prefixed choices nonzero]
  simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    BitVec.setWidth_eq, shiftRightResult32_arithmetic_toInt]

theorem shiftRightImm32State_other_register (state : State) (operation : ShiftRightOp)
    (destination register : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices)
    (different : register ≠ destination) :
    (shiftRightImm32State state operation destination immediate prefixed choices).registers
      register = state.registers register := by
  simp [shiftRightImm32State, State.writeRegister, different]

/-- Equality includes the full byte map and all permission maps. -/
theorem shiftRightImm32State_memory (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices) :
    (shiftRightImm32State state operation destination immediate prefixed choices).memory =
      state.memory := rfl

theorem shiftRightImm32State_flags (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices) :
    (shiftRightImm32State state operation destination immediate prefixed choices).flags =
      shiftRightFlags32 state.flags operation ((state.registers destination).setWidth 32)
        immediate choices := rfl

theorem shiftRightImm32State_preserves_flags (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices) :
    (shiftRightImm32State state operation destination immediate prefixed choices).flags &&&
      ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask :=
  shiftRightFlags32_preserves ..

theorem shiftRightImm32State_rip (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (choices : FlagChoices) :
    (shiftRightImm32State state operation destination immediate prefixed choices).rip =
      state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) := rfl

theorem shiftRightImm32State_eq_of_agreement (state : State) (operation : ShiftRightOp)
    (destination : Register) (immediate : Byte) (prefixed : Bool) (first second : FlagChoices)
    (agree : FlagChoices.Agreement (shiftRightUndefinedFlags32 immediate) first second) :
    shiftRightImm32State state operation destination immediate prefixed first =
      shiftRightImm32State state operation destination immediate prefixed second := by
  simp only [shiftRightImm32State, shiftRightFlags32_eq_of_agreement state.flags operation
    ((state.registers destination).setWidth 32) immediate first second agree]

end EDSL.X86.Sequential
