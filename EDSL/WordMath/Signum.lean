/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.Scalar

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Integer signum and 32-bit word representations. The relation is stated solely
by the order of the input integer. The algebraic implementations below have no
machine-state, decoder, compiler, operating-system or execution dependencies.
-/

namespace EDSL.WordMath

/-- The output is -1, 0 or 1 according to the input's integer order. -/
def Signum (input result : Int) : Prop :=
  (input < 0 → result = -1) ∧
    (input = 0 → result = 0) ∧
    (0 < input → result = 1)

theorem signum_unique {input first second : Int}
    (left : Signum input first) (right : Signum input second) : first = second := by
  by_cases negative : input < 0
  · exact (left.1 negative).trans (right.1 negative).symm
  · by_cases zero : input = 0
    · exact (left.2.1 zero).trans (right.2.1 zero).symm
    · have positive : 0 < input := by omega
      exact (left.2.2 positive).trans (right.2.2 positive).symm

theorem signum_bounds {input result : Int} (satisfies : Signum input result) :
    -1 ≤ result ∧ result ≤ 1 := by
  by_cases negative : input < 0
  · rw [satisfies.1 negative]
    omega
  · by_cases zero : input = 0
    · rw [satisfies.2.1 zero]
      omega
    · rw [satisfies.2.2 (by omega)]
      omega

/-- The canonical signed-low32 representation; negative results are all ones. -/
def signum32 (input : BitVec 32) : BitVec 32 :=
  if input.toInt < 0 then BitVec.allOnes 32
  else if input.toInt = 0 then 0 else 1

theorem signum32_toInt (input : BitVec 32) :
    (signum32 input).toInt =
      if input.toInt < 0 then -1 else if input.toInt = 0 then 0 else 1 := by
  by_cases negative : input.toInt < 0
  · simp [signum32, negative]
  · by_cases zero : input.toInt = 0 <;> simp [signum32, negative, zero]

theorem signum32_contract (input : BitVec 32) :
    Signum input.toInt (signum32 input).toInt := by
  rw [Signum, signum32_toInt]
  refine ⟨?_, ?_, ?_⟩
  · intro negative
    simp [negative]
  · intro zero
    simp [zero]
  · intro positive
    simp [show ¬ input.toInt < 0 by omega, show input.toInt ≠ 0 by omega]

theorem signum32_iff (input result : BitVec 32) :
    Signum input.toInt result.toInt ↔ result = signum32 input := by
  constructor
  · intro satisfies
    exact BitVec.eq_of_toInt_eq (signum_unique satisfies (signum32_contract input))
  · rintro rfl
    exact signum32_contract input

/-- Moving the last bit to bit zero yields exactly the unsigned sign bit. -/
theorem ushiftRight31_eq_signBit (input : BitVec 32) :
    input >>> 31 = if input.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases sign : input.msb with
  | false =>
    have upper : input.toNat < 2147483648 := BitVec.toNat_lt_of_msb_false sign
    simp only [Bool.false_eq_true, ↓reduceIte,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change input.toNat / 2147483648 = 0
    omega
  | true =>
    have lower : 2147483648 ≤ input.toNat := BitVec.le_toNat_of_msb_true sign
    have upper : input.toNat < 4294967296 := input.isLt
    simp only [↓reduceIte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    change input.toNat / 2147483648 = 1
    omega

/-- The same sign-bit law stated independently by signed integer order. -/
theorem ushiftRight31_eq_negative (input : BitVec 32) :
    input >>> 31 = if input.toInt < 0 then 1 else 0 := by
  rw [ushiftRight31_eq_signBit, sign32]
  simp

/-- Arithmetic right-shift by the last bit replicates precisely the sign bit. -/
theorem sshiftRight31_eq_signMask (input : BitVec 32) :
    input.sshiftRight 31 = if input.msb then BitVec.allOnes 32 else 0 := by
  cases sign : input.msb with
  | false =>
    rw [BitVec.sshiftRight_eq_of_msb_false sign, ushiftRight31_eq_signBit]
    simp [sign]
  | true =>
    rw [BitVec.sshiftRight_eq_of_msb_true sign, ushiftRight31_eq_signBit]
    simp [sign]

/-- Signed order, including INT32_MIN, determines the entire sign mask. -/
theorem sshiftRight31_eq_negative (input : BitVec 32) :
    input.sshiftRight 31 = if input.toInt < 0 then BitVec.allOnes 32 else 0 := by
  rw [sshiftRight31_eq_signMask, sign32]
  simp

/-- Positive-indicator minus unsigned sign-bit is the canonical signum word. -/
theorem positive_sub_signBit_eq_signum32 (input : BitVec 32) :
    (if 0 < input.toInt then (1 : BitVec 32) else 0) - (input >>> 31) =
      signum32 input := by
  rw [ushiftRight31_eq_negative]
  by_cases negative : input.toInt < 0
  · simp [signum32, negative, show ¬ 0 < input.toInt by omega,
      BitVec.neg_one_eq_allOnes]
  · by_cases zero : input.toInt = 0
    · simp [signum32, zero]
    · simp [signum32, negative, zero, show 0 < input.toInt by omega]

/-- Nonzero-indicator OR signed sign-mask is the same canonical word. -/
theorem nonzero_or_signMask_eq_signum32 (input : BitVec 32) :
    (if input.toInt ≠ 0 then (1 : BitVec 32) else 0) ||| input.sshiftRight 31 =
      signum32 input := by
  rw [sshiftRight31_eq_negative]
  by_cases negative : input.toInt < 0
  · simp [signum32, negative, show input.toInt ≠ 0 by omega]
  · by_cases zero : input.toInt = 0 <;> simp [signum32, negative, zero]

/-- The Boolean-difference expression satisfies the independent order contract. -/
theorem positive_sub_signBit_contract (input : BitVec 32) :
    Signum input.toInt
      ((if 0 < input.toInt then (1 : BitVec 32) else 0) - (input >>> 31)).toInt := by
  rw [positive_sub_signBit_eq_signum32]
  exact signum32_contract input

/-- The Boolean-OR expression satisfies the same contract for every input. -/
theorem nonzero_or_signMask_contract (input : BitVec 32) :
    Signum input.toInt
      ((if input.toInt ≠ 0 then (1 : BitVec 32) else 0) |||
        input.sshiftRight 31).toInt := by
  rw [nonzero_or_signMask_eq_signum32]
  exact signum32_contract input

end EDSL.WordMath
