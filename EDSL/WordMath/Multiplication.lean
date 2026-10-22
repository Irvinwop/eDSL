/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init

set_option autoImplicit false
set_option warningAsError true

/-!
Word multiplication against unbounded arithmetic. The unsigned contract states
reduction modulo the word size; the signed results describe representability of
the full integer product. These definitions have no instruction, processor flag,
execution, compiler, or operating-system dependencies.

All word widths, including zero, are admitted. At positive widths the signed
bounds are the usual two's-complement interval. The width-zero word has integer
value zero, so the same overflow and exactness statements remain valid there.
-/

namespace EDSL.WordMath

/-- The result is the residue of the unbounded natural product. -/
def MulModulo {width : Nat} (left right result : BitVec width) : Prop :=
  result.toNat = (left.toNat * right.toNat) % 2 ^ width

/-- Word multiplication implements the independent modular-product contract. -/
theorem mulModulo_mul {width : Nat} (left right : BitVec width) :
    MulModulo left right (left * right) :=
  BitVec.toNat_mul left right

/-- A modular product has a unique word result, including at width zero. -/
theorem mulModulo_unique {width : Nat} {left right first second : BitVec width}
    (hfirst : MulModulo left right first)
    (hsecond : MulModulo left right second) : first = second := by
  apply BitVec.eq_of_toNat_eq
  exact hfirst.trans hsecond.symm

/-- Admitting a word under the contract determines its exact value. -/
theorem mulModulo_iff {width : Nat} (left right result : BitVec width) :
    MulModulo left right result ↔ result = left * right := by
  constructor
  · intro h
    exact mulModulo_unique h (mulModulo_mul left right)
  · rintro rfl
    exact mulModulo_mul left right

/-- Existence and uniqueness do not require a positive-width premise. -/
theorem mulModulo_exists_unique {width : Nat} (left right : BitVec width) :
    ∃ result : BitVec width, MulModulo left right result ∧
      ∀ other : BitVec width, MulModulo left right other → other = result :=
  ⟨left * right, mulModulo_mul left right,
    fun _ h => mulModulo_unique h (mulModulo_mul left right)⟩

/-- The full signed integer product lies in the target word's signed range. -/
def SignedMulFits {width : Nat} (left right : BitVec width) : Prop :=
  -(2 ^ (width - 1) : Int) ≤ left.toInt * right.toInt ∧
    left.toInt * right.toInt < (2 ^ (width - 1) : Int)

/-- The overflow bit detects precisely an out-of-range signed product. -/
theorem smulOverflow_eq_true_iff {width : Nat} (left right : BitVec width) :
    left.smulOverflow right = true ↔
      (2 ^ (width - 1) : Int) ≤ left.toInt * right.toInt ∨
      left.toInt * right.toInt < -(2 ^ (width - 1) : Int) := by
  simp only [BitVec.smulOverflow, Bool.or_eq_true, decide_eq_true_eq, ge_iff_le]

/-- Absence of signed overflow is exactly representability of the full product. -/
theorem smulOverflow_eq_false_iff {width : Nat} (left right : BitVec width) :
    left.smulOverflow right = false ↔ SignedMulFits left right := by
  simp only [BitVec.smulOverflow, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, ge_iff_le, SignedMulFits]
  omega

/-- Truncation preserves the signed product exactly iff signed overflow is absent.
The reverse direction follows from the independent bounds of every signed word. -/
theorem smulOverflow_eq_false_iff_toInt_mul {width : Nat}
    (left right : BitVec width) :
    left.smulOverflow right = false ↔
      (left * right).toInt = left.toInt * right.toInt := by
  constructor
  · intro h
    exact BitVec.toInt_mul_of_not_smulOverflow (by simp [h])
  · intro h
    apply (smulOverflow_eq_false_iff left right).mpr
    have lower := BitVec.le_toInt (left * right)
    have upper := BitVec.toInt_lt (x := left * right)
    rw [h] at lower upper
    exact ⟨lower, upper⟩

/-- Equivalent form useful when an instruction writes the truncated word. -/
theorem smulOverflow_eq_true_iff_toInt_mul_ne {width : Nat}
    (left right : BitVec width) :
    left.smulOverflow right = true ↔
      (left * right).toInt ≠ left.toInt * right.toInt := by
  have exactness := smulOverflow_eq_false_iff_toInt_mul left right
  cases h : left.smulOverflow right <;> simp_all

/-- At 64 bits, signed overflow compares the full product to [-2^63, 2^63). -/
theorem smulOverflow64_eq_true_iff (left right : BitVec 64) :
    left.smulOverflow right = true ↔
      9223372036854775808 ≤ left.toInt * right.toInt ∨
      left.toInt * right.toInt < -9223372036854775808 := by
  simpa using smulOverflow_eq_true_iff left right

/-- The exact signed-range contract for 64-bit multiplication. -/
theorem smulOverflow64_eq_false_iff (left right : BitVec 64) :
    left.smulOverflow right = false ↔
      -9223372036854775808 ≤ left.toInt * right.toInt ∧
      left.toInt * right.toInt < 9223372036854775808 := by
  simpa [SignedMulFits] using smulOverflow_eq_false_iff left right

/-- Minus one times one is representable as a signed 64-bit product. -/
theorem signed64_neg_one_mul_one_fits :
    (BitVec.ofInt 64 (-1)).smulOverflow (1 : BitVec 64) = false := by
  decide

/-- Doubling the signed maximum overflows despite fitting the unsigned range. -/
theorem signed64_max_mul_two_overflows :
    (BitVec.intMax 64).smulOverflow (2 : BitVec 64) = true ∧
      (BitVec.intMax 64).umulOverflow (2 : BitVec 64) = false := by
  decide

/-- The positive magnitude of the signed minimum is not signed-representable. -/
theorem signed64_min_mul_neg_one_overflows :
    (BitVec.intMin 64).smulOverflow (BitVec.ofInt 64 (-1)) = true := by
  decide

/-- Signed and unsigned overflow cannot be substituted for one another. -/
theorem signed64_neg_one_mul_two_distinguishes_unsigned :
    (BitVec.ofInt 64 (-1)).smulOverflow (2 : BitVec 64) = false ∧
      (BitVec.ofInt 64 (-1)).umulOverflow (2 : BitVec 64) = true := by
  decide

end EDSL.WordMath
