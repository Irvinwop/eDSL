/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init

set_option autoImplicit false
set_option warningAsError true

/-!
Unsigned floor averages for arbitrary bitvector widths. The contract uses the
unbounded natural sum, so an overflowing word sum is admitted. Width zero is
also admitted: its only word has natural value zero.

These results depend only on `Init`, with no machine, instruction, compiler,
execution, resource, or corpus assumptions.
-/

namespace EDSL.WordMath

/-- Natural addition separates common set bits from differing bits, without
any truncation of the sum or of the doubled common bits. -/
theorem nat_add_eq_twice_and_add_xor (a b : Nat) :
    a + b = 2 * (a &&& b) + (a ^^^ b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · simp [ha]
    have half := ih (a / 2)
      (Nat.div_lt_self (Nat.zero_lt_of_ne_zero ha) (by decide)) (b / 2)
    rw [← Nat.and_div_two, ← Nat.xor_div_two] at half
    have parity : a % 2 + b % 2 =
        2 * ((a &&& b) % 2) + (a ^^^ b) % 2 := by
      have := Nat.mod_lt a (by decide : 0 < 2)
      have := Nat.mod_lt b (by decide : 0 < 2)
      have := Nat.mod_lt (a &&& b) (by decide : 0 < 2)
      have := Nat.mod_lt (a ^^^ b) (by decide : 0 < 2)
      have := Nat.and_mod_two_eq_one (a := a) (b := b)
      have := Nat.xor_mod_two_eq_one (a := a) (b := b)
      omega
    omega

/-- Exact natural identity for words, including when their word sum overflows.
The multiplication by two is natural multiplication, not word multiplication. -/
theorem toNat_add_eq_twice_and_add_xor {width : Nat} (a b : BitVec width) :
    a.toNat + b.toNat = 2 * (a &&& b).toNat + (a ^^^ b).toNat := by
  simpa only [BitVec.toNat_and, BitVec.toNat_xor] using
    nat_add_eq_twice_and_add_xor a.toNat b.toNat

/-- Before performing word addition, the two natural summands already give the
floor of the unbounded average. The shift is unsigned, by the natural count one. -/
theorem and_add_half_xor_eq_half_sum {width : Nat} (a b : BitVec width) :
    (a &&& b).toNat + ((a ^^^ b) >>> 1).toNat = (a.toNat + b.toNat) / 2 := by
  rw [toNat_add_eq_twice_and_add_xor a b, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.pow_one]
  omega

/-- The final addition cannot overflow, without a restriction on the inputs or
on their full-width sum. This also holds at width zero, where the bound is one. -/
theorem and_add_half_xor_lt {width : Nat} (a b : BitVec width) :
    (a &&& b).toNat + ((a ^^^ b) >>> 1).toNat < 2 ^ width := by
  rw [and_add_half_xor_eq_half_sum]
  have := a.isLt
  have := b.isLt
  omega

/-- Exact correctness of the AND/XOR/unsigned-shift expression, for all widths. -/
theorem toNat_and_add_half_xor {width : Nat} (a b : BitVec width) :
    ((a &&& b) + ((a ^^^ b) >>> 1)).toNat = (a.toNat + b.toNat) / 2 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (and_add_half_xor_lt a b)]
  exact and_add_half_xor_eq_half_sum a b

/-- Unsigned floor average, computed without forming the possibly overflowing
input sum. No positive-width or high-bit restriction is required. -/
def unsignedAverage {width : Nat} (a b : BitVec width) : BitVec width :=
  (a &&& b) + ((a ^^^ b) >>> 1)

/-- The helper's mathematical contract uses the unbounded input sum. -/
theorem unsignedAverage_toNat {width : Nat} (a b : BitVec width) :
    (unsignedAverage a b).toNat = (a.toNat + b.toNat) / 2 :=
  toNat_and_add_half_xor a b

/-- Explicit degenerate-width behavior; no nonempty-word premise is hidden. -/
theorem unsignedAverage_zero_width (a b : BitVec 0) : unsignedAverage a b = 0 :=
  Subsingleton.elim _ _

end EDSL.WordMath
