/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init.Data.BitVec.Lemmas
import Init.Omega
set_option warningAsError true
set_option autoImplicit false

/-!
Standalone arbitrary-width set-bit cardinality. The specification scans bit
positions using Init's `cpopNatRec`; it does not execute a clearing-bit loop.
No machine, instruction, ABI, resource, compiler, or corpus claim is made here.
-/

namespace EDSL.WordMath

/-- Cardinality of the set-bit positions in `x`, as an unbounded natural. -/
def cardinality {w : Nat} (x : BitVec w) : Nat :=
  BitVec.cpopNatRec x w 0

@[simp] theorem cardinality_zero (w : Nat) : cardinality (0#w) = 0 := by
  simp [cardinality]

theorem cardinality_le_width {w : Nat} (x : BitVec w) : cardinality x ≤ w := by
  exact BitVec.cpopNatRec_zero_le x w

/-- The width bound is attained by a vector with every position set. -/
@[simp] theorem cardinality_allOnes (w : Nat) :
    cardinality (BitVec.allOnes w) = w := by
  simp [cardinality, BitVec.cpopNatRec_allOnes]

theorem cardinality_concat {w : Nat} (x : BitVec w) (b : Bool) :
    cardinality (x.concat b) = b.toNat + cardinality x := by
  simp only [cardinality, BitVec.cpopNatRec_concat_of_lt (Nat.zero_lt_succ w),
    Nat.succ_sub_one]

private theorem concat_eq_zero {w : Nat} (x : BitVec w) (b : Bool) :
    x.concat b = 0#(w + 1) ↔ x = 0#w ∧ b = false := by
  simp only [← BitVec.toNat_inj, BitVec.toNat_concat, BitVec.toNat_zero]
  cases b <;> simp <;> omega

@[simp] theorem cardinality_eq_zero_iff {w : Nat} (x : BitVec w) :
    cardinality x = 0 ↔ x = 0#w := by
  induction x using BitVec.concat_induction with
  | nil => simp [cardinality]
  | concat x b ih =>
    rw [cardinality_concat, concat_eq_zero]
    cases b <;> simp [ih]

private theorem concat_true_sub_one {w : Nat} (x : BitVec w) :
    x.concat true - 1#(w + 1) = x.concat false := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_not_usubOverflow]
  · simp [BitVec.toNat_concat]
  · simp [BitVec.usubOverflow, BitVec.toNat_concat]

private theorem concat_false_sub_one {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
    x.concat false - 1#(w + 1) = (x - 1#w).concat true := by
  have xn : x.toNat ≠ 0 := by
    intro h
    exact hx (BitVec.eq_of_toNat_eq (by simpa using h))
  have wp : 0 < w := by
    by_cases h : w = 0
    · subst w
      exact (hx (Subsingleton.elim _ _)).elim
    · omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_not_usubOverflow, BitVec.toNat_concat, BitVec.toNat_concat,
    BitVec.toNat_sub_of_not_usubOverflow]
  · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
    omega
  · simp [BitVec.usubOverflow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
    omega
  · simp [BitVec.usubOverflow, BitVec.toNat_concat]
    omega

/-- Clearing the least significant set bit removes exactly one position.
The nonzero premise is essential, including at width zero. -/
theorem cardinality_clear_add_one {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
    cardinality (x &&& (x - 1#w)) + 1 = cardinality x := by
  induction x using BitVec.concat_induction with
  | nil => simp at hx
  | concat x b ih =>
    cases b with
    | false =>
      have xn : x ≠ 0#_ := by
        intro h
        exact hx (by simp [h])
      rw [concat_false_sub_one x xn, BitVec.concat_and_concat]
      simpa [cardinality_concat] using ih xn
    | true =>
      rw [concat_true_sub_one, BitVec.concat_and_concat]
      simp [cardinality_concat, BitVec.and_self, Nat.add_comm]

/-- The equivalent natural-subtraction form of exact decrement. -/
theorem cardinality_clear_eq_sub_one {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
    cardinality (x &&& (x - 1#w)) = cardinality x - 1 := by
  have decrement := cardinality_clear_add_one x hx
  omega

theorem cardinality_pos_iff {w : Nat} (x : BitVec w) :
    0 < cardinality x ↔ x ≠ 0#w := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, cardinality_eq_zero_iff]

/-- A positive natural rank decreases on every admitted clearing step. -/
theorem cardinality_clear_lt {w : Nat} (x : BitVec w) (hx : x ≠ 0#w) :
    cardinality (x &&& (x - 1#w)) < cardinality x := by
  have decrement := cardinality_clear_add_one x hx
  omega

/-- Common arithmetic invariant, independent of instruction or block order.
`count` is a natural number; relating a modular machine counter to this number
is a separate caller obligation. -/
def CountInvariant {w : Nat} (initial remaining : BitVec w) (count : Nat) : Prop :=
  count + cardinality remaining = cardinality initial

theorem countInvariant_start {w : Nat} (initial : BitVec w) :
    CountInvariant initial initial 0 := by
  simp [CountInvariant]

theorem countInvariant_step {w : Nat} {initial remaining : BitVec w} {count : Nat}
    (invariant : CountInvariant initial remaining count) (hnz : remaining ≠ 0#w) :
    CountInvariant initial (remaining &&& (remaining - 1#w)) (count + 1) := by
  have decrement := cardinality_clear_add_one remaining hnz
  simp only [CountInvariant] at invariant ⊢
  omega

theorem countInvariant_finish {w : Nat} {initial remaining : BitVec w} {count : Nat}
    (invariant : CountInvariant initial remaining count) (done : remaining = 0#w) :
    count = cardinality initial := by
  simpa [CountInvariant, done] using invariant

theorem countInvariant_count_le {w : Nat} {initial remaining : BitVec w} {count : Nat}
    (invariant : CountInvariant initial remaining count) : count ≤ cardinality initial := by
  simp only [CountInvariant] at invariant
  omega

theorem countInvariant_count_le_width {w : Nat} {initial remaining : BitVec w}
    {count : Nat} (invariant : CountInvariant initial remaining count) : count ≤ w := by
  exact Nat.le_trans (countInvariant_count_le invariant) (cardinality_le_width initial)

/-- Before an admitted clearing step, the incremented natural counter is still
bounded by the input width. This can discharge a separate no-wrap bridge. -/
theorem countInvariant_succ_le_width {w : Nat} {initial remaining : BitVec w}
    {count : Nat} (invariant : CountInvariant initial remaining count)
    (hnz : remaining ≠ 0#w) : count + 1 ≤ w := by
  exact countInvariant_count_le_width (countInvariant_step invariant hnz)

/-- A natural count bounded by 64 is represented exactly in 32 bits. -/
theorem ofNat32_toNat_of_le64 {count : Nat} (bound : count ≤ 64) :
    (BitVec.ofNat 32 count).toNat = count := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Adding one to a 32-bit count below 64 does not wrap. -/
theorem add_one32_toNat_of_lt64 (counter : BitVec 32) (bound : counter.toNat < 64) :
    (counter + 1).toNat = counter.toNat + 1 := by
  rw [BitVec.toNat_add]
  change (counter.toNat + 1) % 2^32 = counter.toNat + 1
  exact Nat.mod_eq_of_lt (by omega)

/-- The independent invariant supplies the bound needed to increment a
32-bit representation of its natural counter. -/
theorem countInvariant_increment32 {initial remaining : BitVec 64} {count : Nat}
    (invariant : CountInvariant initial remaining count) (hnz : remaining ≠ 0#64)
    (counter : BitVec 32) (represents : counter.toNat = count) :
    (counter + 1).toNat = count + 1 := by
  have bound := countInvariant_succ_le_width invariant hnz
  rw [add_one32_toNat_of_lt64 counter (by omega), represents]

end EDSL.WordMath
