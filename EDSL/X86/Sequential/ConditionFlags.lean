/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Condition
import EDSL.X86.Sequential.Flags

set_option warningAsError true

namespace EDSL.X86.Sequential

/-- SF xor OF corrects the sign of the wrapped subtraction. Same-sign
operands cannot overflow; opposite signs determine signed order independently
of the wrapped result's sign. All facts come from checked BitVec arithmetic. -/
private theorem signed_sub_less {width : Nat} (left right : BitVec width) :
    ((left - right).msb ^^ left.ssubOverflow right) = decide (left.toInt < right.toInt) := by
  by_cases same : left.msb = right.msb
  · have overflow : left.ssubOverflow right = false := by
      rw [BitVec.ssubOverflow_eq,same]
      cases right.msb <;> rfl
    have ordinary := BitVec.toInt_sub_of_not_ssubOverflow
      (x := left) (y := right) (by rw [overflow]; decide)
    rw [overflow,Bool.xor_false,BitVec.msb_eq_toInt,ordinary]
    have order : left.toInt - right.toInt < 0 ↔ left.toInt < right.toInt := by omega
    simp only [order]
  · cases leftSign : left.msb <;> cases rightSign : right.msb
    · exact False.elim (same (leftSign.trans rightSign.symm))
    · have leftNonnegative := BitVec.toInt_nonneg_of_msb_false leftSign
      have rightNegative := BitVec.toInt_neg_of_msb_true rightSign
      have order : ¬left.toInt < right.toInt := by omega
      rw [BitVec.ssubOverflow_eq,leftSign,rightSign]
      simp only [order,decide_false]
      cases (left - right).msb <;> rfl
    · have leftNegative := BitVec.toInt_neg_of_msb_true leftSign
      have rightNonnegative := BitVec.toInt_nonneg_of_msb_false rightSign
      have order : left.toInt < right.toInt := by omega
      rw [BitVec.ssubOverflow_eq,leftSign,rightSign]
      simp only [order,decide_true]
      cases (left - right).msb <;> rfl
    · exact False.elim (same (leftSign.trans rightSign.symm))

/-- Unsigned borrow from the full64 CMP equals mathematical natural order. -/
theorem Condition.cmp_below (old left right : Word) :
    holds .below (cmpFlags64 old left right) = decide (left.toNat < right.toNat) :=
  (cmpFlags64_bits old left right).1

theorem Condition.cmp_aboveEqual (old left right : Word) :
    holds .aboveEqual (cmpFlags64 old left right) = decide (right.toNat ≤ left.toNat) := by
  change Bool.not (holds .below (cmpFlags64 old left right)) = _
  rw [cmp_below]
  simp only [← decide_not,Nat.not_lt]

theorem Condition.cmp_equal_nat (old left right : Word) :
    holds .equal (cmpFlags64 old left right) = decide (left.toNat = right.toNat) := by
  simpa only [holds,Bool.beq_eq_decide_eq,← BitVec.toNat_inj] using cmpFlags64_zero old left right

theorem Condition.cmp_notEqual_nat (old left right : Word) :
    holds .notEqual (cmpFlags64 old left right) = decide (left.toNat ≠ right.toNat) := by
  change Bool.not (holds .equal (cmpFlags64 old left right)) = _
  rw [cmp_equal_nat]
  simp only [← decide_not]

theorem Condition.cmp_belowEqual (old left right : Word) :
    holds .belowEqual (cmpFlags64 old left right) = decide (left.toNat ≤ right.toNat) := by
  change (holds .below (cmpFlags64 old left right) || holds .equal (cmpFlags64 old left right)) = _
  rw [cmp_below,cmp_equal_nat,← Bool.decide_or]
  have order : left.toNat < right.toNat ∨ left.toNat = right.toNat ↔ left.toNat ≤ right.toNat := by omega
  simp only [order]

theorem Condition.cmp_above (old left right : Word) :
    holds .above (cmpFlags64 old left right) = decide (right.toNat < left.toNat) := by
  change (!holds .below (cmpFlags64 old left right) && !holds .equal (cmpFlags64 old left right)) = _
  rw [cmp_below,cmp_equal_nat]
  simp only [← decide_not,← Bool.decide_and]
  have order : (¬left.toNat < right.toNat) ∧ left.toNat ≠ right.toNat ↔ right.toNat < left.toNat := by omega
  simp only [order]

/-- Equality is independent of the chosen signed or unsigned interpretation. -/
theorem Condition.cmp_equal_int (old left right : Word) :
    holds .equal (cmpFlags64 old left right) = decide (left.toInt = right.toInt) := by
  simpa only [holds,Bool.beq_eq_decide_eq,BitVec.toInt_inj] using cmpFlags64_zero old left right

theorem Condition.cmp_notEqual_int (old left right : Word) :
    holds .notEqual (cmpFlags64 old left right) = decide (left.toInt ≠ right.toInt) := by
  change Bool.not (holds .equal (cmpFlags64 old left right)) = _
  rw [cmp_equal_int]
  simp only [← decide_not]

/-- Signed CMP order includes overflow correction, including INT64_MIN/MAX. -/
theorem Condition.cmp_less (old left right : Word) :
    holds .less (cmpFlags64 old left right) = decide (left.toInt < right.toInt) := by
  change ((cmpFlags64 old left right).getLsbD 7 ^^ (cmpFlags64 old left right).getLsbD 11) = _
  rw [(cmpFlags64_bits old left right).2.2.2.2.1,(cmpFlags64_bits old left right).2.2.2.2.2]
  exact signed_sub_less left right

theorem Condition.cmp_greaterEqual (old left right : Word) :
    holds .greaterEqual (cmpFlags64 old left right) = decide (right.toInt ≤ left.toInt) := by
  rw [holds_greaterEqual,cmp_less]
  simp only [← decide_not,Int.not_lt]

theorem Condition.cmp_lessEqual (old left right : Word) :
    holds .lessEqual (cmpFlags64 old left right) = decide (left.toInt ≤ right.toInt) := by
  change (holds .equal (cmpFlags64 old left right) || holds .less (cmpFlags64 old left right)) = _
  rw [cmp_equal_int,cmp_less,← Bool.decide_or]
  have order : left.toInt = right.toInt ∨ left.toInt < right.toInt ↔ left.toInt ≤ right.toInt := by omega
  simp only [order]

theorem Condition.cmp_greater (old left right : Word) :
    holds .greater (cmpFlags64 old left right) = decide (right.toInt < left.toInt) := by
  change (!holds .equal (cmpFlags64 old left right) && holds .greaterEqual (cmpFlags64 old left right)) = _
  rw [cmp_equal_int,cmp_greaterEqual]
  simp only [← decide_not,← Bool.decide_and]
  have order : left.toInt ≠ right.toInt ∧ right.toInt ≤ left.toInt ↔ right.toInt < left.toInt := by omega
  simp only [order]

/-- Unsigned borrow from the full32 CMP equals mathematical natural order. -/
theorem Condition.cmp32_below (old : Word) (left right : BitVec 32) :
    holds .below (cmpFlags32 old left right) = decide (left.toNat < right.toNat) :=
  (cmpFlags32_bits old left right).1

theorem Condition.cmp32_aboveEqual (old : Word) (left right : BitVec 32) :
    holds .aboveEqual (cmpFlags32 old left right) = decide (right.toNat ≤ left.toNat) := by
  change Bool.not (holds .below (cmpFlags32 old left right)) = _
  rw [cmp32_below]
  simp only [← decide_not,Nat.not_lt]

theorem Condition.cmp32_equal_nat (old : Word) (left right : BitVec 32) :
    holds .equal (cmpFlags32 old left right) = decide (left.toNat = right.toNat) := by
  simpa only [holds,Bool.beq_eq_decide_eq,← BitVec.toNat_inj] using cmpFlags32_zero old left right

theorem Condition.cmp32_notEqual_nat (old : Word) (left right : BitVec 32) :
    holds .notEqual (cmpFlags32 old left right) = decide (left.toNat ≠ right.toNat) := by
  change Bool.not (holds .equal (cmpFlags32 old left right)) = _
  rw [cmp32_equal_nat]
  simp only [← decide_not]

theorem Condition.cmp32_belowEqual (old : Word) (left right : BitVec 32) :
    holds .belowEqual (cmpFlags32 old left right) = decide (left.toNat ≤ right.toNat) := by
  change (holds .below (cmpFlags32 old left right) || holds .equal (cmpFlags32 old left right)) = _
  rw [cmp32_below,cmp32_equal_nat,← Bool.decide_or]
  have order : left.toNat < right.toNat ∨ left.toNat = right.toNat ↔ left.toNat ≤ right.toNat := by omega
  simp only [order]

theorem Condition.cmp32_above (old : Word) (left right : BitVec 32) :
    holds .above (cmpFlags32 old left right) = decide (right.toNat < left.toNat) := by
  change (!holds .below (cmpFlags32 old left right) && !holds .equal (cmpFlags32 old left right)) = _
  rw [cmp32_below,cmp32_equal_nat]
  simp only [← decide_not,← Bool.decide_and]
  have order : (¬left.toNat < right.toNat) ∧ left.toNat ≠ right.toNat ↔ right.toNat < left.toNat := by omega
  simp only [order]

/-- Equality is independent of the chosen signed or unsigned interpretation. -/
theorem Condition.cmp32_equal_int (old : Word) (left right : BitVec 32) :
    holds .equal (cmpFlags32 old left right) = decide (left.toInt = right.toInt) := by
  simpa only [holds,Bool.beq_eq_decide_eq,BitVec.toInt_inj] using cmpFlags32_zero old left right

theorem Condition.cmp32_notEqual_int (old : Word) (left right : BitVec 32) :
    holds .notEqual (cmpFlags32 old left right) = decide (left.toInt ≠ right.toInt) := by
  change Bool.not (holds .equal (cmpFlags32 old left right)) = _
  rw [cmp32_equal_int]
  simp only [← decide_not]

/-- Signed CMP order includes overflow correction, including INT32_MIN/MAX. -/
theorem Condition.cmp32_less (old : Word) (left right : BitVec 32) :
    holds .less (cmpFlags32 old left right) = decide (left.toInt < right.toInt) := by
  change ((cmpFlags32 old left right).getLsbD 7 ^^ (cmpFlags32 old left right).getLsbD 11) = _
  rw [(cmpFlags32_bits old left right).2.2.2.2.1,(cmpFlags32_bits old left right).2.2.2.2.2]
  exact signed_sub_less left right

theorem Condition.cmp32_greaterEqual (old : Word) (left right : BitVec 32) :
    holds .greaterEqual (cmpFlags32 old left right) = decide (right.toInt ≤ left.toInt) := by
  rw [holds_greaterEqual,cmp32_less]
  simp only [← decide_not,Int.not_lt]

theorem Condition.cmp32_lessEqual (old : Word) (left right : BitVec 32) :
    holds .lessEqual (cmpFlags32 old left right) = decide (left.toInt ≤ right.toInt) := by
  change (holds .equal (cmpFlags32 old left right) || holds .less (cmpFlags32 old left right)) = _
  rw [cmp32_equal_int,cmp32_less,← Bool.decide_or]
  have order : left.toInt = right.toInt ∨ left.toInt < right.toInt ↔ left.toInt ≤ right.toInt := by omega
  simp only [order]

theorem Condition.cmp32_greater (old : Word) (left right : BitVec 32) :
    holds .greater (cmpFlags32 old left right) = decide (right.toInt < left.toInt) := by
  change (!holds .equal (cmpFlags32 old left right) && holds .greaterEqual (cmpFlags32 old left right)) = _
  rw [cmp32_equal_int,cmp32_greaterEqual]
  simp only [← decide_not,← Bool.decide_and]
  have order : left.toInt ≠ right.toInt ∧ right.toInt ≤ left.toInt ↔ right.toInt < left.toInt := by omega
  simp only [order]


/-- TEST32 equality and sign use the low32 AND; overflow correction reduces
to the sign because TEST clears OF. AF cannot affect any condition code. -/
theorem Condition.test32_equal (old : Word) (left right : BitVec 32) (af : Bool) :
    holds .equal (logicalFlags32 old (left &&& right) af) = (left &&& right == 0) :=
  logicalFlags32_zero ..

theorem Condition.test32_less (old : Word) (left right : BitVec 32) (af : Bool) :
    holds .less (logicalFlags32 old (left &&& right) af) =
      decide ((left &&& right).toInt < 0) := by
  change (_ ^^ _) = _
  rw [(logicalFlags32_bits ..).2.2.2.2.1, (logicalFlags32_bits ..).2.2.2.2.2]
  simp only [Bool.xor_false, BitVec.msb_eq_toInt]

theorem Condition.test32_af_independent (condition : Condition) (old : Word)
    (left right : BitVec 32) (first second : Bool) :
    holds condition (logicalFlags32 old (left &&& right) first) =
      holds condition (logicalFlags32 old (left &&& right) second) := by
  have a := logicalFlags32_bits old (left &&& right) first
  have b := logicalFlags32_bits old (left &&& right) second
  cases condition <;> simp_all only [holds]

end EDSL.X86.Sequential
