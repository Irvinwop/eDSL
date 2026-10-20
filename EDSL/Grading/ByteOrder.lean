/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init.Data.BitVec.Lemmas
import Lean.Elab.Tactic.Omega
import EDSL.Grading.FirstMatchConsumers
import Init.Data.List.Lex

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.ByteOrder
abbrev Byte := BitVec 8

/-- Signed interpretation of subtraction at width 32 after unsigned extension. -/
def signedDifference (a b : Byte) : Int :=
  (a.zeroExtend 32 - b.zeroExtend 32).toInt

theorem zeroExtend32_toInt (a : Byte) :
    (a.zeroExtend 32).toInt = (a.toNat : Int) := by
  have bound : a.toNat < 256 := a.isLt
  change (a.setWidth 32).toInt = (a.toNat : Int)
  rw [BitVec.toInt_setWidth]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- This holds for all bytes, including those whose eighth bit is set. -/
theorem signedDifference_eq (a b : Byte) :
    signedDifference a b = (a.toNat : Int) - (b.toNat : Int) := by
  have boundA : a.toNat < 256 := a.isLt
  have boundB : b.toNat < 256 := b.isLt
  unfold signedDifference
  rw [BitVec.toInt_sub, zeroExtend32_toInt, zeroExtend32_toInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem signedDifference_range (a b : Byte) :
    -255 ≤ signedDifference a b ∧ signedDifference a b ≤ 255 := by
  have boundA : a.toNat < 256 := a.isLt
  have boundB : b.toNat < 256 := b.isLt
  rw [signedDifference_eq]
  omega

theorem signedDifference_negative_iff (a b : Byte) :
    signedDifference a b < 0 ↔ a < b := by
  rw [signedDifference_eq, BitVec.lt_def]
  omega

theorem signedDifference_zero_iff (a b : Byte) :
    signedDifference a b = 0 ↔ a = b := by
  rw [signedDifference_eq, ← BitVec.toNat_inj]
  omega

theorem signedDifference_positive_iff (a b : Byte) :
    0 < signedDifference a b ↔ b < a := by
  rw [signedDifference_eq, BitVec.lt_def]
  omega

open EDSL.Grading.FirstMatch

/-- Mathematical lexicographic order of unsigned bytes. -/
def UnsignedLex (left right : List Byte) : Prop :=
  List.Lex (fun a b => a.toNat < b.toNat) left right

/-- Only the sign is specified. Equal extents are part of the contract. -/
structure Sign (left right : List Byte) (value : Int) : Prop where
  sameLength : left.length = right.length
  negative : value < 0 ↔ UnsignedLex left right
  zero : value = 0 ↔ left = right
  positive : 0 < value ↔ UnsignedLex right left

/-- A common prefix can be removed from the independent order relation. -/
theorem unsignedLex_common_prefix (front left right : List Byte) :
    UnsignedLex (front ++ left) (front ++ right) ↔ UnsignedLex left right := by
  unfold UnsignedLex
  induction front with
  | nil => rfl
  | cons byte front induction =>
    simp only [List.cons_append, List.cons_lex_cons_iff, Nat.lt_irrefl,
      false_or, true_and, induction]

theorem split_at_present {values : List Byte} {index : Nat} {byte : Byte}
    (present : values[index]? = some byte) :
    values = values.take index ++ byte :: values.drop (index + 1) := by
  obtain ⟨inside, equal⟩ := List.getElem_of_getElem? present
  calc
    values = values.take index ++ values.drop index := (List.take_append_drop _ _).symm
    _ = _ := by rw [List.drop_eq_getElem_cons inside, equal]

/-- Reuse the accepted exhaustion theorem on the inspected paired prefix. -/
theorem paired_prefix_equal {left right : List Byte} {count : Nat}
    (scanned : Prefix (left.zip right) (fun pair => pair.1 != pair.2) count) :
    left.take count = right.take count := by
  have commonBound : count ≤ min left.length right.length := by simpa using scanned.bound
  have leftBound : count ≤ left.length := by omega
  have rightBound : count ≤ right.length := by omega
  have takenLength : (left.take count).length = count := by simp [Nat.min_eq_left leftBound]
  have takenRightLength : (right.take count).length = count := by
    simp [Nat.min_eq_left rightBound]
  have takenZipLength : ((left.zip right).take count).length = count := by
    simp only [List.length_take]
    exact Nat.min_eq_left scanned.bound
  have taken : Prefix ((left.zip right).take count) (fun pair => pair.1 != pair.2) count := by
    refine ⟨by omega, ?_⟩
    intro index before ⟨pair, present, hit⟩
    apply scanned.nonmatch index before
    exact ⟨pair, (List.getElem?_take_of_lt before).symm.trans present, hit⟩
  have exhausted := taken.finish_bound takenZipLength.symm
  have paired : Result ((left.take count).zip (right.take count))
      (fun pair => pair.1 != pair.2) (left.take count).length := by
    simpa only [List.zip_eq_zipWith, List.take_zipWith, takenLength] using exhausted
  exact (Consumers.paired_exhaustion_iff_equal (takenLength.trans takenRightLength.symm)).mp paired

/-- A different pair following an equal prefix determines both lexicographic orders. -/
theorem orders_at_first_unequal {left right : List Byte} {index : Nat} {a b : Byte}
    (prefixEqual : left.take index = right.take index)
    (leftAt : left[index]? = some a) (rightAt : right[index]? = some b)
    (different : a ≠ b) :
    (UnsignedLex left right ↔ a < b) ∧
    (UnsignedLex right left ↔ b < a) ∧ left ≠ right := by
  have unequalLists : left ≠ right := by
    intro equal
    have equalAt := leftAt.symm.trans (equal ▸ rightAt)
    exact different (Option.some.inj equalAt)
  refine ⟨?_, ?_, unequalLists⟩
  · rw [split_at_present leftAt, split_at_present rightAt, ← prefixEqual,
      unsignedLex_common_prefix]
    simp only [UnsignedLex, List.cons_lex_cons_iff, different, false_and, or_false,
      BitVec.lt_def]
  · rw [split_at_present rightAt, split_at_present leftAt, prefixEqual,
      unsignedLex_common_prefix]
    have reverseDifferent : b ≠ a := Ne.symm different
    simp only [UnsignedLex, List.cons_lex_cons_iff, reverseDifferent, false_and, or_false,
      BitVec.lt_def]

/-- Any earliest unequal prefix yields the sign of its signed width-32 difference. -/
theorem sign_at_first_unequal {left right : List Byte} {index : Nat} {a b : Byte}
    (sameLength : left.length = right.length)
    (prefixEqual : left.take index = right.take index)
    (leftAt : left[index]? = some a) (rightAt : right[index]? = some b)
    (different : a ≠ b) : Sign left right (signedDifference a b) := by
  obtain ⟨less, greater, unequalLists⟩ :=
    orders_at_first_unequal prefixEqual leftAt rightAt different
  refine ⟨sameLength, ?_, ?_, ?_⟩
  · exact (signedDifference_negative_iff a b).trans less.symm
  · simp only [signedDifference_zero_iff, different, unequalLists]
  · exact (signedDifference_positive_iff a b).trans greater.symm

/-- Zipped inequality gives equal inspected prefixes and the actual unequal bytes. -/
theorem result_first_unequal {left right : List Byte} {index : Nat}
    (sameLength : left.length = right.length)
    (first : Result (left.zip right) (fun pair => pair.1 != pair.2) index)
    (inside : index < left.length) :
    left.take index = right.take index ∧
      ∃ a b, left[index]? = some a ∧ right[index]? = some b ∧ a ≠ b := by
  have insideZip : index < (left.zip right).length := by simpa [sameLength] using inside
  obtain ⟨a, b, leftAt, rightAt, hit⟩ := MatchesAt.zip_iff.mp (first.hit insideZip)
  refine ⟨paired_prefix_equal first.toPrefix, a, b, leftAt, rightAt, ?_⟩
  simpa using hit

theorem result_hit_sign {left right : List Byte} {index : Nat}
    (sameLength : left.length = right.length)
    (first : Result (left.zip right) (fun pair => pair.1 != pair.2) index)
    (inside : index < left.length) :
    ∃ a b, left[index]? = some a ∧ right[index]? = some b ∧
      a ≠ b ∧ Sign left right (signedDifference a b) ∧
      -255 ≤ signedDifference a b ∧ signedDifference a b ≤ 255 := by
  obtain ⟨prefixEqual, a, b, leftAt, rightAt, different⟩ :=
    result_first_unequal sameLength first inside
  exact ⟨a, b, leftAt, rightAt, different,
    sign_at_first_unequal sameLength prefixEqual leftAt rightAt different,
    signedDifference_range a b⟩

/-- Equality, including empty lists, has sign zero under the independent contract. -/
theorem sign_zero_iff_equal (left right : List Byte) : Sign left right 0 ↔ left = right := by
  constructor
  · intro sign
    exact sign.zero.mp rfl
  · rintro rfl
    have noLex : ¬ UnsignedLex left left :=
      List.lex_irrefl (r := fun a b : Byte => a.toNat < b.toNat)
        (fun byte => Nat.lt_irrefl byte.toNat) left
    exact ⟨rfl, by simpa using noLex, by simp, by simpa using noLex⟩

/-- Whole-buffer exhaustion is exactly zero sign; equality of lengths is explicit. -/
theorem result_exhaustion_iff_sign_zero {left right : List Byte}
    (sameLength : left.length = right.length) :
    Result (left.zip right) (fun pair => pair.1 != pair.2) left.length ↔
      Sign left right 0 := by
  rw [Consumers.paired_exhaustion_iff_equal sameLength, sign_zero_iff_equal]

/-- The result always supplies either complete equality or an earliest-pair sign. -/
theorem result_sign_cases {left right : List Byte} {index : Nat}
    (sameLength : left.length = right.length)
    (first : Result (left.zip right) (fun pair => pair.1 != pair.2) index) :
    (index = left.length ∧ Sign left right 0) ∨
      (index < left.length ∧ ∃ a b, left[index]? = some a ∧ right[index]? = some b ∧
        a ≠ b ∧ Sign left right (signedDifference a b) ∧
        -255 ≤ signedDifference a b ∧ signedDifference a b ≤ 255) := by
  have bound := first.zip_bound_of_length_eq sameLength
  by_cases exhausted : index = left.length
  · exact Or.inl ⟨exhausted, (result_exhaustion_iff_sign_zero sameLength).mp (exhausted ▸ first)⟩
  · have inside : index < left.length := by omega
    exact Or.inr ⟨inside, result_hit_sign sameLength first inside⟩

/-- Every pair of equal-length finite byte lists admits the independent sign contract. -/
theorem sign_exists {left right : List Byte} (sameLength : left.length = right.length) :
    ∃ value : Int, Sign left right value := by
  obtain ⟨index, first⟩ := Result.exists (left.zip right) (fun pair => pair.1 != pair.2)
  rcases result_sign_cases sameLength first with exhausted | found
  · exact ⟨0, exhausted.2⟩
  · obtain ⟨a, b, _, _, _, sign, _⟩ := found.2
    exact ⟨signedDifference a b, sign⟩

end EDSL.Grading.ByteOrder
