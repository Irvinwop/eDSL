/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Scalar

set_option warningAsError true

namespace EDSL.Scalar32
open X86

structure ClampInput where
  value : BitVec 32
  lower : BitVec 32
  upper : BitVec 32

/-- Mathematical interval projection, independently of flags, instructions,
compiler shape, execution or fuel. Equal endpoints and signed overflow boundary
values are admitted by the separately stated domain. -/
def Clamped (value lower upper result : Int) : Prop :=
  lower ≤ result ∧ result ≤ upper ∧
    (value < lower → result = lower) ∧
    (lower ≤ value → value ≤ upper → result = value) ∧
    (upper < value → result = upper)

theorem clamped_unique {value lower upper first second : Int}
    (left : Clamped value lower upper first)
    (right : Clamped value lower upper second) : first = second := by
  rcases left with ⟨_, _, leftBelow, leftWithin, leftAbove⟩
  rcases right with ⟨_, _, rightBelow, rightWithin, rightAbove⟩
  by_cases below : value < lower
  · exact (leftBelow below).trans (rightBelow below).symm
  · by_cases above : upper < value
    · exact (leftAbove above).trans (rightAbove above).symm
    · have lowerBound : lower ≤ value := by omega
      have upperBound : value ≤ upper := by omega
      exact (leftWithin lowerBound upperBound).trans
        (rightWithin lowerBound upperBound).symm

/-- A mathematical projection satisfies the relational contract. This lemma
mentions no machine operation or flags, and includes both boundary equalities. -/
theorem clamped_projection (value lower upper : Int) (ordered : lower ≤ upper) :
    Clamped value lower upper
      (if value < lower then lower else if upper < value then upper else value) := by
  by_cases below : value < lower
  · rw [ite_eq_left below]
    refine ⟨by omega, ordered, (fun _ => rfl), ?_, ?_⟩
    · intro lowerBound upperBound
      omega
    · intro above
      omega
  · rw [ite_eq_right below]
    by_cases above : upper < value
    · rw [ite_eq_left above]
      refine ⟨ordered, by omega, ?_, ?_, (fun _ => rfl)⟩
      · intro belowLower
        omega
      · intro lowerBound upperBound
        omega
    · rw [ite_eq_right above]
      refine ⟨by omega, by omega, ?_, (fun _ _ => rfl), ?_⟩
      · intro belowLower
        omega
      · intro aboveUpper
        omega

/-- The API fixes signed low32 inputs while leaving upper argument halves
arbitrary. A C int32 return is observed in low32; a separate machine observation
may additionally establish the zero upper half. -/
def clampSigned : PureCall.Spec where
  Input := ClampInput
  arguments input index :=
    if index.val = 0 then some (.low32 input.value)
    else if index.val = 1 then some (.low32 input.lower)
    else if index.val = 2 then some (.low32 input.upper) else none
  domain input := input.lower.toInt ≤ input.upper.toInt
  result input result :=
    Clamped input.value.toInt input.lower.toInt input.upper.toInt
      (result.setWidth 32).toInt
  useful input := input.lower.toInt < input.value.toInt ∧
    input.value.toInt < input.upper.toInt

theorem clamp_bound_iff (input : ClampInput) (state : State) :
    PureCall.Bound clampSigned input state ↔
      (state.registers .rdi).setWidth 32 = input.value ∧
      (state.registers .rsi).setWidth 32 = input.lower ∧
      (state.registers .rdx).setWidth 32 = input.upper := by
  constructor
  · intro bound
    exact ⟨bound 0 (.low32 input.value) rfl,
      bound 1 (.low32 input.lower) rfl, bound 2 (.low32 input.upper) rfl⟩
  · rintro ⟨value, lower, upper⟩ index argument binding
    simp only [clampSigned] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · split at binding
      · have one : index = 1 := Fin.ext (by assumption)
        subst index
        cases binding
        exact lower
      · split at binding
        · have two : index = 2 := Fin.ext (by assumption)
          subst index
          cases binding
          exact upper
        · contradiction

/-- Signed low32 absolute value is the independent nonnegative-square
relation. The sole excluded input has no representable signed low32 result.
Argument upper halves and return upper halves are unrestricted by this spec. -/
def absoluteSigned : PureCall.Spec where
  Input := BitVec 32
  arguments input index :=
    if index.val = 0 then some (.low32 input) else none
  domain input := input.toInt ≠ -2147483648
  result input result := WordMath.AbsSquare input.toInt (result.setWidth 32).toInt
  useful input := input.toInt < 0

theorem absolute_domain_iff (input : BitVec 32) :
    absoluteSigned.domain input ↔ input ≠ BitVec.intMin 32 := by
  exact not_congr (WordMath.eq_intMin32_iff input).symm

/-- Exactly the first low32 argument is bound; every other register and flag,
and the upper half of RDI, remain arbitrary. -/
theorem absolute_bound_iff (input : BitVec 32) (state : State) :
    PureCall.Bound absoluteSigned input state ↔
      (state.registers .rdi).setWidth 32 = input := by
  constructor
  · intro bound
    exact bound 0 (.low32 input) rfl
  · intro value index argument binding
    simp only [absoluteSigned] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · contradiction

/-- A reusable word-construction bridge, proved from the mathematical spec. -/
theorem absolute_result_iff (input : BitVec 32) (result : Word)
    (domain : absoluteSigned.domain input) :
    absoluteSigned.result input result ↔
      result.setWidth 32 = WordMath.negSelect32 input :=
  WordMath.absSquare32_iff input (result.setWidth 32) domain

theorem absolute_result_exists (input : BitVec 32)
    (domain : absoluteSigned.domain input) : ∃ result, absoluteSigned.result input result := by
  refine ⟨(WordMath.negSelect32 input).setWidth 64, ?_⟩
  apply (absolute_result_iff _ _ domain).mpr
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The signed low32 result is unique; no return upper-half restriction is added. -/
theorem absolute_result_unique {input : BitVec 32} {first second : Word}
    (left : absoluteSigned.result input first) (right : absoluteSigned.result input second) :
    first.setWidth 32 = second.setWidth 32 :=
  BitVec.eq_of_toInt_eq (WordMath.absSquare_unique left right)

theorem absolute_intMin_no_result (result : Word) :
    ¬ absoluteSigned.result (BitVec.intMin 32) result :=
  WordMath.intMin32_no_result (result.setWidth 32)

/-- Usefulness requires a changed mathematical value, independently of code. -/
theorem absolute_useful_changes (input : BitVec 32) (result : Word)
    (useful : absoluteSigned.useful input)
    (satisfies : absoluteSigned.result input result) :
    result.setWidth 32 ≠ input := by
  intro same
  have nonnegative := satisfies.1
  rw [same] at nonnegative
  change input.toInt < 0 at useful
  omega

end EDSL.Scalar32
