/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Popcount

set_option warningAsError true
set_option autoImplicit false

namespace EDSL.Arithmetic64
open X86

/-- Independent full64 set-bit cardinality, returned as an unsigned 32-bit
value. The upper half of the output is unconstrained. Every input is in the
domain; usefulness selects positive cardinalities strictly below 64. -/
def populationCount : PureCall.Spec where
  Input := Word
  arguments input index :=
    if index.val = 0 then some (.word64 input) else none
  domain _ := True
  result input output := (output.setWidth 32).toNat = WordMath.cardinality input
  useful input := 0 < WordMath.cardinality input ∧ WordMath.cardinality input < 64

/-- Full64 RDI is the only argument binding. -/
theorem populationCount_bound_iff (input : Word) (state : State) :
    PureCall.Bound populationCount input state ↔ state.registers .rdi = input := by
  constructor
  · intro bound
    exact bound 0 (.word64 input) rfl
  · intro value index argument binding
    simp only [populationCount] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · contradiction

theorem populationCount_domain (input : Word) : populationCount.domain input := trivial

theorem populationCount_useful_iff (input : Word) :
    populationCount.useful input ↔
      0 < WordMath.cardinality input ∧ WordMath.cardinality input < 64 := Iff.rfl

/-- Separated low and high set bits give an asymmetric useful input. -/
theorem populationCount_useful_asymmetric : populationCount.useful (0x81 : Word) := by
  change 0 < WordMath.cardinality (0x81 : Word) ∧ WordMath.cardinality (0x81 : Word) < 64
  decide

theorem populationCount_cardinality_le (input : Word) : WordMath.cardinality input ≤ 64 :=
  WordMath.cardinality_le_width input

/-- The result fixes exactly the low 32 bits. -/
theorem populationCount_result_iff (input output : Word) :
    populationCount.result input output ↔
      output.setWidth 32 = BitVec.ofNat 32 (WordMath.cardinality input) := by
  change (output.setWidth 32).toNat = WordMath.cardinality input ↔ _
  rw [← BitVec.toNat_inj,
    WordMath.ofNat32_toNat_of_le64 (populationCount_cardinality_le input)]

/-- Existence is mathematical representability, with no execution premise. -/
theorem populationCount_result_exists (input : Word) :
    ∃ output : Word, populationCount.result input output := by
  refine ⟨BitVec.ofNat 64 (WordMath.cardinality input), ?_⟩
  apply (populationCount_result_iff input _).mpr
  simp

theorem populationCount_result_low32_unique {input left right : Word}
    (leftResult : populationCount.result input left)
    (rightResult : populationCount.result input right) :
    left.setWidth 32 = right.setWidth 32 := by
  exact BitVec.eq_of_toNat_eq (leftResult.trans rightResult.symm)

/-- A result always exists, and any two results have the same low32 value.
Uniqueness does not assert equality of the unconstrained upper halves. -/
theorem populationCount_result_exists_unique_low32 (input : Word) :
    ∃ output : Word, populationCount.result input output ∧
      ∀ other : Word, populationCount.result input other →
        other.setWidth 32 = output.setWidth 32 := by
  obtain ⟨output, satisfies⟩ := populationCount_result_exists input
  exact ⟨output, satisfies, fun _ other => populationCount_result_low32_unique other satisfies⟩

end EDSL.Arithmetic64
