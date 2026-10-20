/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Average

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Arithmetic64
open X86

/-- Unsigned floor average of two full64 arguments. The sum is an unbounded
natural sum; every pair, including an overflowing word sum, is admitted. The
relation names no instruction, compiler, execution or successful future run. -/
def average : PureCall.Spec where
  Input := Word × Word
  arguments value index :=
    if index.val = 0 then some (.word64 value.1)
    else if index.val = 1 then some (.word64 value.2) else none
  domain _ := True
  result value output := output.toNat = (value.1.toNat + value.2.toNat) / 2
  useful value := value.1 ≠ value.2 ∧ 2^64 ≤ value.1.toNat + value.2.toNat

/-- Only full64 RDI and RSI are bound. Unbound registers and flags are arbitrary. -/
theorem average_bound_iff (value : Word × Word) (state : State) :
    PureCall.Bound average value state ↔
      state.registers .rdi = value.1 ∧ state.registers .rsi = value.2 := by
  constructor
  · intro bound
    exact ⟨bound 0 (.word64 value.1) rfl, bound 1 (.word64 value.2) rfl⟩
  · rintro ⟨left, right⟩ index argument binding
    simp only [average] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact left
    · split at binding
      · have one : index = 1 := Fin.ext (by assumption)
        subst index
        cases binding
        exact right
      · contradiction

theorem average_domain (value : Word × Word) : average.domain value := trivial

theorem average_result_iff (value : Word × Word) (output : Word) :
    average.result value output ↔ output.toNat = (value.1.toNat + value.2.toNat) / 2 :=
  Iff.rfl

/-- Mathematical representability, without any premise about a machine run. -/
theorem average_result_exists_unique (value : Word × Word) :
    ∃ output, average.result value output ∧
      ∀ other, average.result value other → other = output := by
  refine ⟨WordMath.unsignedAverage value.1 value.2,
    WordMath.unsignedAverage_toNat value.1 value.2, ?_⟩
  intro other satisfies
  exact BitVec.eq_of_toNat_eq (satisfies.trans
    (WordMath.unsignedAverage_toNat value.1 value.2).symm)

/-- Distinct high inputs require handling a sum larger than any full64 word.
Usefulness is separate from the universal admission domain. -/
theorem average_useful_overflow_asymmetric :
    average.useful ((0xffffffffffffffff, 0xfffffffffffffffd) : Word × Word) := by
  change (0xffffffffffffffff : Word) ≠ 0xfffffffffffffffd ∧
    2^64 ≤ (0xffffffffffffffff : Word).toNat + (0xfffffffffffffffd : Word).toNat
  decide +kernel

end EDSL.Arithmetic64
