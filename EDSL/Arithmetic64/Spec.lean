/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Scalar

set_option warningAsError true

namespace EDSL.Arithmetic64
open X86

/-- The fixed full64 unsigned addition specification. Admission includes zero
and overflow; usefulness is separate. The natural-number result does not name
an instruction, compiler, graph, fuel bound or execution. Trusted registration
must select this spec rather than allowing candidates to weaken its fields. -/
def addition : PureCall.Spec where
  Input := Word × Word
  arguments value index :=
    if index.val = 0 then some (.word64 value.1)
    else if index.val = 1 then some (.word64 value.2) else none
  domain _ := True
  result value result := result.toNat = (value.1.toNat + value.2.toNat) % 2^64
  useful value := value.1 ≠ 0 ∧ value.2 ≠ 0

/-- Full argument bindings, without restricting any other register or flag. -/
theorem bound_iff (value : Word × Word) (state : State) :
    PureCall.Bound addition value state ↔
      state.registers .rdi = value.1 ∧ state.registers .rsi = value.2 := by
  constructor
  · intro bound
    exact ⟨bound 0 (.word64 value.1) rfl, bound 1 (.word64 value.2) rfl⟩
  · rintro ⟨left, right⟩ index argument binding
    simp only [addition] at binding
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

/-- Reverse all eight natural base-256 digits, including zero and all boundary
values. The relation does not select an instruction or assume a future run. -/
def byteSwap : PureCall.Spec where
  Input := Word
  arguments input index :=
    if index.val = 0 then some (.word64 input) else none
  domain _ := True
  result input result := WordMath.ByteReverse64 input result
  useful input :=
    WordMath.base256Digit input.toNat 0 ≠ 0 ∧
      WordMath.base256Digit input.toNat 7 = 0

theorem byteSwap_domain (input : Word) : byteSwap.domain input := trivial

/-- Full64 RDI is the only bound argument; all other state is unconstrained. -/
theorem byteSwap_bound_iff (input : Word) (state : State) :
    PureCall.Bound byteSwap input state ↔ state.registers .rdi = input := by
  constructor
  · intro bound
    exact bound 0 (.word64 input) rfl
  · intro value index argument binding
    simp only [byteSwap] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · contradiction

theorem byteSwap_result_iff (input result : Word) :
    byteSwap.result input result ↔ result = WordMath.byteSwap64 input :=
  WordMath.byteReverse64_iff_eq input result

theorem byteSwap_result_exists_unique (input : Word) :
    ∃ result, byteSwap.result input result ∧
      ∀ other, byteSwap.result input other → other = result :=
  ⟨WordMath.byteSwap64 input, WordMath.byteSwap64_contract input,
    fun _ satisfies => WordMath.byteReverse64_unique satisfies (WordMath.byteSwap64_contract input)⟩

/-- Distinct extreme bytes force a changed result, rather than merely
selecting a nonzero fixture or an instruction shape. -/
theorem byteSwap_useful_changes (input result : Word)
    (useful : byteSwap.useful input) (satisfies : byteSwap.result input result) :
    result ≠ input := by
  intro same
  subst result
  have reversed := satisfies 7 (by decide)
  change WordMath.base256Digit input.toNat 7 = WordMath.base256Digit input.toNat 0 at reversed
  exact useful.1 (reversed.symm.trans useful.2)

end EDSL.Arithmetic64
