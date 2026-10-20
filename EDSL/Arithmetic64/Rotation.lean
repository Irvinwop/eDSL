/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Rotation

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Arithmetic64
open X86

/-- Full64 rotate left by an unsigned low32 count. The independent bit-origin
relation reduces every count modulo 64; all values and counts are admitted.
No instruction, compiler or successful execution occurs in this contract. -/
def rotateLeft : PureCall.Spec where
  Input := Word × BitVec 32
  arguments value index :=
    if index.val = 0 then some (.word64 value.1)
    else if index.val = 1 then some (.low32 value.2) else none
  domain _ := True
  result value output := WordMath.IsRotateLeft64 value.1 value.2.toNat output
  useful value := value.1 = 0x8123456789abcdef ∧ value.2 = 4

/-- Only full64 RDI and low32 RSI are bound. In particular the upper half of
RSI, every unbound register and all incoming flags remain arbitrary. -/
theorem rotateLeft_bound_iff (value : Word × BitVec 32) (state : State) :
    PureCall.Bound rotateLeft value state ↔
      state.registers .rdi = value.1 ∧ (state.registers .rsi).setWidth 32 = value.2 := by
  constructor
  · intro bound
    exact ⟨bound 0 (.word64 value.1) rfl, bound 1 (.low32 value.2) rfl⟩
  · rintro ⟨left, count⟩ index argument binding
    simp only [rotateLeft] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact left
    · split at binding
      · have one : index = 1 := Fin.ext (by assumption)
        subst index
        cases binding
        exact count
      · contradiction

theorem rotateLeft_domain (value : Word × BitVec 32) : rotateLeft.domain value := trivial

theorem rotateLeft_result_iff (value : Word × BitVec 32) (output : Word) :
    rotateLeft.result value output ↔
      ∀ i, i < 64 → output.getLsbD i =
        value.1.getLsbD ((i + 64 - value.2.toNat % 64) % 64) := Iff.rfl

/-- Mathematical representability and uniqueness require no machine premise. -/
theorem rotateLeft_result_exists_unique (value : Word × BitVec 32) :
    ∃ output, rotateLeft.result value output ∧
      ∀ other, rotateLeft.result value other → other = output :=
  WordMath.isRotateLeft_exists_unique value.1 value.2.toNat

/-- A useful high-bit/wraparound example selects only an existential witness;
it never restricts the universal domain. -/
theorem rotateLeft_useful_wraparound :
    rotateLeft.useful ((0x8123456789abcdef, 4) : Word × BitVec 32) := ⟨rfl, rfl⟩

end EDSL.Arithmetic64
