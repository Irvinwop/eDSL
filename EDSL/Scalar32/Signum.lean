/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Scalar32.Spec
import EDSL.WordMath.Signum

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Scalar32
open X86

/-- Signed low32 signum on every 32-bit input, including INT32_MIN. Only RDI's
low half is bound. Result upper halves remain unrestricted by this spec; the
result relation depends solely on integer order, independently of code. -/
def signumSigned : PureCall.Spec where
  Input := BitVec 32
  arguments input index :=
    if index.val = 0 then some (.low32 input) else none
  domain _ := True
  result input result := WordMath.Signum input.toInt (result.setWidth 32).toInt
  useful input := input.toInt < -1 ∨ 1 < input.toInt

theorem signum_domain (input : BitVec 32) : signumSigned.domain input := trivial

/-- No other register, flag or upper RDI bit is restricted by argument binding. -/
theorem signum_bound_iff (input : BitVec 32) (state : State) :
    PureCall.Bound signumSigned input state ↔
      (state.registers .rdi).setWidth 32 = input := by
  constructor
  · intro bound
    exact bound 0 (.low32 input) rfl
  · intro value index argument binding
    simp only [signumSigned] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · contradiction

/-- The independent order relation fixes the exact low32 result word. -/
theorem signum_result_iff (input : BitVec 32) (result : Word) :
    signumSigned.result input result ↔
      result.setWidth 32 = WordMath.signum32 input :=
  WordMath.signum32_iff input (result.setWidth 32)

theorem signum_result_exists (input : BitVec 32) :
    ∃ result, signumSigned.result input result := by
  refine ⟨(WordMath.signum32 input).setWidth 64, ?_⟩
  apply (signum_result_iff _ _).mpr
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem signum_result_unique {input : BitVec 32} {first second : Word}
    (left : signumSigned.result input first) (right : signumSigned.result input second) :
    first.setWidth 32 = second.setWidth 32 :=
  BitVec.eq_of_toInt_eq (WordMath.signum_unique left right)

/-- Usefulness selects inputs whose mathematical value actually changes. -/
theorem signum_useful_changes (input : BitVec 32) (result : Word)
    (useful : signumSigned.useful input)
    (satisfies : signumSigned.result input result) :
    result.setWidth 32 ≠ input := by
  intro same
  have bounds := WordMath.signum_bounds satisfies
  rw [same] at bounds
  change input.toInt < -1 ∨ 1 < input.toInt at useful
  omega

end EDSL.Scalar32
