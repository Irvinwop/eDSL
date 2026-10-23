/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Multiplication

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Arithmetic64
open X86

/-- Unsigned multiplication modulo 2^64 for every pair of full64 arguments.
The result is the residue of their unbounded natural product. This independent
specification selects no instruction, compiler, code bytes or execution model.
Usefulness selects nonzero inputs whose natural product wraps, separately from
the universal admission domain. -/
def multiplyModulo : PureCall.Spec where
  Input := Word × Word
  arguments value index :=
    if index.val = 0 then some (.word64 value.1)
    else if index.val = 1 then some (.word64 value.2) else none
  domain _ := True
  result value output := WordMath.MulModulo value.1 value.2 output
  useful value := value.1 ≠ 0 ∧ value.2 ≠ 0 ∧
    2^64 ≤ value.1.toNat * value.2.toNat

/-- Only full64 RDI and RSI are bound. All other registers and flags remain
arbitrary at the argument-binding layer. -/
theorem multiplyModulo_bound_iff (value : Word × Word) (state : State) :
    PureCall.Bound multiplyModulo value state ↔
      state.registers .rdi = value.1 ∧ state.registers .rsi = value.2 := by
  constructor
  · intro bound
    exact ⟨bound 0 (.word64 value.1) rfl, bound 1 (.word64 value.2) rfl⟩
  · rintro ⟨left, right⟩ index argument binding
    simp only [multiplyModulo] at binding
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

theorem multiplyModulo_domain (value : Word × Word) : multiplyModulo.domain value := trivial

theorem multiplyModulo_result_iff (value : Word × Word) (output : Word) :
    multiplyModulo.result value output ↔
      output.toNat = (value.1.toNat * value.2.toNat) % 2^64 := Iff.rfl

/-- Mathematical existence and uniqueness require no machine execution. -/
theorem multiplyModulo_result_exists_unique (value : Word × Word) :
    ∃ output, multiplyModulo.result value output ∧
      ∀ other, multiplyModulo.result value other → other = output :=
  WordMath.mulModulo_exists_unique value.1 value.2

/-- The shared callable postcondition binds the modular result to full64 RAX. -/
theorem multiplyModulo_post_result {input : PureCall.Invocation multiplyModulo}
    {initial final : State} (post : PureCall.Post multiplyModulo input initial final) :
    WordMath.MulModulo input.value.1 input.value.2 (final.registers .rax) :=
  post.result

end EDSL.Arithmetic64
