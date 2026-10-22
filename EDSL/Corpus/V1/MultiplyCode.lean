/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Multiplication
import EDSL.X86.VCGen.CompilerComparisons

set_option autoImplicit false
set_option warningAsError true

/-! Candidate bytes and the independent full64 modular-product contract for
`c_mul_mod64`. File binding and execution require separate evidence. -/

namespace EDSL.Corpus.V1.MultiplyCode
open X86

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

/-- Complete unchanged default-compiler symbol extents. GCC retains its
original ENDBR64; its modeled behavior requires the recorded CET-off target.
Literal candidates alone establish neither decoding nor behavior. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x0f,0xaf,0xc6,0xc3]
  | .defaultClang => [0x48,0x89,0xf8,0x48,0x0f,0xaf,0xc6,0xc3]

/-- Every pair of full64 arguments is admitted. The result is the residue of
their unbounded natural product; it names no compiler, instruction, flags,
execution or successful future run. `PureCall.Post` observes the result in
full64 RAX. Usefulness selects nonzero inputs whose natural product wraps,
separately from the universal admission domain. -/
def spec : PureCall.Spec where
  Input := Word × Word
  arguments value index :=
    if index.val = 0 then some (.word64 value.1)
    else if index.val = 1 then some (.word64 value.2) else none
  domain _ := True
  result value output := WordMath.MulModulo value.1 value.2 output
  useful value := value.1 ≠ 0 ∧ value.2 ≠ 0 ∧
    2^64 ≤ value.1.toNat * value.2.toNat

theorem domain (value : Word × Word) : spec.domain value := trivial

/-- Only full64 RDI and RSI are bound; all other registers and flags remain
arbitrary at this argument-binding layer. -/
theorem bound_iff (value : Word × Word) (state : State) :
    PureCall.Bound spec value state ↔
      state.registers .rdi = value.1 ∧ state.registers .rsi = value.2 := by
  constructor
  · intro bound
    exact ⟨bound 0 (.word64 value.1) rfl, bound 1 (.word64 value.2) rfl⟩
  · rintro ⟨left, right⟩ index argument binding
    simp only [spec] at binding
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

theorem result_iff (value : Word × Word) (output : Word) :
    spec.result value output ↔
      output.toNat = (value.1.toNat * value.2.toNat) % 2^64 := Iff.rfl

/-- Mathematical existence and uniqueness, independent of machine execution. -/
theorem result_exists_unique (value : Word × Word) :
    ∃ output, spec.result value output ∧
      ∀ other, spec.result value other → other = output :=
  WordMath.mulModulo_exists_unique value.1 value.2

/-- The shared callable postcondition binds the modular result to full64 RAX. -/
theorem post_result {input : PureCall.Invocation spec} {initial final : State}
    (post : PureCall.Post spec input initial final) :
    WordMath.MulModulo input.value.1 input.value.2 (final.registers .rax) :=
  post.result

#print axioms bound_iff
#print axioms result_iff
#print axioms result_exists_unique
#print axioms post_result
end EDSL.Corpus.V1.MultiplyCode
