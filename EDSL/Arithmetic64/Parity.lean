/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Parity

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Arithmetic64
open X86

/-- The independent cardinality of the set input bit positions, modulo two.
The sole argument is full64 RDI, every word is in the domain, and the result
constrains only unsigned low32 RAX. Usefulness selects separated high and low
set bits and excludes the all-set word; it never restricts the call domain. -/
def parity64 : PureCall.Spec where
  Input := Word
  arguments input index :=
    if index.val = 0 then some (.word64 input) else none
  domain _ := True
  result input output := (output.setWidth 32).toNat = WordMath.cardinality input % 2
  useful input := input.getLsbD 0 = true ∧ input.getLsbD 63 = true ∧
    WordMath.cardinality input < 64

/-- Full64 RDI is the only argument binding. -/
theorem parity64_bound_iff (input : Word) (state : State) :
    PureCall.Bound parity64 input state ↔ state.registers .rdi = input := by
  constructor
  · intro bound
    exact bound 0 (.word64 input) rfl
  · intro value index argument binding
    simp only [parity64] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · contradiction

theorem parity64_domain (input : Word) : parity64.domain input := trivial

theorem parity64_useful_iff (input : Word) :
    parity64.useful input ↔ input.getLsbD 0 = true ∧ input.getLsbD 63 = true ∧
      WordMath.cardinality input < 64 := Iff.rfl

/-- Both endpoint bits participate in this useful current-call witness. -/
theorem parity64_useful_separated : parity64.useful (0x8000000000000001 : Word) := by
  change (0x8000000000000001 : Word).getLsbD 0 = true ∧
    (0x8000000000000001 : Word).getLsbD 63 = true ∧
    WordMath.cardinality (0x8000000000000001 : Word) < 64
  decide +kernel

/-- The result fixes exactly the low32 parity value. -/
theorem parity64_result_iff (input output : Word) :
    parity64.result input output ↔
      output.setWidth 32 = BitVec.ofNat 32 (WordMath.cardinality input % 2) := by
  change (output.setWidth 32).toNat = WordMath.cardinality input % 2 ↔ _
  have bound : WordMath.cardinality input % 2 < 2 ^ 32 := by
    have := Nat.mod_lt (WordMath.cardinality input) (by decide : 0 < 2)
    omega
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

/-- Natural representability supplies a result without an execution premise. -/
theorem parity64_result_exists (input : Word) :
    ∃ output : Word, parity64.result input output := by
  refine ⟨BitVec.ofNat 64 (WordMath.cardinality input % 2), ?_⟩
  apply (parity64_result_iff input _).mpr
  simp

theorem parity64_result_low32_unique {input left right : Word}
    (leftResult : parity64.result input left) (rightResult : parity64.result input right) :
    left.setWidth 32 = right.setWidth 32 :=
  BitVec.eq_of_toNat_eq (leftResult.trans rightResult.symm)

/-- Any upper32 is compatible with a specified low32 result. -/
theorem parity64_result_upper32 (input output : Word) (upper : BitVec 32)
    (correct : parity64.result input output) :
    parity64.result input (upper ++ output.setWidth 32) := by
  change ((upper ++ output.setWidth 32).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact correct

/-- Every zero-remaining mathematical invariant gives the specified low32
return, without assumptions on the original input or a machine execution. -/
theorem parity64_result_of_invariant {input remaining accumulator : Word}
    (invariant : WordMath.ParityInvariant input remaining accumulator.toNat)
    (done : remaining = 0#64) : parity64.result input accumulator :=
  WordMath.parityInvariant_finish_low32 invariant done

/-- A low32 XOR with the remaining input's low bit preserves the independent
cardinality invariant. The input remains full64 throughout the shift. -/
theorem parity64_step32 {input remaining : Word} {accumulator : BitVec 32}
    (invariant : WordMath.ParityInvariant input remaining accumulator.toNat) :
    WordMath.ParityInvariant input (remaining >>> 1)
      (accumulator ^^^ (remaining.setWidth 32 &&& 1#32)).toNat := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  simpa [WordMath.lowBit] using
    (WordMath.parityInvariant_step_word (a := 32) (by decide) invariant)

end EDSL.Arithmetic64
