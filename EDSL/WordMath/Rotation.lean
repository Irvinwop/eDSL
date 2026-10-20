/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init

set_option autoImplicit false
set_option warningAsError true

/-!
Rotate left specified as a permutation of least-significant-bit positions.
The count is an arbitrary natural, reduced modulo the word width; inputs
have no high-bit restriction. The specification contains no shifts or calls
to `BitVec.rotateLeft`. Its implementation theorem uses Init's bit lemmas.

At width zero there are no bit positions, the specification is vacuous, and
the only possible result is the empty word. No machine, ABI, compiler,
resource, or operating-system assumptions occur in these results.
-/

namespace EDSL.WordMath

/-- Origin of output position `i` under rotate left. For `i < width`, adding
the width before natural subtraction expresses `(i - count % width) mod width`
with wraparound, rather than truncating a negative difference to zero. -/
def rotationOrigin (width count i : Nat) : Nat :=
  (i + width - count % width) % width

/-- Every actual output bit has an actual input origin. -/
theorem rotationOrigin_lt {width count i : Nat} (hi : i < width) :
    rotationOrigin width count i < width :=
  Nat.mod_lt _ (by omega)

/-- The natural formula is exactly mathematical modular subtraction, even
when the unreduced difference is negative. Width is positive because `i` exists. -/
theorem rotationOrigin_eq_int_mod {width count i : Nat} (hi : i < width) :
    (rotationOrigin width count i : Int) =
      ((i : Int) - ↑(count % width)) % (width : Int) := by
  have hc := Nat.mod_lt count (Nat.zero_lt_of_lt hi)
  unfold rotationOrigin
  rw [Int.natCast_emod, Int.natCast_sub (by omega), Int.natCast_add]
  have h : (i : Int) + (width : Int) - ↑(count % width) =
      ((i : Int) - ↑(count % width)) + (width : Int) := by omega
  rw [h, Int.add_emod_right]

/-- Piecewise form of wrapped subtraction, including the boundary count zero. -/
theorem rotationOrigin_eq {width count i : Nat} (hi : i < width) :
    rotationOrigin width count i =
      if i < count % width then width - count % width + i
      else i - count % width := by
  have hc := Nat.mod_lt count (by omega : 0 < width)
  unfold rotationOrigin
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have h : i + width - count % width = (i - count % width) + width := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Moving an origin forward by the effective count recovers its output bit. -/
theorem rotationOrigin_forward {width count i : Nat} (hi : i < width) :
    (rotationOrigin width count i + count % width) % width = i := by
  have hc := Nat.mod_lt count (by omega : 0 < width)
  rw [rotationOrigin_eq hi]
  split
  · have h : width - count % width + i + count % width = i + width := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h : i - count % width + count % width = i := by omega
    rw [h, Nat.mod_eq_of_lt hi]

/-- Each input bit is the origin of the position obtained by moving it forward. -/
theorem rotationOrigin_backward {width count j : Nat} (hj : j < width) :
    rotationOrigin width count ((j + count % width) % width) = j := by
  have hw : 0 < width := by omega
  have hc := Nat.mod_lt count hw
  by_cases h : j + count % width < width
  · rw [Nat.mod_eq_of_lt h, rotationOrigin_eq h]
    simp only [show ¬j + count % width < count % width by omega, ↓reduceIte]
    omega
  · have hm : (j + count % width) % width = j + count % width - width := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm, rotationOrigin_eq (by omega)]
    simp only [show j + count % width - width < count % width by omega, ↓reduceIte]
    omega

/-- The bit-origin map on the genuine positions of a word. At width zero its
domain is empty; no modulo-zero interpretation of a bit position is needed. -/
def rotationOriginIndex {width : Nat} (count : Nat) (i : Fin width) : Fin width :=
  ⟨rotationOrigin width count i.val, rotationOrigin_lt i.isLt⟩

/-- Rotation neither duplicates nor discards bit positions. -/
theorem rotationOriginIndex_injective {width : Nat} (count : Nat) :
    Function.Injective (rotationOriginIndex (width := width) count) := by
  intro i j h
  have he := congrArg Fin.val h
  have hi := rotationOrigin_forward (count := count) i.isLt
  have hj := rotationOrigin_forward (count := count) j.isLt
  change rotationOrigin width count i.val = rotationOrigin width count j.val at he
  rw [he] at hi
  exact Fin.ext (hi.symm.trans hj)

/-- Every input position occurs as an output's origin. -/
theorem rotationOriginIndex_surjective {width : Nat} (count : Nat) :
    Function.Surjective (rotationOriginIndex (width := width) count) := by
  intro j
  refine ⟨⟨(j.val + count % width) % width,
    Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩, ?_⟩
  exact Fin.ext (rotationOrigin_backward j.isLt)

/-- Independent rotate-left relation: every output bit equals its specified
input origin. There is no bound on the natural count or the input high bits. -/
def IsRotateLeft {width : Nat} (input : BitVec width) (count : Nat)
    (output : BitVec width) : Prop :=
  ∀ i, i < width → output.getLsbD i = input.getLsbD (rotationOrigin width count i)

/-- The relation depends only on the count modulo the width. -/
theorem isRotateLeft_mod_iff {width : Nat} (input output : BitVec width) (count : Nat) :
    IsRotateLeft input (count % width) output ↔ IsRotateLeft input count output := by
  simp only [IsRotateLeft, rotationOrigin, Nat.mod_mod]

/-- Equivalently, each input bit moves forward by the effective count. This
characterization also holds for the empty permutation at width zero. -/
theorem isRotateLeft_iff_forward {width : Nat}
    (input output : BitVec width) (count : Nat) :
    IsRotateLeft input count output ↔
      ∀ j, j < width →
        output.getLsbD ((j + count % width) % width) = input.getLsbD j := by
  constructor
  · intro h j hj
    have hb := h ((j + count % width) % width)
      (Nat.mod_lt _ (Nat.zero_lt_of_lt hj))
    rw [rotationOrigin_backward hj] at hb
    exact hb
  · intro h i hi
    have hb := h (rotationOrigin width count i) (rotationOrigin_lt (count := count) hi)
    rw [rotationOrigin_forward hi] at hb
    exact hb

/-- Init's rotate-left operation has exactly the independently specified origin
at every output bit. This includes all counts and the empty-width case. -/
theorem rotateLeft_satisfies {width : Nat} (input : BitVec width) (count : Nat) :
    IsRotateLeft input count (input.rotateLeft count) := by
  intro i hi
  rw [BitVec.getLsbD_rotateLeft, rotationOrigin_eq hi]
  split <;> simp only [hi, decide_true, Bool.true_and]

/-- Bit extensionality makes the independent relation single-valued. -/
theorem isRotateLeft_unique {width count : Nat} {input output₁ output₂ : BitVec width}
    (h₁ : IsRotateLeft input count output₁) (h₂ : IsRotateLeft input count output₂) :
    output₁ = output₂ := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (h₁ i hi).trans (h₂ i hi).symm

/-- Existence and uniqueness for every width and every natural count. -/
theorem isRotateLeft_exists_unique {width : Nat} (input : BitVec width) (count : Nat) :
    ∃ output, IsRotateLeft input count output ∧
      ∀ other, IsRotateLeft input count other → other = output :=
  ⟨input.rotateLeft count, rotateLeft_satisfies input count,
    fun _ h => isRotateLeft_unique h (rotateLeft_satisfies input count)⟩

/-- A convenient bridge from an independent scalar specification to Init. -/
theorem isRotateLeft_iff_eq_rotateLeft {width : Nat}
    (input output : BitVec width) (count : Nat) :
    IsRotateLeft input count output ↔ output = input.rotateLeft count := by
  constructor
  · exact fun h => isRotateLeft_unique h (rotateLeft_satisfies input count)
  · intro h
    rw [h]
    exact rotateLeft_satisfies input count

/-- At width zero there are no positions to constrain. -/
theorem isRotateLeft_zero_width (input output : BitVec 0) (count : Nat) :
    IsRotateLeft input count output := by
  intro i hi
  omega

/-- The empty word is the unique implementation result, for every count. -/
theorem rotateLeft_zero_width (input : BitVec 0) (count : Nat) :
    input.rotateLeft count = 0 :=
  Subsingleton.elim _ _

/-- Full64 scalar relation, with an arbitrary natural count modulo 64. -/
abbrev IsRotateLeft64 (input : BitVec 64) (count : Nat) (output : BitVec 64) : Prop :=
  IsRotateLeft input count output

/-- Explicit full64 bit-origin contract for later scalar specifications. -/
theorem isRotateLeft64_iff (input output : BitVec 64) (count : Nat) :
    IsRotateLeft64 input count output ↔
      ∀ i, i < 64 → output.getLsbD i = input.getLsbD ((i + 64 - count % 64) % 64) :=
  Iff.rfl

/-- Init rotate left satisfies the full64 scalar relation for all inputs/counts. -/
theorem rotateLeft64_satisfies (input : BitVec 64) (count : Nat) :
    IsRotateLeft64 input count (input.rotateLeft count) :=
  rotateLeft_satisfies input count

/-- Every output bit of full64 rotate left has its row09 mathematical origin.
Counts zero, one, 63, 64, 65, and arbitrarily large naturals need no cases. -/
theorem rotateLeft64_getLsbD (input : BitVec 64) (count i : Nat) (hi : i < 64) :
    (input.rotateLeft count).getLsbD i =
      input.getLsbD ((i + 64 - count % 64) % 64) :=
  rotateLeft64_satisfies input count i hi

end EDSL.WordMath
