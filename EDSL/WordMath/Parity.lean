/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.Popcount

set_option autoImplicit false
set_option warningAsError true

/-!
Parity facts derived from the independent set-bit `cardinality`, not from a
shift-loop evaluator. Unsigned shifts use the natural count one. Arbitrary
input widths, including zero, and all input values are admitted.

The accumulator invariant records an exact natural 0/1 bound. Word bridges
state their representation premises explicitly. No machine, instruction,
execution, compiler, resource, or environmental assumptions occur here.
-/

namespace EDSL.WordMath

/-- The least significant bit, false for the unique width-zero word. -/
def lowBit {w : Nat} (x : BitVec w) : Bool := x.getLsbD 0

@[simp] theorem lowBit_zero (w : Nat) : lowBit (0#w) = false := by
  simp [lowBit]

/-- Widening a word with zeroes preserves its set-bit cardinality. -/
theorem cardinality_setWidth_of_le {w v : Nat} (x : BitVec w) (h : w ≤ v) :
    cardinality (x.setWidth v) = cardinality x := by
  simp only [cardinality, BitVec.cpopNatRec_setWidth_of_le x (Nat.le_refl v)]
  have sum : w + (v - w) = v := by omega
  simpa only [sum] using
    (BitVec.cpopNatRec_of_le (x := x) (acc := 0) (v - w) w (Nat.le_refl w))

/-- Removing the low bit splits the independent set-bit cardinality exactly.
The shift retains the original width and fills its high bit with zero. -/
theorem cardinality_shiftRight_one {w : Nat} (x : BitVec w) :
    cardinality x = (lowBit x).toNat + cardinality (x >>> 1) := by
  induction x using BitVec.concat_induction with
  | nil => simp [lowBit, cardinality]
  | @concat w x b _ =>
    have shifted : x.concat b >>> 1 = x.setWidth (w + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_concat, BitVec.toNat_setWidth_of_le (by omega)]
      have bit_bound := Bool.toNat_lt b
      simp only [Nat.pow_one]
      omega
    rw [cardinality_concat, shifted, cardinality_setWidth_of_le x (by omega)]
    simp [lowBit]

/-- A nonzero word strictly descends in natural value after an unsigned shift.
At width zero the premise is impossible; no positive-width premise is hidden. -/
theorem shiftRight_one_toNat_lt {w : Nat} (x : BitVec w) (hnz : x ≠ 0#w) :
    (x >>> 1).toNat < x.toNat := by
  have positive : 0 < x.toNat := by
    have nonzero : x.toNat ≠ 0 := by
      intro h
      exact hnz (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self positive (by decide)

/-- XOR of natural 0/1 values is addition modulo two. -/
theorem xor_bits_eq_add_mod_two {a b : Nat} (ha : a < 2) (hb : b < 2) :
    a ^^^ b = (a + b) % 2 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

/-- The accumulator is 0 or 1 and, together with the remaining set bits,
has the same parity as the initial input. All addition here is natural. -/
def ParityInvariant {w : Nat} (initial remaining : BitVec w)
    (accumulator : Nat) : Prop :=
  accumulator < 2 ∧
    (accumulator + cardinality remaining) % 2 = cardinality initial % 2

theorem parityInvariant_start {w : Nat} (initial : BitVec w) :
    ParityInvariant initial initial 0 := by
  simp [ParityInvariant]

/-- XOR with the low bit and unsigned right shift preserve the invariant.
A nonzero premise is unnecessary for preservation, even at width zero. -/
theorem parityInvariant_step {w : Nat} {initial remaining : BitVec w}
    {accumulator : Nat} (invariant : ParityInvariant initial remaining accumulator) :
    ParityInvariant initial (remaining >>> 1)
      (accumulator ^^^ (lowBit remaining).toNat) := by
  rcases invariant with ⟨bound, invariant⟩
  have bit_bound := Bool.toNat_lt (lowBit remaining)
  constructor
  · exact Nat.xor_lt_two_pow (n := 1) bound bit_bound
  · rw [xor_bits_eq_add_mod_two bound bit_bound, Nat.mod_add_mod,
      Nat.add_assoc, ← cardinality_shiftRight_one]
    exact invariant

theorem parityInvariant_finish {w : Nat} {initial remaining : BitVec w}
    {accumulator : Nat} (invariant : ParityInvariant initial remaining accumulator)
    (done : remaining = 0#w) : accumulator = cardinality initial % 2 := by
  rcases invariant with ⟨bound, invariant⟩
  simpa [done, Nat.mod_eq_of_lt bound] using invariant

/-- A positive-width word represents a Boolean bit exactly. Width zero would
lose a true bit, so it is explicitly excluded from this representation bridge. -/
theorem toNat_lowBit_word {w a : Nat} (x : BitVec w) (positive : 0 < a) :
    ((BitVec.ofBool (lowBit x)).setWidth a).toNat = (lowBit x).toNat := by
  simpa only [BitVec.toNat_ofBool] using
    (BitVec.toNat_setWidth_of_le (b := BitVec.ofBool (lowBit x)) (by omega : 1 ≤ a))

/-- The same invariant step for an arbitrary positive-width word accumulator.
Its 0/1 bound is supplied by the invariant, independently of the input width. -/
theorem parityInvariant_step_word {w a : Nat} {initial remaining : BitVec w}
    {accumulator : BitVec a} (positive : 0 < a)
    (invariant : ParityInvariant initial remaining accumulator.toNat) :
    ParityInvariant initial (remaining >>> 1)
      (accumulator ^^^ (BitVec.ofBool (lowBit remaining)).setWidth a).toNat := by
  rw [BitVec.toNat_xor, toNat_lowBit_word remaining positive]
  exact parityInvariant_step invariant

/-- At zero remaining, the low 32 bits of any word accumulator are the exact
natural parity. Its invariant already guarantees that narrowing cannot wrap. -/
theorem parityInvariant_finish_low32 {w a : Nat} {initial remaining : BitVec w}
    {accumulator : BitVec a}
    (invariant : ParityInvariant initial remaining accumulator.toNat)
    (done : remaining = 0#w) :
    (accumulator.setWidth 32).toNat = cardinality initial % 2 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := invariant.1; omega)]
  exact parityInvariant_finish invariant done

end EDSL.WordMath
