/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init.Data.BitVec

/-!
Shared, independent integer and word mathematics.
No instruction, flag-state, decoder, executor, ABI, or corpus registration is
defined here. `selectSign32` is just a Boolean choice on two words.
-/

namespace EDSL.WordMath

/-- Independent mathematical absolute-value contract, over unbounded integers. -/
def AbsSquare (input result : Int) : Prop :=
  0 ≤ result ∧ result * result = input * input

theorem nonnegative_square_unique {a b : Int}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsq : a * a = b * b) : a = b := by
  have hab : ¬ a < b := by
    intro h
    have := Int.mul_self_lt_mul_self ha h
    omega
  have hba : ¬ b < a := by
    intro h
    have := Int.mul_self_lt_mul_self hb h
    omega
  omega

theorem absSquare_unique {x a b : Int}
    (ha : AbsSquare x a) (hb : AbsSquare x b) : a = b :=
  nonnegative_square_unique ha.1 hb.1 (ha.2.trans hb.2.symm)

theorem absSquare_natAbs (x : Int) : AbsSquare x (x.natAbs : Int) := by
  constructor
  · omega
  · exact Int.natAbs_mul_self' x

theorem absSquare_iff_natAbs (x y : Int) :
    AbsSquare x y ↔ y = (x.natAbs : Int) := by
  constructor
  · intro h
    exact absSquare_unique h (absSquare_natAbs x)
  · rintro rfl
    exact absSquare_natAbs x

theorem absSquare_exists_unique (x : Int) :
    ∃ y : Int, AbsSquare x y ∧ ∀ z : Int, AbsSquare x z → z = y :=
  ⟨x.natAbs, absSquare_natAbs x, fun _ h => absSquare_unique h (absSquare_natAbs x)⟩

/-- The signed minimum has no representable nonnegative signed absolute value. -/
theorem intMin32_toInt : (BitVec.intMin 32).toInt = -2147483648 := by decide

theorem eq_intMin32_iff (x : BitVec 32) :
    x = BitVec.intMin 32 ↔ x.toInt = -2147483648 := by
  rw [← intMin32_toInt, BitVec.toInt_inj]

theorem signed32_bounds (x : BitVec 32) :
    -2147483648 ≤ x.toInt ∧ x.toInt < 2147483648 := by
  constructor
  · simpa using BitVec.le_toInt x
  · simpa using (BitVec.toInt_lt (x := x))

/-- Modular unsigned negation, including zero and the signed minimum. -/
theorem neg32_toNat (x : BitVec 32) :
    (-x).toNat = (4294967296 - x.toNat) % 4294967296 := by
  exact BitVec.toNat_neg x

theorem neg32_modular_cancel (x : BitVec 32) :
    (x.toNat + (-x).toNat) % 4294967296 = 0 := by
  have h := congrArg BitVec.toNat (BitVec.add_right_neg x)
  simpa using h

theorem neg32_eq_ofInt (x : BitVec 32) :
    -x = BitVec.ofInt 32 (-x.toInt) := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_toInt]

theorem neg32_toInt (x : BitVec 32) :
    (-x).toInt = if x.toInt = -2147483648 then x.toInt else -x.toInt := by
  simpa only [eq_intMin32_iff] using (BitVec.toInt_neg_eq_ite (x := x))

theorem neg32_toInt_of_ne_min (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    (-x).toInt = -x.toInt := by
  simp [neg32_toInt, hmin]

theorem sign32 (x : BitVec 32) : x.msb = decide (x.toInt < 0) :=
  BitVec.msb_eq_toInt

theorem sign32_false_iff (x : BitVec 32) : x.msb = false ↔ 0 ≤ x.toInt := by
  simp only [sign32, decide_eq_false_iff_not]
  omega

/-- The sign bit of a negation tests strict positivity, away from INT32_MIN. -/
theorem neg32_sign (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    (-x).msb = decide (0 < x.toInt) := by
  rw [sign32, neg32_toInt_of_ne_min x hmin]
  simp only [Int.neg_lt_zero_iff]

/-- Complete sign rule: the exceptional minimum retains its negative sign. -/
theorem neg32_sign_full (x : BitVec 32) :
    (-x).msb = decide (x.toInt = -2147483648 ∨ 0 < x.toInt) := by
  rw [sign32, neg32_toInt]
  by_cases h : x.toInt = -2147483648
  · simp [h]
  · simp only [h, ↓reduceIte, false_or]
    simp only [Int.neg_lt_zero_iff]

/-- Pure Boolean selection, independently of instruction or flag semantics. -/
def selectSign32 (sign : Bool) (destination source : BitVec 32) : BitVec 32 :=
  if sign then source else destination

theorem selectSign32_of_negative (tested destination source : BitVec 32)
    (h : tested.toInt < 0) : selectSign32 tested.msb destination source = source := by
  simp [selectSign32, sign32, h]

theorem selectSign32_of_nonnegative (tested destination source : BitVec 32)
    (h : 0 ≤ tested.toInt) : selectSign32 tested.msb destination source = destination := by
  simp [selectSign32, sign32, show ¬ tested.toInt < 0 by omega]

/-- Algebraic NEG-result / original-input selection, without machine state. -/
def negSelect32 (x : BitVec 32) : BitVec 32 :=
  selectSign32 (-x).msb (-x) x

theorem negSelect32_toInt (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    (negSelect32 x).toInt = if x.toInt < 0 then -x.toInt else x.toInt := by
  by_cases hp : 0 < x.toInt
  · simp [negSelect32, selectSign32, neg32_sign x hmin, hp,
      show ¬ x.toInt < 0 by omega]
  · by_cases hn : x.toInt < 0
    · simp [negSelect32, selectSign32, neg32_sign x hmin, hp, hn,
        neg32_toInt_of_ne_min x hmin]
    · have hz : x.toInt = 0 := by omega
      simp [negSelect32, selectSign32, neg32_sign x hmin, hz,
        neg32_toInt_of_ne_min x hmin]

theorem negSelect32_contract (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    AbsSquare x.toInt (negSelect32 x).toInt := by
  rw [AbsSquare, negSelect32_toInt x hmin]
  by_cases hn : x.toInt < 0
  · simp only [hn, ↓reduceIte, Int.neg_mul_neg, and_true]
    omega
  · simp only [hn, ↓reduceIte, and_true]
    omega

theorem negSelect32_bounds (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    0 ≤ (negSelect32 x).toInt ∧ (negSelect32 x).toInt ≤ 2147483647 := by
  have hc := negSelect32_contract x hmin
  have hb := signed32_bounds (negSelect32 x)
  exact ⟨hc.1, by omega⟩

theorem negSelect32_unique (x : BitVec 32) (hmin : x.toInt ≠ -2147483648)
    (y : Int) (hy : AbsSquare x.toInt y) : y = (negSelect32 x).toInt :=
  absSquare_unique hy (negSelect32_contract x hmin)

theorem negSelect32_toInt_natAbs (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    (negSelect32 x).toInt = (x.toInt.natAbs : Int) :=
  (absSquare_iff_natAbs _ _).mp (negSelect32_contract x hmin)

theorem negSelect32_msb (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    (negSelect32 x).msb = false :=
  (sign32_false_iff _).mpr (negSelect32_contract x hmin).1

theorem negSelect32_toNat_natAbs (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    (negSelect32 x).toNat = x.toInt.natAbs := by
  have h := negSelect32_toInt_natAbs x hmin
  rw [BitVec.toInt_eq_toNat_of_msb (negSelect32_msb x hmin)] at h
  exact Int.ofNat_inj.mp h

theorem negSelect32_eq_abs (x : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    negSelect32 x = x.abs := by
  apply BitVec.eq_of_toInt_eq
  rw [negSelect32_toInt_natAbs x hmin,
    BitVec.toInt_abs_eq_natAbs_of_ne_intMin (fun h => hmin ((eq_intMin32_iff x).mp h))]

/-- A word satisfies the independent contract iff it is the selected word. -/
theorem absSquare32_iff (x y : BitVec 32) (hmin : x.toInt ≠ -2147483648) :
    AbsSquare x.toInt y.toInt ↔ y = negSelect32 x := by
  constructor
  · intro h
    exact BitVec.eq_of_toInt_eq (negSelect32_unique x hmin y.toInt h)
  · rintro rfl
    exact negSelect32_contract x hmin

/-- The excluded input has no representable signed 32-bit result at all. -/
theorem intMin32_no_result (y : BitVec 32) :
    ¬ AbsSquare (BitVec.intMin 32).toInt y.toInt := by
  intro h
  have hu := (absSquare_iff_natAbs _ _).mp h
  rw [intMin32_toInt] at hu
  have hb := signed32_bounds y
  have hv : ((-2147483648 : Int).natAbs : Int) = 2147483648 := by decide
  rw [hv] at hu
  omega

/-! Bytes are numbered from the least significant byte (lane zero). -/

/-- Natural base-256 digit; independent of any bitvector byte-swap construction. -/
def base256Digit (value index : Nat) : Nat := value / 256 ^ index % 256

/-- An eight-bit lane, zero-extended when its starting offset is outside the word. -/
def byte64 (x : BitVec 64) (index : Nat) : BitVec 8 :=
  x.extractLsb' (8 * index) 8

theorem byte64_toNat (x : BitVec 64) (i : Nat) :
    (byte64 x i).toNat = base256Digit x.toNat i := by
  simp only [byte64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, base256Digit]
  have hp : (256 : Nat) ^ i = 2 ^ (8 * i) := by
    rw [Nat.pow_mul]
  rw [hp]

/-- Each output base-256 digit is the reversed input digit. -/
def ByteReverse64 (input output : BitVec 64) : Prop :=
  ∀ i : Nat, i < 8 → base256Digit output.toNat i = base256Digit input.toNat (7 - i)

/-- Explicit permutation of eight whole lanes; the bits within a lane retain order. -/
def byteSwap64 (x : BitVec 64) : BitVec 64 :=
  byte64 x 0 ++ (byte64 x 1 ++ (byte64 x 2 ++ (byte64 x 3 ++
    (byte64 x 4 ++ (byte64 x 5 ++ (byte64 x 6 ++ byte64 x 7))))))

theorem byteSwap64_lane (x : BitVec 64) (i : Nat) (hi : i < 8) :
    byte64 (byteSwap64 x) i = byte64 x (7 - i) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases cases with h | h | h | h | h | h | h | h <;> subst i
  all_goals
    simp only [byte64, byteSwap64]
    repeat (rw [BitVec.extractLsb'_append_eq_ite]; simp)

theorem byteSwap64_contract (x : BitVec 64) : ByteReverse64 x (byteSwap64 x) := by
  intro i hi
  rw [← byte64_toNat, ← byte64_toNat, byteSwap64_lane x i hi]

theorem byte64_bit (x : BitVec 64) (i j : Nat) (hj : j < 8) :
    (byte64 x i).getLsbD j = x.getLsbD (8 * i + j) := by
  simp [byte64, hj]

theorem byte64_ext {x y : BitVec 64}
    (h : ∀ i : Nat, i < 8 → byte64 x i = byte64 y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : k / 8 < 8 := by omega
  have hj : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hh := congrArg (fun b : BitVec 8 => b.getLsbD (k % 8)) (h (k / 8) hi)
  rw [byte64_bit x _ _ hj, byte64_bit y _ _ hj] at hh
  have he : 8 * (k / 8) + k % 8 = k := by omega
  simpa only [he] using hh

theorem byteReverse64_iff_lanes (x y : BitVec 64) :
    ByteReverse64 x y ↔ ∀ i : Nat, i < 8 → byte64 y i = byte64 x (7 - i) := by
  constructor
  · intro h i hi
    apply BitVec.eq_of_toNat_eq
    simpa only [byte64_toNat] using h i hi
  · intro h i hi
    simpa only [byte64_toNat] using congrArg BitVec.toNat (h i hi)

theorem byteReverse64_unique {x y z : BitVec 64}
    (hy : ByteReverse64 x y) (hz : ByteReverse64 x z) : y = z := by
  apply byte64_ext
  intro i hi
  exact ((byteReverse64_iff_lanes x y).mp hy i hi).trans
    ((byteReverse64_iff_lanes x z).mp hz i hi).symm

theorem byteReverse64_iff_eq (x y : BitVec 64) :
    ByteReverse64 x y ↔ y = byteSwap64 x := by
  constructor
  · intro h
    exact byteReverse64_unique h (byteSwap64_contract x)
  · rintro rfl
    exact byteSwap64_contract x

theorem byteSwap64_bit (x : BitVec 64) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * i + j) = x.getLsbD (8 * (7 - i) + j) := by
  rw [← byte64_bit _ i j hj, byteSwap64_lane x i hi, byte64_bit _ _ j hj]

theorem byteSwap64_involution (x : BitVec 64) : byteSwap64 (byteSwap64 x) = x := by
  apply byte64_ext
  intro i hi
  have hr : 7 - i < 8 := by omega
  rw [byteSwap64_lane _ i hi, byteSwap64_lane _ _ hr]
  congr 1
  omega

theorem byteSwap64_injective {x y : BitVec 64}
    (h : byteSwap64 x = byteSwap64 y) : x = y := by
  have hh := congrArg byteSwap64 h
  simpa only [byteSwap64_involution] using hh

theorem byteReverse64_symmetric {x y : BitVec 64}
    (h : ByteReverse64 x y) : ByteReverse64 y x := by
  apply (byteReverse64_iff_eq y x).mpr
  rw [(byteReverse64_iff_eq x y).mp h, byteSwap64_involution]

theorem byteSwap64_zero : byteSwap64 0 = 0 := by decide

theorem byteSwap64_allOnes : byteSwap64 (BitVec.allOnes 64) = BitVec.allOnes 64 := by decide

/-- Edge bits cross byte positions, without reversing their positions within a byte. -/
theorem byteSwap64_one : byteSwap64 1 = (1 : BitVec 64) <<< 56 := by decide

theorem byteSwap64_topBit : byteSwap64 ((1 : BitVec 64) <<< 63) = (1 : BitVec 64) <<< 7 := by
  decide

/-- Distinct bytes expose lane-order errors that uniform edge values cannot expose. -/
theorem byteSwap64_distinct_bytes : byteSwap64 0x0123456789abcdef = 0xefcdab8967452301 := by
  decide

end EDSL.WordMath
