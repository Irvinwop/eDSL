/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Model

namespace EDSL.X86.Sequential

/-- The six arithmetic status bits; every other bit of the abstract flags word
is preserved. Logical operations take an explicit, independent AF choice.
Intel SDM XOR: https://cdrdv2-public.intel.com/843855/334569-sdm-vol-2d-dec-24.pdf#page=43
Intel SDM TEST: https://cdrdv2.intel.com/v1/dl/getContent/671241#page=729
Neither choice claims a canonical physical value for undefined AF. -/
def statusFlags (old : Word) (cf pf af zf sf of : Bool) : Word :=
  (old &&& ~~~arithmeticFlagMask) ||| flagBit 0 cf ||| flagBit 2 pf |||
    flagBit 4 af ||| flagBit 6 zf ||| flagBit 7 sf ||| flagBit 11 of

theorem statusFlags_bits (old : Word) (cf pf af zf sf of : Bool) :
    (statusFlags old cf pf af zf sf of).getLsbD 0 = cf ∧
    (statusFlags old cf pf af zf sf of).getLsbD 2 = pf ∧
    (statusFlags old cf pf af zf sf of).getLsbD 4 = af ∧
    (statusFlags old cf pf af zf sf of).getLsbD 6 = zf ∧
    (statusFlags old cf pf af zf sf of).getLsbD 7 = sf ∧
    (statusFlags old cf pf af zf sf of).getLsbD 11 = of := by
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;>
    simp [statusFlags, flagBit, arithmeticFlagMask]

theorem statusFlags_preserves (old : Word) (cf pf af zf sf of : Bool) :
    statusFlags old cf pf af zf sf of &&& ~~~arithmeticFlagMask =
      old &&& ~~~arithmeticFlagMask := by
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;>
    simp [statusFlags, flagBit, arithmeticFlagMask, BitVec.and_or_distrib_right, BitVec.and_assoc]

def logicalFlags32 (old : Word) (result : BitVec 32) (af : Bool) : Word :=
  statusFlags old false (evenParity (result.setWidth 8)) af (result == 0) result.msb false

def logicalFlags64 (old result : Word) (af : Bool) : Word :=
  statusFlags old false (evenParity (result.setWidth 8)) af (result == 0) result.msb false

/-- SHR at width64 with count exactly one. AF is the sole undefined flag;
the supplied choice is independent of the operand and incoming flags. -/
def shrOneFlags64 (old value : Word) (af : Bool) : Word :=
  let result := value >>> 1
  statusFlags old (value.getLsbD 0) (evenParity (result.setWidth 8)) af
    (result == 0) result.msb value.msb

theorem shrOneFlags64_bits (old value : Word) (af : Bool) :
    (shrOneFlags64 old value af).getLsbD 0 = value.getLsbD 0 ∧
    (shrOneFlags64 old value af).getLsbD 2 = evenParity ((value >>> 1).setWidth 8) ∧
    (shrOneFlags64 old value af).getLsbD 4 = af ∧
    (shrOneFlags64 old value af).getLsbD 6 = (value >>> 1 == 0) ∧
    (shrOneFlags64 old value af).getLsbD 7 = (value >>> 1).msb ∧
    (shrOneFlags64 old value af).getLsbD 11 = value.msb :=
  statusFlags_bits ..

theorem shrOneFlags64_preserves (old value : Word) (af : Bool) :
    shrOneFlags64 old value af &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

def addFlags64 (old left right : Word) : Word :=
  let result := left + right
  statusFlags old (left.uaddOverflow right) (evenParity (result.setWidth 8))
    ((left.setWidth 4).uaddOverflow (right.setWidth 4)) (result == 0) result.msb
    (left.saddOverflow right)

/-- CMP computes left minus right. CF and AF are unsigned borrows. -/
def cmpFlags64 (old left right : Word) : Word :=
  let result := left - right
  statusFlags old (left.usubOverflow right) (evenParity (result.setWidth 8))
    ((left.setWidth 4).usubOverflow (right.setWidth 4)) (result == 0) result.msb
    (left.ssubOverflow right)

/-- CMP32 subtracts at width 32, discards the result and preserves every
nonarithmetic flag. In particular high GPR halves never participate. -/
def cmpFlags32 (old : Word) (left right : BitVec 32) : Word :=
  let result := left - right
  statusFlags old (left.usubOverflow right) (evenParity (result.setWidth 8))
    ((left.setWidth 4).usubOverflow (right.setWidth 4)) (result == 0) result.msb
    (left.ssubOverflow right)

theorem cmpFlags32_bits (old : Word) (left right : BitVec 32) :
    (cmpFlags32 old left right).getLsbD 0 = left.usubOverflow right ∧
    (cmpFlags32 old left right).getLsbD 2 = evenParity ((left - right).setWidth 8) ∧
    (cmpFlags32 old left right).getLsbD 4 = (left.setWidth 4).usubOverflow (right.setWidth 4) ∧
    (cmpFlags32 old left right).getLsbD 6 = (left - right == 0) ∧
    (cmpFlags32 old left right).getLsbD 7 = (left - right).msb ∧
    (cmpFlags32 old left right).getLsbD 11 = left.ssubOverflow right :=
  statusFlags_bits ..

theorem cmpFlags32_preserves (old : Word) (left right : BitVec 32) :
    cmpFlags32 old left right &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem cmpFlags32_zero (old : Word) (left right : BitVec 32) :
    (cmpFlags32 old left right).getLsbD 6 = (left == right) := by
  rw [(cmpFlags32_bits ..).2.2.2.1]
  simp [Bool.beq_eq_decide_eq, BitVec.sub_eq_iff_eq_add]

theorem cmpFlags32_borrow (old : Word) (left right : BitVec 32) :
    (cmpFlags32 old left right).getLsbD 0 = true ↔ left.toNat < right.toNat := by
  rw [(cmpFlags32_bits ..).1]
  simp [BitVec.usubOverflow]

theorem cmpFlags32_auxiliary (old : Word) (left right : BitVec 32) :
    (cmpFlags32 old left right).getLsbD 4 = true ↔ left.toNat % 16 < right.toNat % 16 := by
  rw [(cmpFlags32_bits ..).2.2.1]
  simp [BitVec.usubOverflow, BitVec.toNat_setWidth]

theorem cmpFlags32_overflow (old : Word) (left right : BitVec 32) :
    (cmpFlags32 old left right).getLsbD 11 = true ↔
      left.toInt - right.toInt < -(2^31 : Int) ∨ 2^31 ≤ left.toInt - right.toInt := by
  rw [(cmpFlags32_bits ..).2.2.2.2.2]
  simp [BitVec.ssubOverflow, or_comm]

/-- NEG is precisely subtraction from zero. Unlike logical instructions,
all six arithmetic flags, including the low-nibble borrow AF, are defined.
Intel SDM Vol.2 NEG, F7 /3, specifies subtraction from zero and these six
affected flags: https://cdrdv2-public.intel.com/789581/325383-sdm-vol-2abcd.pdf -/
theorem cmpFlags32_neg_carry (old : Word) (value : BitVec 32) :
    (cmpFlags32 old 0 value).getLsbD 0 = true ↔ value ≠ 0 := by
  rw [cmpFlags32_borrow]
  change 0 < value.toNat ↔ value ≠ 0
  rw [Nat.pos_iff_ne_zero]
  exact not_congr (BitVec.toNat_inj (y := 0))

theorem cmpFlags32_neg_auxiliary (old : Word) (value : BitVec 32) :
    (cmpFlags32 old 0 value).getLsbD 4 = true ↔ value.toNat % 16 ≠ 0 := by
  rw [cmpFlags32_auxiliary]
  simp [Nat.pos_iff_ne_zero]

theorem cmpFlags32_neg_overflow (old : Word) (value : BitVec 32) :
    (cmpFlags32 old 0 value).getLsbD 11 = true ↔ value.toInt = -2147483648 := by
  rw [cmpFlags32_overflow]
  change (0 - value.toInt < -(2147483648 : Int) ∨ 2147483648 ≤ 0 - value.toInt) ↔
    value.toInt = -2147483648
  have lower := BitVec.le_toInt value
  have upper := BitVec.toInt_lt (x := value)
  have lower' : -(2147483648 : Int) ≤ value.toInt := by simpa using lower
  have upper' : value.toInt < (2147483648 : Int) := by simpa using upper
  omega

/-- INC/DEC leave the complete incoming CF bit intact. -/
def incFlags64 (old value : Word) : Word :=
  let result := value + 1
  statusFlags old (old.getLsbD 0) (evenParity (result.setWidth 8))
    ((value.setWidth 4).uaddOverflow 1) (result == 0) result.msb (value.saddOverflow 1)

/-- INC32 defines PF/AF/ZF/SF/OF at operand width32 and preserves the old CF. -/
def incFlags32 (old : Word) (value : BitVec 32) : Word :=
  let result := value + 1
  statusFlags old (old.getLsbD 0) (evenParity (result.setWidth 8))
    ((value.setWidth 4).uaddOverflow 1) (result == 0) result.msb (value.saddOverflow 1)

theorem incFlags32_bits (old : Word) (value : BitVec 32) :
    (incFlags32 old value).getLsbD 0 = old.getLsbD 0 ∧
    (incFlags32 old value).getLsbD 2 = evenParity ((value + 1).setWidth 8) ∧
    (incFlags32 old value).getLsbD 4 = (value.setWidth 4).uaddOverflow 1 ∧
    (incFlags32 old value).getLsbD 6 = (value + 1 == 0) ∧
    (incFlags32 old value).getLsbD 7 = (value + 1).msb ∧
    (incFlags32 old value).getLsbD 11 = value.saddOverflow 1 := statusFlags_bits ..

theorem incFlags32_preserves (old : Word) (value : BitVec 32) :
    incFlags32 old value &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem incFlags32_carry (old : Word) (value : BitVec 32) :
    (incFlags32 old value).getLsbD 0 = old.getLsbD 0 := (incFlags32_bits ..).1

def decFlags64 (old value : Word) : Word :=
  let result := value - 1
  statusFlags old (old.getLsbD 0) (evenParity (result.setWidth 8))
    ((value.setWidth 4).usubOverflow 1) (result == 0) result.msb (value.ssubOverflow 1)

theorem logicalFlags32_bits (old : Word) (result : BitVec 32) (af : Bool) :
    (logicalFlags32 old result af).getLsbD 0 = false ∧
    (logicalFlags32 old result af).getLsbD 2 = evenParity (result.setWidth 8) ∧
    (logicalFlags32 old result af).getLsbD 4 = af ∧
    (logicalFlags32 old result af).getLsbD 6 = (result == 0) ∧
    (logicalFlags32 old result af).getLsbD 7 = result.msb ∧
    (logicalFlags32 old result af).getLsbD 11 = false :=
  statusFlags_bits ..

theorem logicalFlags64_bits (old result : Word) (af : Bool) :
    (logicalFlags64 old result af).getLsbD 0 = false ∧
    (logicalFlags64 old result af).getLsbD 2 = evenParity (result.setWidth 8) ∧
    (logicalFlags64 old result af).getLsbD 4 = af ∧
    (logicalFlags64 old result af).getLsbD 6 = (result == 0) ∧
    (logicalFlags64 old result af).getLsbD 7 = result.msb ∧
    (logicalFlags64 old result af).getLsbD 11 = false :=
  statusFlags_bits ..

theorem addFlags64_bits (old left right : Word) :
    (addFlags64 old left right).getLsbD 0 = left.uaddOverflow right ∧
    (addFlags64 old left right).getLsbD 2 = evenParity ((left + right).setWidth 8) ∧
    (addFlags64 old left right).getLsbD 4 = (left.setWidth 4).uaddOverflow (right.setWidth 4) ∧
    (addFlags64 old left right).getLsbD 6 = (left + right == 0) ∧
    (addFlags64 old left right).getLsbD 7 = (left + right).msb ∧
    (addFlags64 old left right).getLsbD 11 = left.saddOverflow right :=
  statusFlags_bits ..

theorem cmpFlags64_bits (old left right : Word) :
    (cmpFlags64 old left right).getLsbD 0 = left.usubOverflow right ∧
    (cmpFlags64 old left right).getLsbD 2 = evenParity ((left - right).setWidth 8) ∧
    (cmpFlags64 old left right).getLsbD 4 = (left.setWidth 4).usubOverflow (right.setWidth 4) ∧
    (cmpFlags64 old left right).getLsbD 6 = (left - right == 0) ∧
    (cmpFlags64 old left right).getLsbD 7 = (left - right).msb ∧
    (cmpFlags64 old left right).getLsbD 11 = left.ssubOverflow right :=
  statusFlags_bits ..

theorem incFlags64_bits (old value : Word) :
    (incFlags64 old value).getLsbD 0 = old.getLsbD 0 ∧
    (incFlags64 old value).getLsbD 2 = evenParity ((value + 1).setWidth 8) ∧
    (incFlags64 old value).getLsbD 4 = (value.setWidth 4).uaddOverflow 1 ∧
    (incFlags64 old value).getLsbD 6 = (value + 1 == 0) ∧
    (incFlags64 old value).getLsbD 7 = (value + 1).msb ∧
    (incFlags64 old value).getLsbD 11 = value.saddOverflow 1 :=
  statusFlags_bits ..

theorem decFlags64_bits (old value : Word) :
    (decFlags64 old value).getLsbD 0 = old.getLsbD 0 ∧
    (decFlags64 old value).getLsbD 2 = evenParity ((value - 1).setWidth 8) ∧
    (decFlags64 old value).getLsbD 4 = (value.setWidth 4).usubOverflow 1 ∧
    (decFlags64 old value).getLsbD 6 = (value - 1 == 0) ∧
    (decFlags64 old value).getLsbD 7 = (value - 1).msb ∧
    (decFlags64 old value).getLsbD 11 = value.ssubOverflow 1 :=
  statusFlags_bits ..

theorem logicalFlags32_preserves (old : Word) (result : BitVec 32) (af : Bool) :
    logicalFlags32 old result af &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem logicalFlags64_preserves (old result : Word) (af : Bool) :
    logicalFlags64 old result af &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem addFlags64_preserves (old left right : Word) :
    addFlags64 old left right &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem cmpFlags64_preserves (old left right : Word) :
    cmpFlags64 old left right &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem incFlags64_preserves (old value : Word) :
    incFlags64 old value &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem decFlags64_preserves (old value : Word) :
    decFlags64 old value &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem logicalFlags32_zero (old : Word) (result : BitVec 32) (af : Bool) :
    (logicalFlags32 old result af).getLsbD 6 = (result == 0) :=
  (logicalFlags32_bits ..).2.2.2.1

theorem logicalFlags64_zero (old result : Word) (af : Bool) :
    (logicalFlags64 old result af).getLsbD 6 = (result == 0) :=
  (logicalFlags64_bits ..).2.2.2.1

theorem cmpFlags64_zero (old left right : Word) :
    (cmpFlags64 old left right).getLsbD 6 = (left == right) := by
  rw [(cmpFlags64_bits ..).2.2.2.1]
  simp [Bool.beq_eq_decide_eq, BitVec.sub_eq_iff_eq_add]

/-- Both AF outcomes exist, and specifying the six status bits plus preservation
of all remaining bits leaves no additional freedom. -/
theorem statusFlags_unique (old actual : Word) (cf pf af zf sf of : Bool)
    (outside : actual &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask)
    (bits : actual.getLsbD 0 = cf ∧ actual.getLsbD 2 = pf ∧ actual.getLsbD 4 = af ∧
      actual.getLsbD 6 = zf ∧ actual.getLsbD 7 = sf ∧ actual.getLsbD 11 = of) :
    actual = statusFlags old cf pf af zf sf of := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i bound
  have frame := congrArg (fun word : Word => word.getLsbD i) outside
  have expected := statusFlags_bits old cf pf af zf sf of
  by_cases h0 : i = 0
  · subst i; exact bits.1.trans expected.1.symm
  by_cases h2 : i = 2
  · subst i; exact bits.2.1.trans expected.2.1.symm
  by_cases h4 : i = 4
  · subst i; exact bits.2.2.1.trans expected.2.2.1.symm
  by_cases h6 : i = 6
  · subst i; exact bits.2.2.2.1.trans expected.2.2.2.1.symm
  by_cases h7 : i = 7
  · subst i; exact bits.2.2.2.2.1.trans expected.2.2.2.2.1.symm
  by_cases h11 : i = 11
  · subst i; exact bits.2.2.2.2.2.trans expected.2.2.2.2.2.symm
  have mask : arithmeticFlagMask.getLsbD i = false := by
    change (2261 : Nat).testBit i = false
    change ((2^0 ||| 2^2 ||| 2^4 ||| 2^6 ||| 2^7 ||| 2^11) : Nat).testBit i = false
    simp only [Nat.testBit_or, Nat.testBit_two_pow]
    simp [Ne.symm h0, Ne.symm h2, Ne.symm h4, Ne.symm h6, Ne.symm h7, Ne.symm h11]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, bound, decide_true, mask,
    Bool.not_false, Bool.and_true] at frame
  rw [frame]
  symm
  have preserved := congrArg (fun word : Word => word.getLsbD i)
    (statusFlags_preserves old cf pf af zf sf of)
  simpa only [BitVec.getLsbD_and, BitVec.getLsbD_not, bound, decide_true, mask,
    Bool.not_false, Bool.and_true] using preserved

/-- The independent architectural flag contract for a full64 SHR by one.
The actual AF bit is unrestricted, including for a physical observation. -/
def ShrOneFlags64Admissible (old value actual : Word) : Prop :=
  actual &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask ∧
  actual.getLsbD 0 = value.getLsbD 0 ∧
  actual.getLsbD 2 = evenParity ((value >>> 1).setWidth 8) ∧
  actual.getLsbD 6 = (value >>> 1 == 0) ∧
  actual.getLsbD 7 = (value >>> 1).msb ∧
  actual.getLsbD 11 = value.msb

/-- Defined flags and the nonarithmetic frame determine an AF witness, without
assuming that both abstract choices occur on a particular physical processor. -/
theorem shrOneFlags64_admissible_iff (old value actual : Word) :
    ShrOneFlags64Admissible old value actual ↔ ∃ af, actual = shrOneFlags64 old value af := by
  constructor
  · rintro ⟨outside, carry, parity, zero, sign, overflow⟩
    exact ⟨actual.getLsbD 4, statusFlags_unique old actual _ _ _ _ _ _ outside
      ⟨carry, parity, rfl, zero, sign, overflow⟩⟩
  · rintro ⟨af, rfl⟩
    have bits := shrOneFlags64_bits old value af
    exact ⟨shrOneFlags64_preserves old value af, bits.1, bits.2.1,
      bits.2.2.2.1, bits.2.2.2.2.1, bits.2.2.2.2.2⟩

theorem shrOneFlags64_choices (old value : Word) (left right : Bool) :
    shrOneFlags64 old value left &&& ~~~(0x10 : Word) =
      shrOneFlags64 old value right &&& ~~~(0x10 : Word) := by
  cases left <;> cases right <;>
    simp [shrOneFlags64, statusFlags, flagBit, BitVec.and_or_distrib_right]

theorem shrOneFlags64_choice_injective (old value : Word) (left right : Bool) :
    shrOneFlags64 old value left = shrOneFlags64 old value right ↔ left = right := by
  constructor
  · intro same
    have bit := congrArg (fun flags : Word => flags.getLsbD 4) same
    simpa only [(shrOneFlags64_bits old value left).2.2.1,
      (shrOneFlags64_bits old value right).2.2.1] using bit
  · rintro rfl
    rfl

theorem shrOneFlags64_admits_both (old value : Word) :
    ShrOneFlags64Admissible old value (shrOneFlags64 old value false) ∧
    ShrOneFlags64Admissible old value (shrOneFlags64 old value true) :=
  ⟨(shrOneFlags64_admissible_iff ..).mpr ⟨false, rfl⟩,
    (shrOneFlags64_admissible_iff ..).mpr ⟨true, rfl⟩⟩

/-- Complete logical-instruction contract: AF is the only unspecified status
bit. Both Boolean choices meet this contract and exhaust its concrete outcomes.
This overapproximation makes no claim that a processor realizes every choice. -/
def LogicalFlagsAdmissible (old actual : Word) (parity zero sign : Bool) : Prop :=
  actual &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask ∧
  actual.getLsbD 0 = false ∧ actual.getLsbD 2 = parity ∧
  actual.getLsbD 6 = zero ∧ actual.getLsbD 7 = sign ∧ actual.getLsbD 11 = false

theorem logicalFlags32_admissible_iff (old actual : Word) (result : BitVec 32) :
    LogicalFlagsAdmissible old actual (evenParity (result.setWidth 8)) (result == 0) result.msb ↔
      ∃ af, actual = logicalFlags32 old result af := by
  constructor
  · rintro ⟨outside, carry, parity, zero, sign, overflow⟩
    exact ⟨actual.getLsbD 4, statusFlags_unique old actual _ _ _ _ _ _ outside
      ⟨carry, parity, rfl, zero, sign, overflow⟩⟩
  · rintro ⟨af, rfl⟩
    have bits := logicalFlags32_bits old result af
    exact ⟨logicalFlags32_preserves old result af, bits.1, bits.2.1,
      bits.2.2.2.1, bits.2.2.2.2.1, bits.2.2.2.2.2⟩

theorem logicalFlags64_admissible_iff (old actual result : Word) :
    LogicalFlagsAdmissible old actual (evenParity (result.setWidth 8)) (result == 0) result.msb ↔
      ∃ af, actual = logicalFlags64 old result af := by
  constructor
  · rintro ⟨outside, carry, parity, zero, sign, overflow⟩
    exact ⟨actual.getLsbD 4, statusFlags_unique old actual _ _ _ _ _ _ outside
      ⟨carry, parity, rfl, zero, sign, overflow⟩⟩
  · rintro ⟨af, rfl⟩
    have bits := logicalFlags64_bits old result af
    exact ⟨logicalFlags64_preserves old result af, bits.1, bits.2.1,
      bits.2.2.2.1, bits.2.2.2.2.1, bits.2.2.2.2.2⟩

theorem logicalFlags32_choices (old : Word) (result : BitVec 32) (left right : Bool) :
    logicalFlags32 old result left &&& ~~~(0x10 : Word) =
      logicalFlags32 old result right &&& ~~~(0x10 : Word) := by
  cases left <;> cases right <;>
    simp [logicalFlags32, statusFlags, flagBit, BitVec.and_or_distrib_right]

theorem logicalFlags64_choices (old result : Word) (left right : Bool) :
    logicalFlags64 old result left &&& ~~~(0x10 : Word) =
      logicalFlags64 old result right &&& ~~~(0x10 : Word) := by
  cases left <;> cases right <;>
    simp [logicalFlags64, statusFlags, flagBit, BitVec.and_or_distrib_right]

theorem incFlags64_carry (old value : Word) :
    (incFlags64 old value).getLsbD 0 = old.getLsbD 0 := (incFlags64_bits ..).1

theorem decFlags64_carry (old value : Word) :
    (decFlags64 old value).getLsbD 0 = old.getLsbD 0 := (decFlags64_bits ..).1

/-- Independent mathematical carry/overflow specifications at the actual width. -/
theorem addFlags64_carry (old left right : Word) :
    (addFlags64 old left right).getLsbD 0 = true ↔ 2^64 ≤ left.toNat + right.toNat := by
  rw [(addFlags64_bits ..).1]
  simp [BitVec.uaddOverflow]

theorem addFlags64_overflow (old left right : Word) :
    (addFlags64 old left right).getLsbD 11 = true ↔
      left.toInt + right.toInt < -(2^63 : Int) ∨ 2^63 ≤ left.toInt + right.toInt := by
  rw [(addFlags64_bits ..).2.2.2.2.2]
  simp [BitVec.saddOverflow, or_comm]

theorem cmpFlags64_borrow (old left right : Word) :
    (cmpFlags64 old left right).getLsbD 0 = true ↔ left.toNat < right.toNat := by
  rw [(cmpFlags64_bits ..).1]
  simp [BitVec.usubOverflow]

theorem cmpFlags64_overflow (old left right : Word) :
    (cmpFlags64 old left right).getLsbD 11 = true ↔
      left.toInt - right.toInt < -(2^63 : Int) ∨ 2^63 ≤ left.toInt - right.toInt := by
  rw [(cmpFlags64_bits ..).2.2.2.2.2]
  simp [BitVec.ssubOverflow, or_comm]

end EDSL.X86.Sequential
