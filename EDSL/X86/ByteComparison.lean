/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Flags

set_option autoImplicit false

namespace EDSL.X86.Sequential

/-- Byte subtraction flags for CMP. Intel SDM Volume 2, CMP (80 /7 ib):
the destination is unchanged and CF/PF/AF/ZF/SF/OF describe an eight-bit
subtraction. No sign extension to a wider arithmetic width is performed. -/
def cmpFlags8 (old : Word) (left right : Byte) : Word :=
  let result := left - right
  statusFlags old (left.usubOverflow right) (evenParity result)
    ((left.setWidth 4).usubOverflow (right.setWidth 4)) (result == 0) result.msb
    (left.ssubOverflow right)

theorem cmpFlags8_bits (old : Word) (left right : Byte) :
    (cmpFlags8 old left right).getLsbD 0 = left.usubOverflow right ∧
    (cmpFlags8 old left right).getLsbD 2 = evenParity (left - right) ∧
    (cmpFlags8 old left right).getLsbD 4 = (left.setWidth 4).usubOverflow (right.setWidth 4) ∧
    (cmpFlags8 old left right).getLsbD 6 = (left - right == 0) ∧
    (cmpFlags8 old left right).getLsbD 7 = (left - right).msb ∧
    (cmpFlags8 old left right).getLsbD 11 = left.ssubOverflow right :=
  statusFlags_bits ..

theorem cmpFlags8_preserves (old : Word) (left right : Byte) :
    cmpFlags8 old left right &&& ~~~arithmeticFlagMask = old &&& ~~~arithmeticFlagMask :=
  statusFlags_preserves ..

theorem cmpFlags8_zero (old : Word) (left right : Byte) :
    (cmpFlags8 old left right).getLsbD 6 = (left == right) := by
  rw [(cmpFlags8_bits ..).2.2.2.1]
  simp [Bool.beq_eq_decide_eq, BitVec.sub_eq_iff_eq_add]

theorem cmpFlags8_borrow (old : Word) (left right : Byte) :
    (cmpFlags8 old left right).getLsbD 0 = true ↔ left.toNat < right.toNat := by
  rw [(cmpFlags8_bits ..).1]
  simp [BitVec.usubOverflow]

theorem cmpFlags8_auxiliary (old : Word) (left right : Byte) :
    (cmpFlags8 old left right).getLsbD 4 = true ↔ left.toNat % 16 < right.toNat % 16 := by
  rw [(cmpFlags8_bits ..).2.2.1]
  simp [BitVec.usubOverflow, BitVec.toNat_setWidth]

theorem cmpFlags8_overflow (old : Word) (left right : Byte) :
    (cmpFlags8 old left right).getLsbD 11 = true ↔
      left.toInt - right.toInt < -(128 : Int) ∨ 128 ≤ left.toInt - right.toInt := by
  rw [(cmpFlags8_bits ..).2.2.2.2.2]
  simp [BitVec.ssubOverflow, or_comm]

theorem Condition.cmp8_equal (old : Word) (left right : Byte) :
    Condition.equal.holds (cmpFlags8 old left right) = (left == right) :=
  cmpFlags8_zero ..

theorem Condition.cmp8_notEqual (old : Word) (left right : Byte) :
    Condition.notEqual.holds (cmpFlags8 old left right) = Bool.not (left == right) := by
  change Bool.not ((cmpFlags8 old left right).getLsbD 6) = Bool.not (left == right)
  rw [cmpFlags8_zero]

end EDSL.X86.Sequential
