/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ConditionFlags

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- Logical-result equality can be observed by signed integer equality without
restricting the operand or the independently undefined AF bit. -/
theorem Condition.logical32_equal_int (old : Word) (value : BitVec 32) (af : Bool) :
    holds .equal (logicalFlags32 old value af) = decide (value.toInt = 0) := by
  rw [Condition.holds, (logicalFlags32_bits old value af).2.2.2.1]
  have equivalent : value = (0 : BitVec 32) ↔ value.toInt = 0 := by
    constructor
    · rintro rfl
      rfl
    · intro zero
      exact BitVec.eq_of_toInt_eq zero
  rw [Bool.beq_eq_decide_eq]
  simp only [equivalent]

theorem Condition.logical32_notEqual_int (old : Word) (value : BitVec 32) (af : Bool) :
    holds .notEqual (logicalFlags32 old value af) = decide (value.toInt ≠ 0) := by
  change (!(holds .equal (logicalFlags32 old value af))) = _
  rw [logical32_equal_int]
  simp only [← decide_not]

/-- With OF cleared by logical instructions, SETG observes strict signed
positivity. The result includes the signed minimum and ignores AF. -/
theorem Condition.logical32_greater_zero (old : Word) (value : BitVec 32) (af : Bool) :
    holds .greater (logicalFlags32 old value af) = decide (0 < value.toInt) := by
  have zero := logical32_equal_int old value af
  change (logicalFlags32 old value af).getLsbD 6 = decide (value.toInt = 0) at zero
  simp only [Condition.holds, zero, (logicalFlags32_bits old value af).2.2.2.2.1,
    (logicalFlags32_bits old value af).2.2.2.2.2, BitVec.msb_eq_toInt]
  by_cases negative : value.toInt < 0
  · simp [negative, show ¬ 0 < value.toInt by omega]
  · by_cases zero : value.toInt = 0
    · simp [zero]
    · simp [negative, zero, show 0 < value.toInt by omega]

end EDSL.X86.Sequential
