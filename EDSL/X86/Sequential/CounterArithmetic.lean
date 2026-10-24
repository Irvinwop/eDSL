/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

Natural-number consequences of existing low32 instruction operations.
The input words retain arbitrary upper bits; these are shared arithmetic laws.
-/
import EDSL.X86.Sequential.Counter32
import EDSL.X86.Sequential.Immediate32
import EDSL.X86.Sequential.TestImmediate8
import EDSL.X86.Sequential.Address32
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- SUB32 imm8=2, including the actual zero-extended destination expression. -/
theorem subImm32_two_nat (value : Word) (remaining : Nat)
    (matching : (value.setWidth 32).toNat = remaining) (enough : 2 ≤ remaining) :
    ((value.setWidth 32 - (2 : Byte).signExtend 32).setWidth 64).toNat = remaining - 2 := by
  have ordered : (2 : BitVec 32) ≤ value.setWidth 32 := by
    change (2 : Nat) ≤ (value.setWidth 32).toNat
    omega
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  change (value.setWidth 32 - (2 : BitVec 32)).toNat = remaining - 2
  simpa [matching] using BitVec.toNat_sub_of_le ordered

/-- ADD32 imm8=0xf8 computes a Nat decrement when eight remain.
Only the result is equated with subtraction; ADD flags remain ADD flags. -/
theorem addImm32_minus_eight_nat (value : Word) (remaining : Nat)
    (matching : (value.setWidth 32).toNat = remaining) (enough : 8 ≤ remaining) :
    ((value.setWidth 32 + (0xf8 : Byte).signExtend 32).setWidth 64).toNat = remaining - 8 := by
  have negativeImmediate : (0xf8 : Byte).signExtend 32 = -(8 : BitVec 32) := by decide
  have ordered : (8 : BitVec 32) ≤ value.setWidth 32 := by
    change (8 : Nat) ≤ (value.setWidth 32).toNat
    omega
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), negativeImmediate,
    BitVec.add_neg_eq_sub]
  simpa [matching] using BitVec.toNat_sub_of_le ordered

/-- LEA32 [base-1] first evaluates the unrestricted full64 address.
Only the low32 base matches count; no upper-half or signed-range premise. -/
theorem Address.baseDisp8_minus_one_nat (before : State) (base : Register) (count : Nat)
    (matching : ((before.registers base).setWidth 32).toNat = count) (positive : 0 < count) :
    ((((Address.baseDisp8 base 0xff).eval before).setWidth 32).setWidth 64).toNat = count - 1 := by
  have ordered : (1 : BitVec 32) ≤ (before.registers base).setWidth 32 := by
    change (1 : Nat) ≤ ((before.registers base).setWidth 32).toNat
    omega
  have displacement : ((0xff : Byte).signExtend 64).setWidth 32 = -(1 : BitVec 32) := by
    decide
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  change ((before.registers base + (0xff : Byte).signExtend 64).setWidth 32).toNat = count - 1
  rw [BitVec.setWidth_add _ _ (by decide : 32 ≤ 64), displacement, BitVec.add_neg_eq_sub]
  simpa [matching] using BitVec.toNat_sub_of_le ordered

/-- The existing logical operation, signed immediate and zero extension.
Mask/modulo arithmetic itself is already in the pinned Nat library. -/
theorem logicalImm32_and_seven_nat (value : Word) (count : Nat)
    (matching : (value.setWidth 32).toNat = count) :
    ((LogicalOp.band.eval (value.setWidth 32) ((7 : Byte).signExtend 32)).setWidth 64).toNat =
      count % 8 := by
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  change (value.setWidth 32 &&& (7 : BitVec 32)).toNat = count % 8
  rw [BitVec.toNat_and, matching]
  exact Nat.and_two_pow_sub_one_eq_mod count 3

/-- Arithmetic parity of the low32 count, as the actual TEST8 AND1 result.
This is a Nat identity; the architectural PF is the evenParity Bool. -/
theorem testImm8_and_one_nat (value : Word) (count : Nat)
    (matching : (value.setWidth 32).toNat = count) :
    (value.setWidth 8 &&& (1 : Byte)).toNat = count % 2 := by
  have lowParity : value.toNat % 2 = count % 2 := by
    have observed := congrArg (fun n : Nat => n % 2) matching
    simpa only [BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd value.toNat (by decide : 2 ∣ 2^32)] using observed
  rw [testImm8_result_toNat]
  change (value.toNat % 256) &&& 1 = count % 2
  rw [Nat.and_one_is_mod, Nat.mod_mod_of_dvd value.toNat (by decide : 2 ∣ 256)]
  exact lowParity

end EDSL.X86.Sequential

#print axioms EDSL.X86.Sequential.subImm32_two_nat
#print axioms EDSL.X86.Sequential.addImm32_minus_eight_nat
#print axioms EDSL.X86.Sequential.Address.baseDisp8_minus_one_nat
#print axioms EDSL.X86.Sequential.logicalImm32_and_seven_nat
#print axioms EDSL.X86.Sequential.testImm8_and_one_nat
#audit_edsl
