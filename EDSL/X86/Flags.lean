/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State

namespace EDSL.X86

/-- The six status flags written by a 32-bit integer addition. Other RFLAGS
bits, including reserved bits in this abstract word, retain their input value. -/
def arithmeticFlagMask : Word := 0x8d5

def flagBit (index : Nat) (value : Bool) : Word :=
  (if value then (1 : Word) else 0) <<< index

def evenParity (byte : Byte) : Bool := !byte.cpop.getLsbD 0

/-- ADD/XADD status flags use the sum, even though XADD returns the old
destination in its source register. Carry and signed overflow use Lean's
independent mathematical overflow predicates. -/
def addFlags32 (flags : Word) (left right : BitVec 32) : Word :=
  let result := left + right
  (flags &&& ~~~arithmeticFlagMask) |||
    flagBit 0 (left.uaddOverflow right) |||
    flagBit 2 (evenParity (result.setWidth 8)) |||
    flagBit 4 ((left.setWidth 4).uaddOverflow (right.setWidth 4)) |||
    flagBit 6 (result == 0) |||
    flagBit 7 result.msb |||
    flagBit 11 (left.saddOverflow right)

theorem addFlags32_bits (flags : Word) (left right : BitVec 32) :
    (addFlags32 flags left right).getLsbD 0 = left.uaddOverflow right ∧
    (addFlags32 flags left right).getLsbD 2 = evenParity ((left + right).setWidth 8) ∧
    (addFlags32 flags left right).getLsbD 4 = (left.setWidth 4).uaddOverflow (right.setWidth 4) ∧
    (addFlags32 flags left right).getLsbD 6 = (left + right == 0) ∧
    (addFlags32 flags left right).getLsbD 7 = (left + right).msb ∧
    (addFlags32 flags left right).getLsbD 11 = left.saddOverflow right := by
  cases carry : left.uaddOverflow right <;>
    cases parity : evenParity ((left + right).setWidth 8) <;>
    cases auxiliary : (left.setWidth 4).uaddOverflow (right.setWidth 4) <;>
    (by_cases zero : left + right = 0) <;>
    cases sign : (left + right).msb <;>
    cases overflow : left.saddOverflow right <;>
    simp_all [addFlags32, flagBit, arithmeticFlagMask]

theorem addFlags32_preserves (flags : Word) (left right : BitVec 32) :
    addFlags32 flags left right &&& ~~~arithmeticFlagMask = flags &&& ~~~arithmeticFlagMask := by
  cases carry : left.uaddOverflow right <;>
    cases parity : evenParity ((left + right).setWidth 8) <;>
    cases auxiliary : (left.setWidth 4).uaddOverflow (right.setWidth 4) <;>
    (by_cases zero : left + right = 0) <;>
    cases sign : (left + right).msb <;>
    cases overflow : left.saddOverflow right <;>
    simp_all [addFlags32, flagBit, arithmeticFlagMask, BitVec.and_or_distrib_right, BitVec.and_assoc]

theorem addFlags32_carry (flags : Word) (left right : BitVec 32) :
    (addFlags32 flags left right).getLsbD 0 = true ↔ 2^32 ≤ left.toNat + right.toNat := by
  rw [(addFlags32_bits flags left right).1]
  simp [BitVec.uaddOverflow]

theorem addFlags32_overflow (flags : Word) (left right : BitVec 32) :
    (addFlags32 flags left right).getLsbD 11 = true ↔
      left.toInt + right.toInt < -(2^31 : Int) ∨ 2^31 ≤ left.toInt + right.toInt := by
  rw [(addFlags32_bits flags left right).2.2.2.2.2]
  simp [BitVec.saddOverflow, or_comm]

end EDSL.X86
