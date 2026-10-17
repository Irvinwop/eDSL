/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory64

namespace EDSL.X86

/-- The byte primitives accept exactly the same readable canonical cells;
their DATA and STACK error constructors remain distinct. -/
theorem readDataByte_readStackByte_success_iff (memory : Memory) (address : Word) (byte : Byte) :
    readDataByte memory address = .ok byte ↔ readStackByte memory address = .ok byte := by
  unfold readDataByte readStackByte
  split <;> cases memory.read address <;> simp

private theorem throw_error (fault : Error) : (throw fault : Except Error α) = .error fault := rfl

private theorem bind_success_iff (result : Except ε α) (next : α → Except ε β) (value : β) :
    (result >>= next) = .ok value ↔ ∃ input, result = .ok input ∧ next input = .ok value := by
  cases result <;> simp

/-- Complete eight-byte DATA and STACK reads succeed with exactly the same
value. Both retain their nonwrapping/canonical checks and separate faults. -/
theorem loadQWord_readWord_success_iff (memory : Memory) (address value : Word) :
    loadQWord memory address = .ok value ↔ readWord memory address = .ok value := by
  by_cases wraps : address.toNat + 7 ≥ 2^64
  · simp [loadQWord, readWord, wraps, throw_error]
  · simp only [loadQWord, readWord, ite_eq_right wraps, bind_success_iff,
      readDataByte_readStackByte_success_iff, joinQWord, pure_ok]

theorem readWord_of_loadQWord (memory : Memory) (address value : Word)
    (success : loadQWord memory address = .ok value) :
    readWord memory address = .ok value :=
  (loadQWord_readWord_success_iff memory address value).mp success

theorem loadQWord_of_readWord (memory : Memory) (address value : Word)
    (success : readWord memory address = .ok value) :
    loadQWord memory address = .ok value :=
  (loadQWord_readWord_success_iff memory address value).mpr success

end EDSL.X86
