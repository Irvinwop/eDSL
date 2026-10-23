/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.MachineChoices
import EDSL.X86.Sequential.CallerOnly
import EDSL.OS.CallResources

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- Truncation of a full64 effective address has the usual signed modular
interpretation. The input is not assumed canonical or accessible. -/
theorem addressLow32_signed (value : Word) :
    (value.setWidth 32).toInt = value.toInt.bmod (2^32) := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod]
  exact (Int.bmod_bmod_of_dvd (by decide : 2^32 ∣ 2^64)).symm

/-- Shared LEA address arithmetic, independent of the destination width.
The displacement is a signed integer; no operand-memory premise occurs. -/
theorem Address.eval_baseDisp8_signed (before : State) (base : Register)
    (displacement : Byte) :
    ((Address.baseDisp8 base displacement).eval before).toInt =
      ((before.registers base).toInt + displacement.toInt).bmod (2^64) := by
  simp only [Address.eval, BitVec.toInt_add,
    BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 64)]

theorem Address.eval_sibDisp8_signed (before : State) (base index : Register)
    (scale : Fin 4) (displacement : Byte) :
    ((Address.sibDisp8 base (some index) scale displacement).eval before).toInt =
      ((before.registers base).toInt +
        ((before.registers index).toNat * 2^scale.val : Nat) + displacement.toInt).bmod (2^64) := by
  simp only [Address.eval, BitVec.toInt_add, BitVec.toInt_shiftLeft,
    BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 64), Nat.shiftLeft_eq,
    Int.add_bmod_bmod, Int.bmod_add_bmod]

theorem execute_lea32 (before : State) (destination : Register) (address : Address)
    (prefixed choice : Bool) :
    execute before (.lea32 destination address prefixed) choice =
      .ok ⟨.next { before.writeRegister destination
        (((address.eval before).setWidth 32).setWidth 64) with
        rip := before.rip + BitVec.ofNat 64 ((if prefixed then 3 else 2) + address.suffixBytes) }, []⟩ := rfl

/-- Complete width and frame contract, valid for every GPR including RSP and
for all aliases between the destination and the prestate base/index. -/
structure Address32Context (before after : State) (destination : Register)
    (address : Address) (prefixed : Bool) : Prop where
  value : after.registers destination = ((address.eval before).setWidth 32).setWidth 64
  natural : (after.registers destination).toNat = (address.eval before).toNat % 2^32
  width : (after.registers destination).toNat < 2^32
  other : ∀ register, register ≠ destination → after.registers register = before.registers register
  memory : after.memory = before.memory
  flags : after.flags = before.flags
  rip : after.rip = before.rip +
    BitVec.ofNat 64 ((if prefixed then 3 else 2) + address.suffixBytes)

theorem execute_lea32_context (before : State) (destination : Register)
    (address : Address) (prefixed : Bool) :
    ∃ after, (∀ choice, execute before (.lea32 destination address prefixed) choice =
      .ok ⟨.next after, []⟩) ∧ Address32Context before after destination address prefixed := by
  refine ⟨_, fun _ => rfl, ?_⟩
  constructor
  · simp [State.writeRegister]
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), BitVec.toNat_setWidth]
  · simp only [State.writeRegister, ↓reduceIte,
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    exact ((address.eval before).setWidth 32).isLt
  · intro register different
    simp [State.writeRegister, different]
  · rfl
  · rfl
  · rfl

/-- Reuse the full64 LEA address contract: destination narrowing is the only
value difference. Prefix/encoding lengths are accounted for separately. -/
theorem lea32_narrows_lea64 (before : State) (destination : Register)
    (address : Address) (prefixed choice : Bool) :
    ∃ wide narrow,
      execute before (.lea64 destination address) choice = .ok ⟨.next wide, []⟩ ∧
      execute before (.lea32 destination address prefixed) choice = .ok ⟨.next narrow, []⟩ ∧
      narrow.registers destination = ((wide.registers destination).setWidth 32).setWidth 64 ∧
      narrow.flags = wide.flags ∧ narrow.memory = wide.memory := by
  obtain ⟨wide, executedWide, valueWide, _, memoryWide, flagsWide, _⟩ :=
    execute_lea64_context before destination address choice
  obtain ⟨narrow, executedNarrow, context⟩ := execute_lea32_context before destination address prefixed
  exact ⟨wide, narrow, executedWide, executedNarrow choice,
    by rw [context.value, valueWide], context.flags.trans flagsWide.symm,
    context.memory.trans memoryWide.symm⟩

theorem execute_lea32_baseDisp8_signed {before after : State} {destination base : Register}
    {displacement : Byte} {prefixed choice : Bool} {reads : List Read}
    (actual : execute before (.lea32 destination (.baseDisp8 base displacement) prefixed) choice =
      .ok ⟨.next after, reads⟩) :
    ((after.registers destination).setWidth 32).toInt =
      ((before.registers base).toInt + displacement.toInt).bmod (2^32) := by
  cases actual
  simp only [State.writeRegister, ↓reduceIte,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  rw [addressLow32_signed, Address.eval_baseDisp8_signed,
    Int.bmod_bmod_of_dvd (by decide : 2^32 ∣ 2^64)]

theorem execute_lea32_sibDisp8_signed {before after : State} {destination base index : Register}
    {scale : Fin 4} {displacement : Byte} {prefixed choice : Bool} {reads : List Read}
    (actual : execute before (.lea32 destination (.sibDisp8 base (some index) scale displacement)
      prefixed) choice = .ok ⟨.next after, reads⟩) :
    ((after.registers destination).setWidth 32).toInt =
      ((before.registers base).toInt +
        ((before.registers index).toNat * 2^scale.val : Nat) + displacement.toInt).bmod (2^32) := by
  cases actual
  simp only [State.writeRegister, ↓reduceIte,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  rw [addressLow32_signed, Address.eval_sibDisp8_signed,
    Int.bmod_bmod_of_dvd (by decide : 2^32 ∣ 2^64)]

theorem lea32_effects (before : State) (destination : Register) (address : Address) (prefixed : Bool) :
    (Instruction.lea32 destination address prefixed).operandReads before = [] ∧
    (Instruction.lea32 destination address prefixed).storeIntent before = none ∧
    (Instruction.lea32 destination address prefixed).storeIntent64 before = none ∧
    (Instruction.lea32 destination address prefixed).choiceFlag before = none ∧
    (Instruction.lea32 destination address prefixed).undefinedFlags before = [] ∧
    (Instruction.lea32 destination address prefixed).boolChoiceProfile = true ∧
    CallerOnly (.lea32 destination address prefixed) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩

theorem executeWith_lea32 (before : State) (destination : Register) (address : Address)
    (prefixed : Bool) (choices : FlagChoices) :
    executeWith before (.lea32 destination address prefixed) choices =
      execute before (.lea32 destination address prefixed) false := rfl

end EDSL.X86.Sequential

namespace EDSL.OS.CallResources
open X86 X86.Sequential

/-- Exact current memory authority survives even if the destination is RSP.
This gives no authority to read any newly computed stack address. -/
theorem current_lea32_step {call : Call} {shared : Shared} {before : State}
    {destination : Register} {address : Address} {prefixed : Bool}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.lea32 destination address prefixed)) :
    ∃ after, (∀ choice, step choice before = .ok ⟨.next after, []⟩) ∧
      Current call shared after ∧ Address32Context before after destination address prefixed := by
  obtain ⟨after, executed, context⟩ := execute_lea32_context before destination address prefixed
  exact ⟨after, fun choice => (step_eq_execute choice decoded).trans (executed choice),
    current.sameMemory context.memory, context⟩

end EDSL.OS.CallResources
