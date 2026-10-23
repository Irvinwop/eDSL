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

theorem execute_testImm8 (before : State) (operand : Register) (immediate : Byte)
    (prefixed af : Bool) :
    execute before (.testImm8 operand immediate prefixed) af =
      .ok ⟨.next { before with
        rip := before.rip + BitVec.ofNat 64 (if prefixed then 4 else 3)
        flags := logicalFlags8 before.flags ((before.registers operand).setWidth 8 &&& immediate) af },
        []⟩ := rfl

/-- The mathematical byte mask uses the raw immediate, including its bit7.
Dirty upper56 operand bits have no role in either the result or its flags. -/
theorem testImm8_result_toNat (value : Word) (immediate : Byte) :
    (value.setWidth 8 &&& immediate).toNat = (value.toNat % 256) &&& immediate.toNat := by
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]

/-- Entire register file and RAM/permissions survive. The only status-bit
freedom is AF, whose value comes from the choice rather than the old flags. -/
structure TestImmediate8Context (before after : State) (operand : Register)
    (immediate : Byte) (prefixed af : Bool) : Prop where
  registers : after.registers = before.registers
  memory : after.memory = before.memory
  carry : after.flags.getLsbD 0 = false
  parity : after.flags.getLsbD 2 = evenParity ((before.registers operand).setWidth 8 &&& immediate)
  auxiliary : after.flags.getLsbD 4 = af
  zero : after.flags.getLsbD 6 = ((before.registers operand).setWidth 8 &&& immediate == 0)
  sign : after.flags.getLsbD 7 = ((before.registers operand).setWidth 8 &&& immediate).msb
  overflow : after.flags.getLsbD 11 = false
  frame : after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask
  rip : after.rip = before.rip + BitVec.ofNat 64 (if prefixed then 4 else 3)

theorem execute_testImm8_context (before : State) (operand : Register) (immediate : Byte)
    (prefixed af : Bool) :
    ∃ after, execute before (.testImm8 operand immediate prefixed) af = .ok ⟨.next after, []⟩ ∧
      TestImmediate8Context before after operand immediate prefixed af := by
  refine ⟨_, rfl, ?_⟩
  have bits := logicalFlags8_bits before.flags ((before.registers operand).setWidth 8 &&& immediate) af
  exact ⟨rfl, rfl, bits.1, bits.2.1, bits.2.2.1, bits.2.2.2.1,
    bits.2.2.2.2.1, bits.2.2.2.2.2, logicalFlags8_preserves .., rfl⟩

/-- Architectural defined flags plus the nonarithmetic frame exactly describe
all modeled results. AF has no constraint in this independent predicate. -/
theorem execute_testImm8_admissible_iff (before : State) (operand : Register)
    (immediate : Byte) (prefixed : Bool) (actual : Word) :
    (∃ af, execute before (.testImm8 operand immediate prefixed) af =
      .ok ⟨.next { before with
        rip := before.rip + BitVec.ofNat 64 (if prefixed then 4 else 3)
        flags := actual }, []⟩) ↔
      LogicalFlagsAdmissible before.flags actual
        (evenParity ((before.registers operand).setWidth 8 &&& immediate))
        ((before.registers operand).setWidth 8 &&& immediate == 0)
        ((before.registers operand).setWidth 8 &&& immediate).msb := by
  rw [logicalFlags8_admissible_iff]
  constructor
  · rintro ⟨af, success⟩
    refine ⟨af, ?_⟩
    rw [execute_testImm8] at success
    have same := congrArg (fun observation : Observation => match observation.result with
      | .next final => final.flags | _ => 0) (Except.ok.inj success)
    exact same.symm
  · rintro ⟨af, same⟩
    refine ⟨af, ?_⟩
    rw [execute_testImm8, ←same]

theorem testImm8_effects (before : State) (operand : Register) (immediate : Byte) (prefixed : Bool) :
    (Instruction.testImm8 operand immediate prefixed).operandReads before = [] ∧
    (Instruction.testImm8 operand immediate prefixed).storeIntent before = none ∧
    (Instruction.testImm8 operand immediate prefixed).storeIntent64 before = none ∧
    (Instruction.testImm8 operand immediate prefixed).choosesAF = true ∧
    (Instruction.testImm8 operand immediate prefixed).choiceFlag before = some .af ∧
    (Instruction.testImm8 operand immediate prefixed).undefinedFlags before = [.af] ∧
    (Instruction.testImm8 operand immediate prefixed).boolChoiceProfile = true ∧
    CallerOnly (.testImm8 operand immediate prefixed) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩

theorem executeWith_testImm8 (before : State) (operand : Register) (immediate : Byte)
    (prefixed : Bool) (choices : FlagChoices) :
    executeWith before (.testImm8 operand immediate prefixed) choices =
      execute before (.testImm8 operand immediate prefixed) (choices.get .af) := rfl

/-- Changing any inactive vector component has no effect. AF can vary
independently even when all five other choice bits disagree. -/
theorem executeWith_testImm8_agreement (before : State) (operand : Register) (immediate : Byte)
    (prefixed : Bool) (left right : FlagChoices)
    (agree : FlagChoices.Agreement [.af] left right) :
    executeWith before (.testImm8 operand immediate prefixed) left =
      executeWith before (.testImm8 operand immediate prefixed) right := by
  rw [executeWith_testImm8, executeWith_testImm8, agree .af (by simp)]

/-- Both AF outcomes are represented, and only the named bit differs.
This is a model of undefined behavior of a flag, with no physical claim. -/
theorem execute_testImm8_choices (before : State) (operand : Register) (immediate : Byte)
    (prefixed left right : Bool) :
    ∃ first second,
      execute before (.testImm8 operand immediate prefixed) left = .ok ⟨.next first, []⟩ ∧
      execute before (.testImm8 operand immediate prefixed) right = .ok ⟨.next second, []⟩ ∧
      first.registers = second.registers ∧ first.memory = second.memory ∧ first.rip = second.rip ∧
      first.flags &&& ~~~(0x10 : Word) = second.flags &&& ~~~(0x10 : Word) ∧
      first.flags.getLsbD 4 = left ∧ second.flags.getLsbD 4 = right :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, logicalFlags8_choices ..,
    (logicalFlags8_bits ..).2.2.1, (logicalFlags8_bits ..).2.2.1⟩

end EDSL.X86.Sequential

namespace EDSL.OS.CallResources
open X86 X86.Sequential

theorem current_testImm8_step {call : Call} {shared : Shared} {before : State}
    {operand : Register} {immediate : Byte} {prefixed : Bool}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.testImm8 operand immediate prefixed)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧ Current call shared after ∧
      TestImmediate8Context before after operand immediate prefixed af := by
  obtain ⟨after, executed, context⟩ := execute_testImm8_context before operand immediate prefixed af
  exact ⟨after, (step_eq_execute af decoded).trans executed,
    current.sameMemory context.memory, context⟩

end EDSL.OS.CallResources
