/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ExecutionChoices
import EDSL.WordMath.Multiplication
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.FlagChoiceExecution
open X86 X86.Sequential

/- XOR EAX,EAX; ROL RAX,CL; RET. XOR chooses AF; rotation by two
chooses OF and retains AF. The literal expected flag words below check that
components and instruction indices are selected independently. -/
private def code : List Byte := [0x31, 0xc0, 0x48, 0xd3, 0xc0, 0xc3]

private def initial : State where
  registers r := if r = .rsp then 32768 else if r = .rcx then 2 else 0xdeadbeef
  rip := 4096
  flags := 0x202
  memory := {
    read := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4102 then
        code[address.toNat - 4096]?
      else if 32768 ≤ address.toNat ∧ address.toNat < 32776 then
        [0, 0x20, 0, 0, 0, 0, 0, 0][address.toNat - 32768]?
      else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4102)
    writable := fun _ => false }

/-- Opposite inactive bits expose wrong-component selection. Choices after
RET deliberately differ as well, so ignoring fuel/return boundaries is visible. -/
private def choices (af of : Bool) : ChoiceStream FlagChoices := fun index =>
  if index = 0 then ⟨true, true, af, true, true, !of⟩
  else if index = 1 then ⟨true, false, !af, false, false, of⟩
  else FlagChoices.uniform true

private structure RunSummary where
  value : Word
  flags : Word
  rip : Word
  rsp : Word
  instructions : Nat
  reads : List Read
  deriving DecidableEq

private def observe (af of : Bool) (fuel : Nat) :
    Option RunSummary := do
  let result ← (runWith (choices af of) fuel initial).toOption
  return ⟨result.state.registers .rax, result.state.flags, result.state.rip,
    result.state.registers .rsp, result.instructions, result.reads⟩

/-- All four observable combinations cross two actual decoded instruction
boundaries; RET contributes the real stack read and exact final PC/SP. -/
theorem independent_instruction_choices :
    observe false false 3 = some ⟨0, 0x246, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]⟩ ∧
    observe false true 3 = some ⟨0, 0xa46, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]⟩ ∧
    observe true false 3 = some ⟨0, 0x256, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]⟩ ∧
    observe true true 3 = some ⟨0, 0xa56, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]⟩ := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Two instructions are insufficient to execute the third instruction RET. -/
theorem short_fuel_rejected : observe false true 2 = none := by rfl

/-- A vector adapter must preserve failed actual byte fetches too. -/
theorem missing_code_rejected :
    stepWith (FlagChoices.uniform true) { initial with rip := 0 } =
      .error (.inaccessibleInstruction 0) := by rfl

#audit_edsl
end EDSL.Tests.FlagChoiceExecution
