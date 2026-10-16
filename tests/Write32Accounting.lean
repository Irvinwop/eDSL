/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Accounting
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.Write32Accounting
open X86 X86.Sequential Grading OS

-- The Useful hypothesis is essential: on already-equal inputs an actual RET
-- satisfies the independent Post in one instruction. This does not establish
-- the universal task Claim for RET-only code, which useful inputs refute.
theorem already_equal_ret {input initial} (pre : Write32.Pre [0xc3] input initial)
    (equal : input.oldValue = input.argument.setWidth 32) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Write32.Post input initial result.state ∧ result.instructions = 1 := by
  let final := WordResources.returnAfter initial input.returnAddress
  have first := pre.code.2 0 0xc3 (by decide)
  simp only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] at first
  have decoded : Sequential.decodeAt initial = .ok (.legacy .ret) := by
    apply decodeAt_legacy
    simp [X86.decodeAt, first]
  have actual : Sequential.step (choices 0) initial =
      .ok ⟨.returned final, [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
    rw [step_eq_execute _ decoded]
    simp [Sequential.execute, X86.executeInstruction, executeRet, pre.stack,
      pre.returnCanonical, Sequential.Instruction.operandReads, final, WordResources.returnAfter]
  refine ⟨⟨final, 1, [⟨.stack, initial.registers .rsp, 8⟩]⟩,
    Sequential.Executes.ret actual, ?_, rfl⟩
  refine ⟨?_, (by intros; rfl), rfl, rfl, rfl, ?_, ?_, rfl⟩
  · exact pre.oldValue.trans (congrArg Except.ok equal)
  · simp [final, WordResources.returnAfter, State.writeRegister]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same
      subst register
      simp [Write32.calleeSaved] at member
    simp [final, WordResources.returnAfter, State.writeRegister, notStack]

-- Exhibit an admitted, writable target and real caller slot for that boundary
-- case, using the decoder-independent OS world rather than a successful-run
-- precondition. No-op rejection on useful inputs remains in GradingWrite.
theorem one_instruction_possible : ∃ input initial result,
    Write32.Pre [0xc3] input initial ∧ ¬Write32.Useful input ∧
    Sequential.Executes (fun _ => false) initial result ∧
    Write32.Post input initial result.state ∧ result.instructions = 1 := by
  let witness := Write32.Domain.candidate [0xc3] (by decide) (by decide)
  let initial : State := { witness.initial with registers := fun register =>
    if register = .rsi then 0 else witness.initial.registers register }
  let input : Write32.Input :=
    ⟨witness.call.targetPointer, 0, witness.oldValue, witness.call.returnAddress⟩
  have pre : Write32.Pre [0xc3] input initial := by
    refine ⟨witness.raw.code, ?_, ?_, witness.raw.old, witness.raw.writable,
      witness.raw.codeDisjoint, ?_, ?_, witness.raw.returnCanonical, ?_, ?_⟩
    · simpa [initial] using witness.raw.targetPointer
    · simp [initial, input]
    · simpa [initial] using witness.raw.stackDisjoint
    · simpa [initial] using witness.raw.stack
    · simpa [initial] using witness.raw.stackBound
    · simpa [initial] using witness.raw.postStackCanonical
  have equal : input.oldValue = input.argument.setWidth 32 := rfl
  obtain ⟨result, execution, post, cost⟩ := already_equal_ret pre equal (fun _ => false)
  exact ⟨input, initial, result, pre, fun useful => useful equal, execution, post, cost⟩

end EDSL.Tests.Write32Accounting

#audit_edsl
