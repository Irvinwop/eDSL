/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedSet64.Execution

namespace EDSL.X86.LockedSet64

def Instruction.ofOld : LockedLogical64.Instruction → Instruction
  | .orRdiRsi => .logicalRdiRsi .bor
  | .ret => .ret

/-- Execute equality includes failures, for the old OR instruction only. -/
theorem execute_oldOR (state : State) (af : Bool) :
    execute state (.logicalRdiRsi .bor) af =
      LockedLogical64.execute state .orRdiRsi af := rfl

theorem execute_oldRet (state : State) (af : Bool) :
    execute state .ret af = LockedLogical64.execute state .ret af := rfl

theorem execute_of_old (state : State) (instruction : LockedLogical64.Instruction) (af : Bool) :
    execute state (Instruction.ofOld instruction) af = LockedLogical64.execute state instruction af := by
  cases instruction <;> rfl

/-- Only successful old decodes embed; AND/XOR are intentionally newly admitted. -/
theorem decodeAt_of_old {state : State} {instruction : LockedLogical64.Instruction}
    (decoded : LockedLogical64.decodeAt state = .ok instruction) :
    decodeAt state = .ok (Instruction.ofOld instruction) := by
  apply decodeAt_of_code
  have code := LockedLogical64.decodeAt_code decoded
  cases instruction <;> exact code

theorem old_successful_step {initial : State} {af : Bool} {observation : Observation}
    (success : LockedLogical64.step af initial = .ok observation) :
    step af initial = .ok observation := by
  obtain ⟨instruction, decoded, executed⟩ := LockedLogical64.step_sound success
  rw [step_eq_execute af (decodeAt_of_old decoded), execute_of_old]
  exact executed

/-- The old event/access/result types are operation neutral and shared exactly. -/
theorem Executes.of_old {choices : Choices} {initial : State} {result : Result}
    (execution : LockedLogical64.Executes choices initial result) :
    Executes choices initial result := by
  induction execution with
  | ret actual => exact .ret (old_successful_step actual)
  | atomic64 actual tail induction => exact .atomic64 (old_successful_step actual) induction

theorem run_eq_old_of_executes {choices : Choices} {initial : State} {result : Result}
    (execution : LockedLogical64.Executes choices initial result) (fuel : Nat) :
    run choices fuel initial = LockedLogical64.run choices fuel initial := by
  rw [(Executes.of_old execution).run_eq, execution.run_eq]

end EDSL.X86.LockedSet64
