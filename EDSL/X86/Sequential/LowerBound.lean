/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Return

set_option warningAsError true

namespace EDSL.X86.Sequential

/-- An actual terminal step is RET and preserves every register except RSP.
There is no candidate-code, read-only, ABI or current-resource premise. -/
theorem step_returned_register {initial final : State} {af : Bool} {reads : List Read}
    (actual : step af initial = .ok ⟨.returned final, reads⟩)
    (register : Register) (different : register ≠ .rsp) :
    final.registers register = initial.registers register := by
  cases decoded : Sequential.decodeAt initial with
  | error fault => simp [step, decoded] at actual
  | ok instruction =>
    rw [step_eq_execute af decoded] at actual
    have onlyRet := execute_returned_only_ret actual rfl
    subst instruction
    cases loaded : readWord initial.memory (initial.registers .rsp) with
    | error fault => simp [execute, X86.executeInstruction, executeRet, loaded] at actual
    | ok target =>
      cases valid : canonical target <;>
        simp [execute, X86.executeInstruction, executeRet, loaded, valid] at actual
      rcases actual with ⟨rfl, rfl⟩
      simp [State.writeRegister, different]

/-- Every returning execution that changes a non-RSP register retires at least
two modeled instructions. Atomic prefixes are included. This bound depends
 only on the actual sequential ISA and return semantics, not a program shape. -/
theorem Executes.changed_register_needs_two {choices : Choices} {initial : State} {result : Result}
    (actual : Sequential.Executes choices initial result) (register : Register)
    (different : register ≠ .rsp)
    (changed : result.state.registers register ≠ initial.registers register) :
    2 ≤ result.instructions := by
  cases actual with
  | ret terminal => exact False.elim (changed (step_returned_register terminal register different))
  | next _ tail | atomic _ tail =>
    have positive := Engine.Executes.positive Sequential.step tail
    simp only [Result.prepend]
    omega

end EDSL.X86.Sequential
