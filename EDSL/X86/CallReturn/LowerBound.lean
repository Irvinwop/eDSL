/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Execution

set_option warningAsError true

namespace EDSL.X86.CallReturn

/-- A terminal instruction is the actual original-slot RET. It changes RSP
and RIP, while retaining RAX, regardless of code or resource policies. -/
theorem boundaryStep_returned_rax {originalSlot : Word} {before after : State}
    {af : Bool} {reads : List Read}
    (actual : boundaryStep originalSlot af before = .ok ⟨.returned after, reads⟩) :
    after.registers .rax = before.registers .rax := by
  obtain ⟨_, _, target, _, _, same, _⟩ := boundaryStep_terminal_iff.mp actual
  rw [same]
  simp [State.writeRegister]

/-- Within this concrete ISA/return-boundary model, changing RAX and returning
requires at least two retired instructions. Atomic prefixes are covered, and
no client policy or assumed instruction selection is needed. -/
theorem ExecutesFrom.changed_rax_needs_two {originalSlot : Word} {choices : Choices}
    {initial : State} {result : Result}
    (actual : ExecutesFrom originalSlot choices initial result)
    (changed : result.state.registers .rax ≠ initial.registers .rax) :
    2 ≤ result.instructions := by
  cases actual with
  | ret step => exact False.elim (changed (boundaryStep_returned_rax step))
  | next _ tail | atomic _ tail =>
    have positive := ExecutesFrom.positive tail
    simp only [Sequential.Result.prepend]
    omega

end EDSL.X86.CallReturn
