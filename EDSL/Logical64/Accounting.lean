/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Resources
import EDSL.X86.Sequential.LowerBound

set_option warningAsError true

namespace EDSL.Logical64
open X86 X86.Sequential

/-- A returning implementation must retire at least two instructions when
its independent mathematical answer differs from incoming RAX. This covers
all sequential instructions, including atomic prefixes, without fixing a CFG,
compiler or instruction selection. It is not a physical timing bound. -/
theorem minimum_modeled_instructions {operation : Operation} {input : Input}
    {choices : Choices} {initial : State} {result : Result}
    (execution : Sequential.Executes choices initial result)
    (post : Post operation input initial result.state)
    (needed : ¬MathematicalResult operation input.left input.right (initial.registers .rax)) :
    2 ≤ result.instructions := by
  have changed : result.state.registers .rax ≠ initial.registers .rax := by
    intro same
    have answer := post.result
    rw [same] at answer
    exact needed answer
  exact execution.changed_register_needs_two .rax (by decide) changed

/-- A universal claim supplies the result for the caller's actual execution.
The admission remains independent of cost and future successful execution. -/
theorem claim_minimum {operation : Operation} {bytes : List Byte} {input : Input}
    {choices : Choices} {initial : State} {result : Result}
    (claim : Grading.ReadOnlySemanticClaim (readOnlyTask operation) bytes)
    (pre : Pre bytes input initial)
    (needed : ¬MathematicalResult operation input.left input.right (initial.registers .rax))
    (execution : Sequential.Executes choices initial result) :
    2 ≤ result.instructions := by
  have post : Post operation input initial result.state :=
    Sequential.AllExecutions.project (claim.machine input initial pre).1 ⟨choices,execution⟩
  exact minimum_modeled_instructions execution post needed

end EDSL.Logical64
