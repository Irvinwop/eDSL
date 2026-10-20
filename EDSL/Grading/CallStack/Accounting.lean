/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Contract
import EDSL.X86.CallReturn.LowerBound

set_option warningAsError true

namespace EDSL.Grading.CallStack
open X86 EDSL.CallStack

/-- Every accepted implementation needs at least two modeled instructions on
an admitted input requiring RAX to change. This is separate from acceptance,
which fixes neither instruction selection nor an instruction budget. -/
theorem minimum_modeled_instructions {program} (claim : Claim program)
    {resource initial choices result} (pre : ResourcePre program resource initial)
    (useful : Useful resource initial) (actual : CallReturn.Executes choices initial result) :
    2 ≤ result.instructions := by
  obtain ⟨evolved, returned⟩ := claim.all_results pre actual
  have changed : result.state.registers .rax ≠ initial.registers .rax := by
    intro same
    have natural := congrArg BitVec.toNat same
    exact useful (natural.symm.trans returned.post.value)
  exact CallReturn.ExecutesFrom.changed_rax_needs_two actual changed

theorem minimum_run {program} (claim : Claim program)
    {resource initial choices fuel result} (pre : ResourcePre program resource initial)
    (useful : Useful resource initial)
    (actual : CallReturn.run choices fuel initial = .ok result) :
    2 ≤ result.instructions := minimum_modeled_instructions claim pre useful (CallReturn.run_sound actual)

end EDSL.Grading.CallStack
