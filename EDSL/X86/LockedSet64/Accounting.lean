/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedSet64.Execution

namespace EDSL.X86.LockedSet64

/-- An event-free return contains only RET in this deliberately restricted
profile. The fact comes from actual step effects, not from a cost assignment. -/
theorem Executes.memory_of_no_events {choices : Choices} {initial : State} {output : Result}
    (execution : Executes choices initial output) (empty : output.events = []) :
    output.state.memory = initial.memory := by
  cases execution with
  | ret actual => exact (step_returned_sound actual).2.1.memory
  | atomic64 _ _ => simp [Result.prepend] at empty

/-- Any returning execution that changes an observed byte needs an RMW plus
RET. This lower bound counts retired instructions ONLY in the logical/RET profile;
it is not a global x86 instruction, micro-op, time or source-level optimum. -/
theorem Executes.changed_byte_lower_bound {choices : Choices} {initial : State} {output : Result}
    (execution : Executes choices initial output) (address : Word)
    (changed : output.state.memory.read address ≠ initial.memory.read address) :
    2 ≤ output.instructions := by
  have nonempty : output.events ≠ [] := by
    intro empty
    exact changed (congrArg (fun memory : Memory => memory.read address)
      (execution.memory_of_no_events empty))
  have count := execution.event_count
  have length : 0 < output.events.length := List.length_pos_iff.mpr nonempty
  omega

end EDSL.X86.LockedSet64
