/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.PointerSteps

namespace EDSL.Sum32
open X86

/-- Every checked pointer/count loop terminates from its header for every AF
choice stream. The prologue is independent and is not executed by this theorem.
The result binds the actual machine execution to the independent modular sum,
complete memory/ABI frame, exact retired-instruction count and operand reads. -/
theorem pointer_loop {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state values accumulator target)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices state result ∧
      LoopPost state accumulator values target result.state ∧
      result.instructions = 6 * values.length + 3 ∧
      result.reads = pointerReads state values := by
  induction values generalizing state accumulator choices with
  | nil => simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
      PointerProof.finish valid mode header choices
  | cons value values induction =>
    obtain ⟨middle, block, nextHeader, pointer, frame⟩ :=
      PointerProof.iteration valid mode header choices
    obtain ⟨result, execution, post, cost, reads⟩ := induction nextHeader (choices.drop 6)
    refine ⟨result.prepend 6 [⟨.data, state.registers .rdi, 4⟩],
      block.then_executes execution, ?_, ?_, ?_⟩
    · change LoopPost state accumulator (value :: values) target result.state
      refine ⟨?_, post.memory.trans frame.memory, post.returnAddress, ?_, ?_,
        post.flags.trans frame.flags⟩
      · simpa only [sum32_cons, BitVec.add_assoc] using post.value
      · rw [post.stackPointer, frame.stack]
      · intro register allowed
        exact (post.preserved register allowed).trans (frame.preserved register allowed)
    · change 6 + result.instructions = 6 * (value :: values).length + 3
      rw [cost, List.length_cons]
      omega
    · change [⟨.data, state.registers .rdi, 4⟩] ++ result.reads = pointerReads state (value :: values)
      rw [reads]
      simp only [pointerReads, inputReads, pointer, frame.stack, List.cons_append, List.nil_append]

/-- All choices have a finite actual execution satisfying the complete loop contract. -/
theorem pointer_all_executions {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state values accumulator target) :
    Sequential.AllExecutions state (fun result =>
      LoopPost state accumulator values target result.state ∧
      result.instructions = 6 * values.length + 3 ∧ result.reads = pointerReads state values) :=
  pointer_loop valid mode header

theorem pointer_run {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state values accumulator target)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (6 * values.length + 3) state = .ok result ∧
      LoopPost state accumulator values target result.state ∧
      result.instructions = 6 * values.length + 3 ∧ result.reads = pointerReads state values :=
  (pointer_all_executions valid mode header).run (fun _ contract => contract.2.1) choices

theorem pointer_no_fault_prefix {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state values accumulator target)
    (choices : Sequential.Choices) {fuel : Nat} {fault : Error}
    (failed : Sequential.run choices fuel state = .error fault) : fault = .exhaustedFuel :=
  (pointer_all_executions valid mode header).no_fault_prefix choices failed

theorem pointer_no_divergence {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state values accumulator target) :
    ¬ Sequential.Diverges state :=
  (pointer_all_executions valid mode header).no_divergence

end EDSL.Sum32
