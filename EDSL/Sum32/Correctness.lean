/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Initialization
import EDSL.Sum32.Pointer
import EDSL.Sum32.Index
import EDSL.Sum32.Check

namespace EDSL.Sum32
open X86

theorem Initialized.finish {bytes : List Byte} {plan : Plan} {initial middle final : State}
    {values : List (BitVec 32)} {target : Word}
    (ready : Initialized bytes plan initial values target middle) (valid : Valid bytes plan)
    (returned : LoopPost middle 0 values target final) : Post initial values target final := by
  have result := returned.zero
  refine ⟨result.value, result.memory.trans ready.effect.memory, result.returnAddress, ?_, ?_,
    result.flags.trans ready.effect.flags⟩
  · rw [result.stackPointer, ready.stackPointer]
  · intro register outside
    exact (result.preserved register outside).trans (ready.preserved valid register outside)

/-- Every admitted input has a complete actual execution for EVERY sequence
of undefined AF choices. The code is checked structurally against one shared
mathematical contract; no successful future evaluator run is an input premise. -/
theorem executes {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post initial values target result.state ∧
      result.instructions = plan.cost values.length ∧ result.reads = operandReads initial values := by
  obtain ⟨middle, prefixBlock, ready⟩ := initialization_enabled valid admitted choices
  have updatesValid := (Bool.and_eq_true_iff.mp valid.shape).2
  cases mode : plan.mode with
  | pointerCount =>
    obtain ⟨result, execution, returned, cost, reads⟩ :=
      pointer_loop valid mode ready.pointer (choices.drop plan.prologue.length)
    have updateCount : plan.updates.length = 2 := by
      simpa only [mode] using plan.updates_length updatesValid
    refine ⟨result.prepend plan.prologue.length [], prefixBlock.then_executes execution,
      ready.finish valid returned, ?_, ?_⟩
    · change plan.prologue.length + result.instructions = plan.cost values.length
      rw [cost]
      simp only [Plan.cost, updateCount]
      omega
    · change [] ++ result.reads = operandReads initial values
      simpa only [List.nil_append, pointerReads, operandReads, ready.base, ready.stackPointer] using reads
  | index =>
    obtain ⟨result, execution, returned, cost, reads⟩ :=
      index_loop valid mode (ready.indexed mode) (choices.drop plan.prologue.length)
    have updateCount : plan.updates.length = 1 := by
      simpa only [mode] using plan.updates_length updatesValid
    refine ⟨result.prepend plan.prologue.length [], prefixBlock.then_executes execution,
      ready.finish valid returned, ?_, ?_⟩
    · change plan.prologue.length + result.instructions = plan.cost values.length
      rw [cost]
      simp only [Plan.cost, updateCount]
      omega
    · change [] ++ result.reads = operandReads initial values
      simpa [indexReads, operandReads, ready.base, ready.stackPointer] using reads

theorem all_executions {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) :
    Sequential.AllExecutions initial (fun result => Post initial values target result.state ∧
      result.instructions = plan.cost values.length ∧ result.reads = operandReads initial values) := by
  intro choices
  exact executes valid admitted choices

/-- An explicit terminating evaluator bound follows from the verified loops;
fuel success is a conclusion, and input lengths remain symbolic. -/
theorem sound {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (plan.cost values.length) initial = .ok result ∧
      Post initial values target result.state ∧ result.instructions = plan.cost values.length ∧
      result.reads = operandReads initial values := by
  obtain ⟨result, execution, post, cost, reads⟩ := executes valid admitted choices
  exact ⟨result, Sequential.run_complete execution (Nat.le_of_eq cost), post, cost, reads⟩

theorem checked_sound {bytes : List Byte} {plan : Plan} (accepted : check bytes = some plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (plan.cost values.length) initial = .ok result ∧
      Post initial values target result.state ∧ result.instructions = plan.cost values.length ∧
      result.reads = operandReads initial values :=
  sound (check_sound accepted) admitted choices

theorem no_divergence {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) : ¬ Sequential.Diverges initial :=
  (all_executions valid admitted).no_divergence

theorem safe {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) : Sequential.Safe initial :=
  (all_executions valid admitted).safe

end EDSL.Sum32
