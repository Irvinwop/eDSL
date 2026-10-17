/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64.Prefix

set_option warningAsError true

namespace EDSL.CallMemory64.Compiler
open X86 OS

def reads (resource : Resources) : List CallReturn.Read :=
  [⟨.data, resource.descriptor.target, 8⟩,
    ⟨.stack, resource.descriptor.frame.top - 16, 8⟩,
    ⟨.stack, resource.descriptor.frame.top - 8, 8⟩,
    ⟨.stack, resource.descriptor.frame.top, 8⟩]

/-- GCC's actual separate-TU trace returns for every admitted machine state,
every full-width input and every AF choice stream. Its DATA store and all
private writes belong to this same covered mixed execution. -/
theorem gcc_covered {resource : Resources} {initial : State}
    (pre : ResourcePre (program .gccSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      result.instructions = 8 ∧ result.reads = reads resource ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨evolved, history, current, targetReadback⟩ := prefix_covered pre choices
  have slot : StackFrame.Slot resource.descriptor.frame
      ((afterInnerRet initial evolved resource.value).registers .rsp) := by
    rw [stack_afterInnerRet pre]
    exact CallStack.private_slot_at_depth current.contract.stack (by decide : 8 ≤ 8)
      (Nat.le_trans (by decide : 8 ≤ 16) pre.capacity)
  obtain ⟨value, _, observed, _, _⟩ := StackFrame.current_privateSlot current.stack slot
  have popPC : (afterInnerRet initial evolved resource.value).rip = resource.descriptor.frame.call.code + 6 :=
    pc_afterInnerRet pre evolved resource.value
  have popStep := pop_step (profile := .gccSeparate) current pre.code popPC slot observed ((choices.drop 5) 0)
  have popCurrent := popStep.current current
  have incPC : (popped .gccSeparate (afterInnerRet initial evolved resource.value) value).rip =
      resource.descriptor.frame.call.code + 7 := by
    simp [popped, CallReturn.popState, CallReturn.stackLength, popPC, BitVec.add_assoc]
  have incStep := increment_step (profile := .gccSeparate) popCurrent pre.code incPC
    (((choices.drop 5).drop 1) 0)
  have incCurrent := incStep.current popCurrent
  have rootPC : (increment (popped .gccSeparate (afterInnerRet initial evolved resource.value) value)).rip =
      resource.descriptor.frame.call.code + 10 := by
    simp [increment, CallStack.Compiler.increment, incPC, BitVec.add_assoc]
  have stackRoot : (increment (popped .gccSeparate (afterInnerRet initial evolved resource.value) value)).registers .rsp =
      resource.descriptor.frame.top := by
    simp [increment, CallStack.Compiler.increment, popped, popDestination, CallReturn.popState,
      State.writeRegister, stack_afterInnerRet pre, BitVec.sub_add_cancel]
  have rootStep := root_ret_step (profile := .gccSeparate) incCurrent pre.code rootPC stackRoot
    ((((choices.drop 5).drop 1).drop 1) 0)
  have popFetch := node_fetchWithin (current_code (profile := .gccSeparate) current pre.code)
    pre.code .pop popPC
  have incFetch := node_fetchWithin (current_code (profile := .gccSeparate) popCurrent pre.code)
    pre.code .increment incPC
  have rootFetch := node_fetchWithin (current_code (profile := .gccSeparate) incCurrent pre.code)
    pre.code .ret rootPC
  let final := finish (increment (popped .gccSeparate (afterInnerRet initial evolved resource.value) value))
    resource.descriptor.frame.call.returnAddress
  have execution : OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved
      ⟨final, 8, reads resource⟩ := by
    simpa only [Sequential.Result.prepend, List.nil_append, List.append_nil,
      List.singleton_append, List.cons_append, stack_afterInnerRet pre, stackRoot, reads] using
      history.then_execution (.next popStep popFetch (.next incStep incFetch (.ret rootStep rootFetch)))
  have memory := execution.memory_frame pre.current
  have frame : RegisterFrame initial final := (frame_prefix initial evolved resource.value).trans
    ((frame_popped .gccSeparate _ value).trans
      ((CallStack.Compiler.frame_increment _).trans (CallStack.Compiler.frame_finish _ _)))
  refine ⟨evolved, _, execution, rfl, rfl, ?_⟩
  refine ⟨?_, targetReadback, memory.1, memory.2.1, memory.2.2, rfl, ?_, frame.preserved, frame.flags⟩
  · change (resource.value + 1).toNat = resultNat resource.value
    exact one_addition resource.value
  · simp [final, CallStack.Compiler.finish, stackRoot, pre.stack, State.writeRegister]

/-- The independent semantic theorem has no cost, compiler metadata, future
callback, fixed register seed or fixed AF stream in its admission. -/
theorem gcc_semantic :
    ∀ resource initial, ResourcePre (program .gccSeparate) resource initial →
      ∀ choices, ∃ evolved result,
        OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
        Post (resourceInput resource) initial result.state := by
  intro resource initial pre choices
  obtain ⟨evolved, result, execution, _, _, post⟩ := gcc_covered pre choices
  exact ⟨evolved, result, execution, post⟩

/-- The exact actual evaluator, reusable current endpoint and union history
come from the same covered execution as the independent postcondition. -/
theorem gcc_evaluated {resource : Resources} {initial : State}
    (pre : ResourcePre (program .gccSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.runFrom resource.descriptor.frame.top choices 8 initial = .ok result ∧
      OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      OS.CallMemory64.Current resource.descriptor evolved result.state ∧
      OS.CallMemory64.Preservation resource.descriptor resource.shared evolved ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = 8 ∧ result.reads = reads resource := by
  obtain ⟨evolved, result, execution, cost, trace, post⟩ := gcc_covered pre choices
  exact ⟨evolved, result, execution.run (Nat.le_of_eq cost), execution,
    execution.current pre.current, execution.preserves, post, cost, trace⟩

/-- Clang's linked text increments before POP RCX. The common helper prefix
retains its actual store/reload/RET ordering and current resource world. -/
theorem clang_covered {resource : Resources} {initial : State}
    (pre : ResourcePre (program .clangSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      result.instructions = 8 ∧ result.reads = reads resource ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨evolved, history, current, targetReadback⟩ := prefix_covered pre choices
  have incPC : (afterInnerRet initial evolved resource.value).rip = resource.descriptor.frame.call.code + 6 :=
    pc_afterInnerRet pre evolved resource.value
  have incStep := increment_step (profile := .clangSeparate) current pre.code incPC ((choices.drop 5) 0)
  have incCurrent := incStep.current current
  have popPC : (increment (afterInnerRet initial evolved resource.value)).rip =
      resource.descriptor.frame.call.code + 9 := by
    simp [increment, CallStack.Compiler.increment, incPC, BitVec.add_assoc]
  have stackInc : (increment (afterInnerRet initial evolved resource.value)).registers .rsp =
      resource.descriptor.frame.top - 8 := by
    simp [increment, CallStack.Compiler.increment, State.writeRegister, stack_afterInnerRet pre]
  have slot : StackFrame.Slot resource.descriptor.frame
      ((increment (afterInnerRet initial evolved resource.value)).registers .rsp) := by
    rw [stackInc]
    exact CallStack.private_slot_at_depth incCurrent.contract.stack (by decide : 8 ≤ 8)
      (Nat.le_trans (by decide : 8 ≤ 16) pre.capacity)
  obtain ⟨value, _, observed, _, _⟩ := StackFrame.current_privateSlot incCurrent.stack slot
  have popStep := pop_step (profile := .clangSeparate) incCurrent pre.code popPC slot observed
    (((choices.drop 5).drop 1) 0)
  have popCurrent := popStep.current incCurrent
  have rootPC : (popped .clangSeparate (increment (afterInnerRet initial evolved resource.value)) value).rip =
      resource.descriptor.frame.call.code + 10 := by
    simp [popped, CallReturn.popState, CallReturn.stackLength, popPC, BitVec.add_assoc]
  have stackRoot : (popped .clangSeparate (increment (afterInnerRet initial evolved resource.value)) value).registers .rsp =
      resource.descriptor.frame.top := by
    rw [popped_stack, stackInc, BitVec.sub_add_cancel]
  have rootStep := root_ret_step (profile := .clangSeparate) popCurrent pre.code rootPC stackRoot
    ((((choices.drop 5).drop 1).drop 1) 0)
  have incFetch := node_fetchWithin (current_code (profile := .clangSeparate) current pre.code)
    pre.code .increment incPC
  have popFetch := node_fetchWithin (current_code (profile := .clangSeparate) incCurrent pre.code)
    pre.code .pop popPC
  have rootFetch := node_fetchWithin (current_code (profile := .clangSeparate) popCurrent pre.code)
    pre.code .ret rootPC
  let final := finish (popped .clangSeparate (increment (afterInnerRet initial evolved resource.value)) value)
    resource.descriptor.frame.call.returnAddress
  have execution : OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved
      ⟨final, 8, reads resource⟩ := by
    simpa only [Sequential.Result.prepend, List.nil_append, List.append_nil,
      List.singleton_append, List.cons_append, stackInc, stackRoot, reads] using
      history.then_execution (.next incStep incFetch (.next popStep popFetch (.ret rootStep rootFetch)))
  have memory := execution.memory_frame pre.current
  have frame : RegisterFrame initial final := (frame_prefix initial evolved resource.value).trans
    ((CallStack.Compiler.frame_increment _).trans
      ((frame_popped .clangSeparate _ value).trans (CallStack.Compiler.frame_finish _ _)))
  refine ⟨evolved, _, execution, rfl, rfl, ?_⟩
  refine ⟨?_, targetReadback, memory.1, memory.2.1, memory.2.2, rfl, ?_, frame.preserved, frame.flags⟩
  · change (resource.value + 1).toNat = resultNat resource.value
    exact one_addition resource.value
  · simp [final, CallStack.Compiler.finish, stackRoot, pre.stack, State.writeRegister]

theorem covered (profile : Profile) {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      result.instructions = 8 ∧ result.reads = reads resource ∧
      Post (resourceInput resource) initial result.state := by
  cases profile with
  | gccSeparate => exact gcc_covered pre choices
  | clangSeparate => exact clang_covered pre choices

theorem clang_semantic :
    ∀ resource initial, ResourcePre (program .clangSeparate) resource initial →
      ∀ choices, ∃ evolved result,
        OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
        Post (resourceInput resource) initial result.state := by
  intro resource initial pre choices
  obtain ⟨evolved, result, execution, _, _, post⟩ := clang_covered pre choices
  exact ⟨evolved, result, execution, post⟩

theorem evaluated (profile : Profile) {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.runFrom resource.descriptor.frame.top choices 8 initial = .ok result ∧
      OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      OS.CallMemory64.Current resource.descriptor evolved result.state ∧
      OS.CallMemory64.Preservation resource.descriptor resource.shared evolved ∧
      Post (resourceInput resource) initial result.state ∧
      result.instructions = 8 ∧ result.reads = reads resource := by
  obtain ⟨evolved, result, execution, cost, trace, post⟩ := covered profile pre choices
  exact ⟨evolved, result, execution.run (Nat.le_of_eq cost), execution,
    execution.current pre.current, execution.preserves, post, cost, trace⟩

end EDSL.CallMemory64.Compiler
