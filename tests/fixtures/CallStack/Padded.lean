/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.State
import EDSL.CallStack.Frame

set_option warningAsError true

namespace EDSL.CallStack.Compiler.Padded
open X86 OS

def afterPush (initial : State) : State := pushed initial
def afterCall (profile : Profile) (initial : State) : State := called profile (afterPush initial)
def afterHelper (profile : Profile) (initial : State) : State := helper (afterCall profile initial)
def afterInnerRet (profile : Profile) (initial : State) : State :=
  finish (afterHelper profile initial) (CallReturn.returnAddress (afterPush initial))

theorem stack_afterPush {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterPush initial).registers .rsp = resource.frame.top - 8 := by
  simp [afterPush, pushed, CallReturn.pushState, CallReturn.stackDestination,
    State.writeRegister, pre.stack]

theorem stack_afterHelper {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterHelper profile initial).registers .rsp = resource.frame.top - 16 := by
  simp [afterHelper, helper, afterCall, called, CallReturn.callState, CallReturn.leaState,
    State.writeRegister, CallReturn.stackDestination, stack_afterPush pre, BitVec.sub_sub]

theorem stack_afterInnerRet {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterInnerRet profile initial).registers .rsp = resource.frame.top - 8 := by
  simp [afterInnerRet, finish, State.writeRegister, stack_afterHelper pre,
    BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem pc_afterPush {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (pad : padded profile = true) :
    (afterPush initial).rip = resource.frame.call.code + BitVec.ofNat 64 (offset profile .call) := by
  cases profile <;> simp_all [padded, afterPush, pushed, CallReturn.pushState,
    CallReturn.stackLength, program, entry, offset, pre.entry, BitVec.add_assoc]

theorem pc_afterHelper {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (pad : padded profile = true) :
    (afterHelper profile initial).rip =
      resource.frame.call.code + BitVec.ofNat 64 (offset profile .innerRet) := by
  have pc := call_target (pc_afterPush pre pad)
  change (afterCall profile initial).rip = _ at pc
  cases profile <;> simp_all [padded, afterHelper, helper, CallReturn.leaState,
    CallReturn.Instruction.length, offset, BitVec.add_assoc]

theorem pc_afterInnerRet {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (pad : padded profile = true) :
    (afterInnerRet profile initial).rip =
      resource.frame.call.code + BitVec.ofNat 64 (offset profile (continuation profile)) := by
  exact call_continuation (pc_afterPush pre pad)

/-- Both private writes arise from the actual decoded instructions, in order;
RET consumes the second write's current RAM value. -/
theorem prefix_checked {profile : Profile} {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (pad : padded profile = true)
    (choices : CallReturn.Choices) :
    ∃ evolved,
      StackFrame.CPU.History resource.frame choices resource.shared initial evolved
        (afterInnerRet profile initial) 4 [⟨.stack, resource.frame.top - 16, 8⟩] ∧
      StackFrame.Current resource.frame evolved (afterInnerRet profile initial) := by
  have pushSlot : StackFrame.Slot resource.frame (CallReturn.stackDestination initial) := by
    rw [CallReturn.stackDestination, pre.stack]
    exact private_slot_at_depth pre.current.contract (by decide : 8 ≤ 8) (Nat.le_trans (by decide : 8 ≤ 16) pre.capacity)
  have pushPC : initial.rip = resource.frame.call.code + BitVec.ofNat 64 (offset profile .push) := by
    cases profile with
    | gccSame => cases pad
    | gccSeparate => exact pre.entry
    | clangSame => exact pre.entry
    | clangSeparate => exact pre.entry
  obtain ⟨pushedWorld, pushStep, pushCurrent, _⟩ :=
    push_enabled pre.current pre.code pad pushPC pushSlot (choices 0)
  have callSlot : StackFrame.Slot resource.frame (CallReturn.stackDestination (afterPush initial)) := by
    rw [CallReturn.stackDestination, stack_afterPush pre, BitVec.sub_sub]
    exact private_slot_at_depth pushCurrent.contract (by decide : 8 ≤ 16) pre.capacity
  obtain ⟨calledWorld, callStep, callCurrent, readback⟩ :=
    call_enabled pushCurrent pre.code (pc_afterPush pre pad) callSlot ((choices.drop 1) 0)
  have helperPC : (afterCall profile initial).rip =
      resource.frame.call.code + BitVec.ofNat 64 (offset profile .helper) :=
    call_target (pc_afterPush pre pad)
  have helperStep := helper_step callCurrent pre.code helperPC (((choices.drop 1).drop 1) 0)
  have helperCurrent := helperStep.current callCurrent
  have innerSlot : StackFrame.Slot resource.frame ((afterHelper profile initial).registers .rsp) := by
    rw [stack_afterHelper pre]
    exact private_slot_at_depth helperCurrent.contract (by decide : 8 ≤ 16) pre.capacity
  have loaded : readWord (afterHelper profile initial).memory
      ((afterHelper profile initial).registers .rsp) = .ok (CallReturn.returnAddress (afterPush initial)) := by
    simpa only [afterPush, afterHelper, helper, CallReturn.leaState, State.writeRegister,
      afterCall, called, CallReturn.callState, show Register.rsp ≠ .rax by decide,
      ite_false, ite_true] using readback
  have innerStep := inner_ret_step helperCurrent pre.code (pc_afterHelper pre pad)
    innerSlot loaded (call_addresses (current_code pushCurrent pre.code) (pc_afterPush pre pad)).2
    ((((choices.drop 1).drop 1).drop 1) 0)
  refine ⟨calledWorld, ?_, innerStep.current helperCurrent⟩
  have history : StackFrame.CPU.History resource.frame choices resource.shared initial calledWorld
      (afterInnerRet profile initial) 4 [⟨.stack, (afterHelper profile initial).registers .rsp, 8⟩] :=
    .next pushStep (.next callStep (.next helperStep (.next innerStep .nil)))
  simpa only [stack_afterHelper pre] using history


theorem frame_prefix (profile : Profile) (initial : State) :
    RegisterFrame initial (afterInnerRet profile initial) :=
  (frame_pushed initial).trans ((frame_called profile _).trans
    ((frame_helper _).trans (frame_finish _ _)))

/-- The separate-TU GCC program restores its padding slot before INC. This
whole execution includes both checked owner mutations and the original RET. -/
theorem gcc_correct {resource : Resources} {initial : State}
    (pre : ResourcePre (program .gccSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved result ∧
      result.instructions = 7 ∧
      result.reads = [⟨.stack, resource.frame.top - 16, 8⟩,
        ⟨.stack, resource.frame.top - 8, 8⟩, ⟨.stack, resource.frame.top, 8⟩] ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨evolved, history, current⟩ := prefix_checked pre rfl choices
  have slot : StackFrame.Slot resource.frame ((afterInnerRet .gccSeparate initial).registers .rsp) := by
    rw [stack_afterInnerRet pre]
    exact private_slot_at_depth current.contract (by decide : 8 ≤ 8) (Nat.le_trans (by decide : 8 ≤ 16) pre.capacity)
  obtain ⟨value, _, loaded, _, _⟩ := StackFrame.current_privateSlot current slot
  have popPC : (afterInnerRet .gccSeparate initial).rip = resource.frame.call.code + 6 :=
    pc_afterInnerRet pre rfl
  have popStep := pop_step (profile := .gccSeparate) current pre.code rfl popPC slot loaded ((choices.drop 4) 0)
  have popCurrent := popStep.current current
  have incPC : (popped .gccSeparate (afterInnerRet .gccSeparate initial) value).rip =
      resource.frame.call.code + 7 := by
    simp [popped, CallReturn.popState, CallReturn.stackLength, popPC, BitVec.add_assoc]
  have incStep := increment_step (profile := .gccSeparate) popCurrent pre.code incPC (((choices.drop 4).drop 1) 0)
  have incCurrent := incStep.current popCurrent
  have rootPC : (increment (popped .gccSeparate (afterInnerRet .gccSeparate initial) value)).rip =
      resource.frame.call.code + 10 := by
    simp [increment, incPC, BitVec.add_assoc]
  have stackRoot : (increment (popped .gccSeparate (afterInnerRet .gccSeparate initial) value)).registers .rsp =
      resource.frame.top := by
    simp [increment, popped, popDestination, CallReturn.popState, State.writeRegister,
      stack_afterInnerRet pre, BitVec.sub_add_cancel]
  have rootStep := root_ret_step (profile := .gccSeparate) incCurrent pre.code rootPC stackRoot ((((choices.drop 4).drop 1).drop 1) 0)
  let final := finish (increment (popped .gccSeparate (afterInnerRet .gccSeparate initial) value))
    resource.frame.call.returnAddress
  have execution : StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved
      ⟨final, 7, [⟨.stack, resource.frame.top - 16, 8⟩,
        ⟨.stack, resource.frame.top - 8, 8⟩, ⟨.stack, resource.frame.top, 8⟩]⟩ := by
    simpa only [Sequential.Result.prepend, List.nil_append, List.append_nil,
      List.singleton_append, stack_afterInnerRet pre, stackRoot] using
      history.then_execution (.next popStep (.next incStep (.ret rootStep)))
  have memory := memory_frame pre.current (execution.current pre.current) execution.preserves
  have frame : RegisterFrame initial final := (frame_prefix .gccSeparate initial).trans
    ((frame_popped .gccSeparate _ value).trans ((frame_increment _).trans (frame_finish _ _)))
  refine ⟨evolved, _, execution, rfl, rfl, ?_⟩
  refine ⟨?_, memory.1, memory.2.1, memory.2.2, rfl, ?_, frame.preserved, frame.flags⟩
  · change (((initial.registers .rdi + 1) + 1)).toNat = resultNat resource.value
    rw [pre.argument]
    exact two_additions resource.value
  · simp [final, finish, stackRoot, pre.stack, State.writeRegister]

/-- Both Clang placements share the same stack and instruction order. Their
actual displacements, complete code windows and entry offsets remain distinct. -/
theorem clang_correct {profile : Profile} {resource : Resources} {initial : State}
    (clang : profile = .clangSame ∨ profile = .clangSeparate)
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved, ∃ result : CallReturn.Result,
      StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved result ∧
      result.instructions = 7 ∧
      result.reads = [⟨.stack, resource.frame.top - 16, 8⟩,
        ⟨.stack, resource.frame.top - 8, 8⟩, ⟨.stack, resource.frame.top, 8⟩] ∧
      Post (resourceInput resource) initial result.state := by
  have pad : padded profile = true := by rcases clang with rfl | rfl <;> rfl
  have continuationEq : continuation profile = .increment := by rcases clang with rfl | rfl <;> rfl
  obtain ⟨evolved, history, current⟩ := prefix_checked pre pad choices
  have incPC : (afterInnerRet profile initial).rip =
      resource.frame.call.code + BitVec.ofNat 64 (offset profile .increment) := by
    simpa only [continuationEq] using pc_afterInnerRet pre pad
  have incStep := increment_step current pre.code incPC ((choices.drop 4) 0)
  have incCurrent := incStep.current current
  have popPC : (increment (afterInnerRet profile initial)).rip =
      resource.frame.call.code + BitVec.ofNat 64 (offset profile .pop) := by
    rcases clang with rfl | rfl <;> simp [increment, incPC, offset, BitVec.add_assoc]
  have stackInc : (increment (afterInnerRet profile initial)).registers .rsp = resource.frame.top - 8 := by
    simp [increment, State.writeRegister, stack_afterInnerRet pre]
  have slot : StackFrame.Slot resource.frame ((increment (afterInnerRet profile initial)).registers .rsp) := by
    rw [stackInc]
    exact private_slot_at_depth incCurrent.contract (by decide : 8 ≤ 8) (Nat.le_trans (by decide : 8 ≤ 16) pre.capacity)
  obtain ⟨value, _, loaded, _, _⟩ := StackFrame.current_privateSlot incCurrent slot
  have present : active profile .pop = true := pad
  have popStep := pop_step incCurrent pre.code present popPC slot loaded (((choices.drop 4).drop 1) 0)
  have popCurrent := popStep.current incCurrent
  have rootPC : (popped profile (increment (afterInnerRet profile initial)) value).rip =
      resource.frame.call.code + BitVec.ofNat 64 (offset profile .ret) := by
    rcases clang with rfl | rfl <;>
      simp [popped, CallReturn.popState, CallReturn.stackLength, popPC, offset, BitVec.add_assoc]
  have stackRoot : (popped profile (increment (afterInnerRet profile initial)) value).registers .rsp =
      resource.frame.top := by
    rcases clang with rfl | rfl <;>
      simp [popped, popDestination, CallReturn.popState, State.writeRegister, stackInc, BitVec.sub_add_cancel]
  have rootStep := root_ret_step popCurrent pre.code rootPC stackRoot ((((choices.drop 4).drop 1).drop 1) 0)
  let final := finish (popped profile (increment (afterInnerRet profile initial)) value)
    resource.frame.call.returnAddress
  have execution : StackFrame.CPU.Execution resource.frame choices resource.shared initial evolved
      ⟨final, 7, [⟨.stack, resource.frame.top - 16, 8⟩,
        ⟨.stack, resource.frame.top - 8, 8⟩, ⟨.stack, resource.frame.top, 8⟩]⟩ := by
    simpa only [Sequential.Result.prepend, List.nil_append, List.append_nil,
      List.singleton_append, stackInc, stackRoot] using
      history.then_execution (.next incStep (.next popStep (.ret rootStep)))
  have memory := memory_frame pre.current (execution.current pre.current) execution.preserves
  have frame : RegisterFrame initial final := (frame_prefix profile initial).trans
    ((frame_increment _).trans ((frame_popped profile _ value).trans (frame_finish _ _)))
  refine ⟨evolved, _, execution, rfl, rfl, ?_⟩
  refine ⟨?_, memory.1, memory.2.1, memory.2.2, rfl, ?_, frame.preserved, frame.flags⟩
  · have different : popDestination profile ≠ .rax := by rcases clang with rfl | rfl <;> decide
    change (if Register.rax = popDestination profile then value else
      (initial.registers .rdi + 1) + 1).toNat = resultNat resource.value
    rw [ite_eq_right (Ne.symm different), pre.argument]
    exact two_additions resource.value
  · simp [final, finish, stackRoot, pre.stack, State.writeRegister]

end EDSL.CallStack.Compiler.Padded
