/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64.State

set_option warningAsError true

namespace EDSL.CallMemory64.Compiler
open X86 OS

def afterPush (initial : State) : State := pushed initial
def afterCall (initial : State) : State := called (afterPush initial)
def afterStore (initial : State) (world : Borrowing.State) : State := stored (afterCall initial) world
def afterLoad (initial : State) (world : Borrowing.State) (value : Word) : State :=
  loaded (afterStore initial world) value
def afterInnerRet (initial : State) (world : Borrowing.State) (value : Word) : State :=
  finish (afterLoad initial world value) (CallReturn.returnAddress (afterPush initial))

theorem stack_afterPush {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterPush initial).registers .rsp = resource.descriptor.frame.top - 8 := by
  simp [afterPush, pushed, CallStack.Compiler.pushed, CallReturn.pushState,
    CallReturn.stackDestination, State.writeRegister, pre.stack]

theorem stack_afterCall {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterCall initial).registers .rsp = resource.descriptor.frame.top - 16 := by
  simp [afterCall, called, CallReturn.callState, State.writeRegister,
    CallReturn.stackDestination, stack_afterPush pre, BitVec.sub_sub]

theorem stack_afterLoad {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (world : Borrowing.State) (value : Word) :
    (afterLoad initial world value).registers .rsp = resource.descriptor.frame.top - 16 := by
  simp [afterLoad, loaded, afterStore, stored, WordResources64.storeAfterLength,
    State.writeRegister, stack_afterCall pre]

theorem stack_afterInnerRet {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (world : Borrowing.State) (value : Word) :
    (afterInnerRet initial world value).registers .rsp = resource.descriptor.frame.top - 8 := by
  simp [afterInnerRet, finish, CallStack.Compiler.finish, State.writeRegister,
    stack_afterLoad pre, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem pc_afterPush {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterPush initial).rip = resource.descriptor.frame.call.code + 1 := by
  simp [afterPush, pushed, CallStack.Compiler.pushed, CallReturn.pushState,
    CallReturn.stackLength, program, pre.entry]

theorem pc_afterCall {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) :
    (afterCall initial).rip = resource.descriptor.frame.call.code + 11 :=
  call_target (pc_afterPush pre)

theorem pc_afterStore {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (world : Borrowing.State) :
    (afterStore initial world).rip = resource.descriptor.frame.call.code + 14 := by
  simp [afterStore, stored, WordResources64.storeAfterLength, pc_afterCall pre, BitVec.add_assoc]

theorem pc_afterLoad {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (world : Borrowing.State) (value : Word) :
    (afterLoad initial world value).rip = resource.descriptor.frame.call.code + 17 := by
  simp [afterLoad, loaded, pc_afterStore pre, BitVec.add_assoc]

theorem pc_afterInnerRet {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (world : Borrowing.State) (value : Word) :
    (afterInnerRet initial world value).rip = resource.descriptor.frame.call.code + 6 :=
  call_continuation (pc_afterPush pre)

theorem frame_prefix (initial : State) (world : Borrowing.State) (value : Word) :
    RegisterFrame initial (afterInnerRet initial world value) :=
  (CallStack.Compiler.frame_pushed initial).trans ((frame_called _).trans
    ((frame_stored _ _).trans ((frame_loaded _ _).trans (CallStack.Compiler.frame_finish _ _))))

/-- PUSH, CALL, DATA store, current DATA reload and internal RET use one actual
evolving OS world. The DATA store preserves the return word by allocation
separation; the reload observes that store's current owned value. -/
theorem prefix_covered {profile : Profile} {resource : Resources} {initial : State}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved,
      OS.CallMemory64.CoveredHistory resource.descriptor choices resource.shared initial evolved
        (afterInnerRet initial evolved resource.value) 5
        [⟨.data, resource.descriptor.target, 8⟩,
          ⟨.stack, resource.descriptor.frame.top - 16, 8⟩] ∧
      OS.CallMemory64.Current resource.descriptor evolved
        (afterInnerRet initial evolved resource.value) ∧
      readWord (afterInnerRet initial evolved resource.value).memory resource.descriptor.target =
        .ok resource.value := by
  have pushSlot : StackFrame.Slot resource.descriptor.frame (CallReturn.stackDestination initial) := by
    rw [CallReturn.stackDestination, pre.stack]
    exact CallStack.private_slot_at_depth pre.current.contract.stack (by decide : 8 ≤ 8)
      (Nat.le_trans (by decide : 8 ≤ 16) pre.capacity)
  have pushPC : initial.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .push) :=
    pre.entry
  obtain ⟨pushedWorld, pushStep, pushCurrent⟩ :=
    push_enabled pre.current pre.code pushPC pushSlot (choices 0)
  have callSlot : StackFrame.Slot resource.descriptor.frame
      (CallReturn.stackDestination (afterPush initial)) := by
    rw [CallReturn.stackDestination, stack_afterPush pre, BitVec.sub_sub]
    exact CallStack.private_slot_at_depth pushCurrent.contract.stack (by decide : 8 ≤ 16) pre.capacity
  obtain ⟨calledWorld, callStep, callCurrent, callReadback⟩ :=
    call_enabled pushCurrent pre.code (pc_afterPush pre) callSlot ((choices.drop 1) 0)
  have pointer : (afterCall initial).registers .rdi = resource.descriptor.target := by
    simpa [afterCall, called, afterPush, pushed, CallStack.Compiler.pushed,
      CallReturn.callState, CallReturn.pushState, State.writeRegister] using pre.pointer
  have argument : (afterCall initial).registers .rsi = resource.value := by
    simpa [afterCall, called, afterPush, pushed, CallStack.Compiler.pushed,
      CallReturn.callState, CallReturn.pushState, State.writeRegister] using pre.argument
  obtain ⟨dataWorld, storeStep, storeCurrent, storeEffect, ownedReadback⟩ :=
    store_enabled callCurrent pre.code (pc_afterCall pre) pointer argument
      (((choices.drop 1).drop 1) 0)
  have loadPointer : (afterStore initial dataWorld).registers .rdi = resource.descriptor.target := pointer
  have loadStep := load_step storeCurrent pre.code (pc_afterStore pre dataWorld) loadPointer
    ownedReadback ((((choices.drop 1).drop 1).drop 1) 0)
  have loadCurrent := loadStep.current storeCurrent
  have innerSlot : StackFrame.Slot resource.descriptor.frame
      ((afterLoad initial dataWorld resource.value).registers .rsp) := by
    rw [stack_afterLoad pre]
    exact CallStack.private_slot_at_depth loadCurrent.contract.stack (by decide : 8 ≤ 16) pre.capacity
  have returnReadback : readWord (afterLoad initial dataWorld resource.value).memory
      ((afterLoad initial dataWorld resource.value).registers .rsp) =
        .ok (CallReturn.returnAddress (afterPush initial)) := by
    have retained := (data_preserves_private callCurrent storeCurrent storeEffect callSlot).trans callReadback
    exact retained
  have innerStep := inner_ret_step loadCurrent pre.code (pc_afterLoad pre dataWorld resource.value)
    innerSlot returnReadback (call_addresses (current_code pushCurrent pre.code) (pc_afterPush pre)).2
    (((((choices.drop 1).drop 1).drop 1).drop 1) 0)
  have pushFetch := node_fetchWithin (current_code pre.current pre.code) pre.code .push pushPC
  have callFetch := node_fetchWithin (current_code pushCurrent pre.code) pre.code .call (pc_afterPush pre)
  have storeFetch := node_fetchWithin (current_code callCurrent pre.code) pre.code .store (pc_afterCall pre)
  have loadFetch := node_fetchWithin (current_code storeCurrent pre.code) pre.code .load (pc_afterStore pre dataWorld)
  have innerFetch := node_fetchWithin (current_code loadCurrent pre.code) pre.code .innerRet
    (pc_afterLoad pre dataWorld resource.value)
  have history : OS.CallMemory64.CoveredHistory resource.descriptor choices resource.shared initial dataWorld
      (afterInnerRet initial dataWorld resource.value) 5
      [⟨.data, resource.descriptor.target, 8⟩,
        ⟨.stack, (afterLoad initial dataWorld resource.value).registers .rsp, 8⟩] :=
    .next pushStep pushFetch (.next callStep callFetch (.next storeStep storeFetch
      (.next loadStep loadFetch (.next innerStep innerFetch .nil))))
  refine ⟨dataWorld, ?_, innerStep.current loadCurrent, ?_⟩
  · simpa only [stack_afterLoad pre] using history
  · change readWord (afterLoad initial dataWorld resource.value).memory resource.descriptor.target = _
    exact Borrowing.loadOwnedWord64_readWord _ _ _ _ _ ownedReadback

end EDSL.CallMemory64.Compiler
