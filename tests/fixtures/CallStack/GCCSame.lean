/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.State
import EDSL.CallStack.Frame

set_option warningAsError true

namespace EDSL.CallStack.Compiler.GCCSame
open X86 OS

def afterCall (initial : State) : State := called .gccSame initial
def afterHelper (initial : State) : State := helper (afterCall initial)
def afterInnerRet (initial : State) : State := finish (afterHelper initial) (CallReturn.returnAddress initial)
def afterIncrement (initial : State) : State := increment (afterInnerRet initial)
def final (initial : State) (target : Word) : State := finish (afterIncrement initial) target

theorem covered_correct {resource : Resources} {initial : State}
    (pre : ResourcePre (program .gccSame) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved,
      CoveredHistory resource.frame choices resource.shared initial evolved
        (afterIncrement initial) 4 [⟨.stack, resource.frame.top - 8, 8⟩] ∧
      StackFrame.CPU.Step resource.frame evolved evolved (afterIncrement initial)
        (final initial resource.frame.call.returnAddress) ((choices.drop 4) 0)
        ⟨.returned (final initial resource.frame.call.returnAddress), [⟨.stack, resource.frame.top, 8⟩]⟩ ∧
      FetchWithin resource.frame (afterIncrement initial) ∧
      Post (resourceInput resource) initial (final initial resource.frame.call.returnAddress) := by
  have current := pre.current
  have capacity := pre.capacity
  have same : resource.frame.call.bytes = bytes .gccSame := pre.code
  have pc : initial.rip = resource.frame.call.code + 5 := pre.entry
  have slot : StackFrame.Slot resource.frame (CallReturn.stackDestination initial) := by
    rw [CallReturn.stackDestination, pre.stack]
    exact private_slot_at_depth (depth := 8) current.contract (by decide) (by omega)
  obtain ⟨evolved, callStep, currentCall, readback⟩ := call_enabled (profile := .gccSame) current same pc slot (choices 0)
  have helperPC : (afterCall initial).rip = resource.frame.call.code := by
    change CallReturn.callTarget initial (displacement .gccSame) = _
    simpa [offset] using call_target (profile := .gccSame) pc
  have helperStep := helper_step (profile := .gccSame) currentCall same (by
    change (afterCall initial).rip = resource.frame.call.code + 0
    exact helperPC.trans (BitVec.add_zero _).symm) ((choices.drop 1) 0)
  have currentHelper := helperStep.current currentCall
  have innerPC : (afterHelper initial).rip = resource.frame.call.code + 4 := by
    change (afterCall initial).rip + 4 = _
    rw [helperPC]
  have stackHelper : (afterHelper initial).registers .rsp = resource.frame.top - 8 := by
    simp [afterHelper, helper, afterCall, called, CallReturn.callState, CallReturn.leaState,
      State.writeRegister, CallReturn.stackDestination, pre.stack]
  have innerSlot : StackFrame.Slot resource.frame ((afterHelper initial).registers .rsp) := by
    rw [stackHelper]
    exact private_slot_at_depth (depth := 8) currentHelper.contract (by decide) (by omega)
  have innerRead : readWord (afterHelper initial).memory ((afterHelper initial).registers .rsp) =
      .ok (CallReturn.returnAddress initial) := by
    exact readback
  have innerStep := inner_ret_step (profile := .gccSame) currentHelper same innerPC innerSlot innerRead
    (call_addresses (profile := .gccSame) (current_code current same) pc).2 (((choices.drop 1).drop 1) 0)
  have currentInner := innerStep.current currentHelper
  have incrementPC : (afterInnerRet initial).rip = resource.frame.call.code + 10 := by
    change CallReturn.returnAddress initial = _
    simpa [continuation, offset] using call_continuation (profile := .gccSame) pc
  have incStep := increment_step (profile := .gccSame) currentInner same incrementPC ((((choices.drop 1).drop 1).drop 1) 0)
  have currentIncrement := incStep.current currentInner
  have rootPC : (afterIncrement initial).rip = resource.frame.call.code + 13 := by
    simp [afterIncrement, increment, incrementPC, BitVec.add_assoc]
  have stackRoot : (afterIncrement initial).registers .rsp = resource.frame.top := by
    change (afterHelper initial).registers .rsp + 8 = resource.frame.top
    rw [stackHelper, BitVec.sub_add_cancel]
  have rootStep := root_ret_step (profile := .gccSame) currentIncrement same rootPC stackRoot ((choices.drop 4) 0)
  have callFetch := node_fetchWithin (current_code current same) same .call rfl pc
  have helperFetch := node_fetchWithin (current_code currentCall same) same .helper rfl (by
    change (afterCall initial).rip = resource.frame.call.code + 0
    exact helperPC.trans (BitVec.add_zero _).symm)
  have innerFetch := node_fetchWithin (current_code currentHelper same) same .innerRet rfl innerPC
  have incFetch := node_fetchWithin (current_code currentInner same) same .increment rfl incrementPC
  have rootFetch := node_fetchWithin (current_code currentIncrement same) same .ret rfl rootPC
  have history : CoveredHistory resource.frame choices resource.shared initial evolved
      (afterIncrement initial) 4 [⟨.stack, resource.frame.top - 8, 8⟩] := by
    have trace : CoveredHistory resource.frame choices resource.shared initial evolved
        (afterIncrement initial) 4 [⟨.stack, (afterHelper initial).registers .rsp, 8⟩] :=
      .next callStep callFetch (.next helperStep helperFetch
        (.next innerStep innerFetch (.next incStep incFetch .nil)))
    simpa only [stackHelper] using trace
  have endpoint := rootStep.current currentIncrement
  have memory := memory_frame current endpoint history.preserves
  have frame : RegisterFrame initial (final initial resource.frame.call.returnAddress) :=
    (frame_called .gccSame initial).trans ((frame_helper _).trans
      ((frame_finish _ _).trans ((frame_increment _).trans (frame_finish _ _))))
  refine ⟨evolved, history, ?_, rootFetch, ?_⟩
  · have last : StackFrame.CPU.Step resource.frame evolved evolved (afterIncrement initial)
        (final initial resource.frame.call.returnAddress) ((choices.drop 4) 0)
        ⟨.returned (final initial resource.frame.call.returnAddress),
          [⟨.stack, (afterIncrement initial).registers .rsp, 8⟩]⟩ := rootStep
    simpa only [stackRoot] using last
  · refine ⟨?_, memory.1, memory.2.1, memory.2.2, rfl, ?_, frame.preserved, frame.flags⟩
    · change (((initial.registers .rdi + 1) + 1)).toNat = resultNat resource.value
      rw [pre.argument]
      exact two_additions resource.value
    · simp [final, finish, stackRoot, pre.stack, State.writeRegister]

theorem correct {resource : Resources} {initial : State}
    (pre : ResourcePre (program .gccSame) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved,
      StackFrame.CPU.History resource.frame choices resource.shared initial evolved
        (afterIncrement initial) 4 [⟨.stack, resource.frame.top - 8, 8⟩] ∧
      StackFrame.CPU.Step resource.frame evolved evolved (afterIncrement initial)
        (final initial resource.frame.call.returnAddress) ((choices.drop 4) 0)
        ⟨.returned (final initial resource.frame.call.returnAddress), [⟨.stack, resource.frame.top, 8⟩]⟩ ∧
      Post (resourceInput resource) initial (final initial resource.frame.call.returnAddress) := by
  obtain ⟨evolved, history, last, _, post⟩ := covered_correct pre choices
  exact ⟨evolved, history.history, last, post⟩

end EDSL.CallStack.Compiler.GCCSame
