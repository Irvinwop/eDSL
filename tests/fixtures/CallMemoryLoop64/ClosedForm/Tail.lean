/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.ClosedForm.Front

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.ClosedForm
open X86 OS

structure Output (resource : Resources) (initial final : State) : Prop where
  value : final.registers .rax = resource.value + resource.count
  stored : readWord final.memory resource.descriptor.target =
    if resource.count = 0 then readWord initial.memory resource.descriptor.target
    else .ok (targetWord resource.value resource.count)
  returned : final.rip = resource.descriptor.frame.call.returnAddress
  stack : final.registers .rsp = resource.descriptor.frame.top + 8
  frame : Frame initial final

/-- Branch on the actual TEST flags. A zero count performs no mutation;
a nonzero count uses the current DATA owner for one actual store. Both paths
read the original caller word for RET in their current coupled OS world. -/
theorem tail {profile resource initial middle}
    (same : resource.descriptor.frame.call.bytes = bytes profile)
    (current : Current resource.descriptor resource.shared middle)
    (inv : Front profile resource initial middle) (choices : CallReturn.Choices) :
    ∃ evolved result, CoveredExecution resource.descriptor choices resource.shared middle evolved result ∧
      Output resource initial result.state ∧
      result.instructions = if resource.count = 0 then 2 else 4 := by
  by_cases empty : resource.count = 0
  · have flag : middle.flags.getLsbD 6 = true := by rw [inv.zero, empty]; rfl
    let s1 := jumped middle (resource.descriptor.frame.call.code + BitVec.ofNat 64 (retOffset profile))
    have one0 := guard_next current same inv.pc flag (choices 0)
    have current1 : Current resource.descriptor resource.shared s1 := one0.current current
    have stack1 : s1.registers .rsp = resource.descriptor.frame.top := inv.stack
    have returning := root_ret current1 same rfl stack1 (choices.drop 1)
    have execution := OS.CallMemory64.CoveredExecution.next one0.step one0.fetch returning
    refine ⟨resource.shared, _, execution, ?_, ?_⟩
    · refine ⟨?_, ?_, rfl, ?_, inv.frame.trans
        ((frame_jumped middle _).trans (frame_finished s1 _))⟩
      · change middle.registers .rax = resource.value + resource.count
        exact inv.value
      · change readWord middle.memory resource.descriptor.target =
          if resource.count = 0 then readWord initial.memory resource.descriptor.target else _
        rw [ite_eq_left empty, inv.memory]
      · change middle.registers .rsp + 8 = resource.descriptor.frame.top + 8
        rw [inv.stack]
    · simp only [Sequential.Result.prepend, empty, ↓reduceIte]
  · have flag : middle.flags.getLsbD 6 = false := by
      rw [inv.zero]
      exact beq_eq_false_iff_ne.mpr empty
    let s1 := jumped middle (resource.descriptor.frame.call.code + BitVec.ofNat 64 (predOffset profile))
    have one0 := guard_next current same inv.pc flag (choices 0)
    have current1 : Current resource.descriptor resource.shared s1 := one0.current current
    let s2 := predecessor profile s1
    have one1 := predecessor_next current1 same rfl ((choices.drop 1) 0)
    have current2 : Current resource.descriptor resource.shared s2 := one1.current current1
    have pc2 : s2.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 (storeOffset profile) := by
      change (resource.descriptor.frame.call.code + BitVec.ofNat 64 (predOffset profile)) + 4 = _
      rw [BitVec.add_assoc]
      congr 1
      cases profile <;> decide
    have pointer2 : s2.registers .rdi = resource.descriptor.target := by
      cases profile <;>
        simpa [s2, predecessor, CallReturn.leaState, scratch, State.writeRegister, s1, jumped] using inv.pointer
    have stack2 : s2.registers .rsp = resource.descriptor.frame.top := by
      cases profile <;>
        simpa [s2, predecessor, CallReturn.leaState, scratch, State.writeRegister, s1, jumped] using inv.stack
    have value2 : s2.registers (scratch profile) = targetWord resource.value resource.count := by
      simp [s2, predecessor, CallReturn.leaState, State.writeRegister, CallReturn.Address.eval,
        s1, jumped, inv.value]
      exact target_predecessor _ _ empty
    have return2 : s2.registers .rax = resource.value + resource.count := by
      cases profile <;>
        simpa [s2, predecessor, CallReturn.leaState, scratch, State.writeRegister, s1, jumped] using inv.value
    obtain ⟨evolved, one2, _, owned⟩ := store_next current2 same pc2 pointer2 (((choices.drop 1).drop 1) 0)
    let s3 := stored s2 evolved
    have current3 : Current resource.descriptor evolved s3 := one2.current current2
    have pc3 : s3.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 (retOffset profile) := by
      change s2.rip + 3 = _
      rw [pc2, BitVec.add_assoc]
      congr 1
      cases profile <;> decide
    have stack3 : s3.registers .rsp = resource.descriptor.frame.top := stack2
    have observed : readWord s3.memory resource.descriptor.target =
        .ok (targetWord resource.value resource.count) := by
      rw [current3.coupled]
      exact (Borrowing.loadOwnedWord64_readWord _ _ _ _ _ owned).trans (congrArg Except.ok value2)
    have returning := root_ret current3 same pc3 stack3 (((choices.drop 1).drop 1).drop 1)
    have execution := OS.CallMemory64.CoveredExecution.next one0.step one0.fetch
      (.next one1.step one1.fetch (.next one2.step one2.fetch returning))
    refine ⟨evolved, _, execution, ?_, ?_⟩
    · refine ⟨?_, ?_, rfl, ?_, inv.frame.trans ((frame_jumped middle _).trans
        ((frame_predecessor profile s1).trans ((frame_stored s2 evolved).trans (frame_finished s3 _))))⟩
      · change s2.registers .rax = resource.value + resource.count
        exact return2
      · change readWord s3.memory resource.descriptor.target =
          if resource.count = 0 then _ else .ok (targetWord resource.value resource.count)
        rw [ite_eq_right empty]
        exact observed
      · change s2.registers .rsp + 8 = resource.descriptor.frame.top + 8
        rw [stack2]
    · simp only [Sequential.Result.prepend, ite_eq_right empty]

end EDSL.CallMemoryLoop64.ClosedForm
