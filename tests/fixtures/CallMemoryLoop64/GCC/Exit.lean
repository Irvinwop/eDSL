/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC.Facts

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

/-- The independent natural predecessor formula agrees with word subtraction
for every nonzero full64 count, including a wrapped returned sum. -/
theorem target_predecessor (value count : Word) (nonzero : count ≠ 0) :
    value + count - 1 = targetWord value count := by
  have positive : 0 < count.toNat := by
    have different : count.toNat ≠ 0 := fun equal => nonzero (BitVec.eq_of_toNat_eq equal)
    omega
  change BitVec.ofNat 64 (value.toNat + count.toNat) - BitVec.ofNat 64 1 =
    BitVec.ofNat 64 (value.toNat + count.toNat - 1)
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)

/-- Arithmetic and ABI endpoint facts. The global union memory frame is
obtained from the same complete covered execution at the public theorem. -/
structure Output (resource : Resources) (initial final : State) : Prop where
  value : final.registers .rax = resource.value + resource.count
  stored : readWord final.memory resource.descriptor.target =
    if resource.count = 0 then readWord initial.memory resource.descriptor.target
    else .ok (targetWord resource.value resource.count)
  returned : final.rip = resource.descriptor.frame.call.returnAddress
  stack : final.registers .rsp = resource.descriptor.frame.top + 8
  preserved : ∀ register, register ∉ CallStack.clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- TEST/JE plus the five-instruction epilogue. The pad POP observes its
current arbitrary word; RBX and RBP are restored from the saved actual words. -/
theorem exit {resource : Resources} {initial state : State} {shared : Shared}
    (same : resource.descriptor.frame.call.bytes = text)
    (capacity : 32 ≤ resource.descriptor.frame.capacity)
    (current : Current resource.descriptor shared state)
    (inv : Invariant resource initial state 0) (choices : CallReturn.Choices) :
    ∃ result, CoveredExecution resource.descriptor choices shared state shared result ∧
      result.instructions = 7 ∧ Output resource initial result.state := by
  have zeroCounter : state.registers .rbx = 0 := BitVec.eq_of_toNat_eq inv.counter
  let s1 := tested state (choices 0)
  have step0 := test_next current same inv.pc (choices 0)
  have c1 : Current resource.descriptor shared s1 := step0.current current
  have pc1 : s1.rip = resource.descriptor.frame.call.code + 12 := by
    simp [s1, tested, inv.pc, BitVec.add_assoc]
  have flag : s1.flags.getLsbD 6 = true := by
    change (Sequential.logicalFlags64 state.flags (state.registers .rbx) (choices 0)).getLsbD 6 = true
    rw [Sequential.logicalFlags64_zero]
    simp [zeroCounter]
  let s2 := atPC s1 (resource.descriptor.frame.call.code + 31)
  have step1 : Next resource.descriptor shared shared s1 s2 ((choices.drop 1) 0) :=
    guard_next c1 same pc1 flag ((choices.drop 1) 0)
  have c2 := step1.current c1
  have sp2 : s2.registers .rsp = resource.descriptor.frame.top - 24 := inv.stack
  have slot2 : StackFrame.Slot resource.descriptor.frame (s2.registers .rsp) := by
    rw [sp2]
    exact depth_slot c2 capacity (by decide : 8 ≤ 24) (by decide)
  obtain ⟨pad, _, observed, _, _⟩ := StackFrame.current_privateSlot c2.stack slot2
  let s3 := popped s2 .rdx pad
  have step2 := pop_next c2 same
    (by decide : (31, .pop64 .rdx false) ∈ Compiler.sites .gccSeparate) rfl slot2 observed
    (((choices.drop 1).drop 1) 0)
  have c3 : Current resource.descriptor shared s3 := step2.current c2
  have pc3 : s3.rip = resource.descriptor.frame.call.code + 32 := by
    simp [s3, popped, CallReturn.popState, CallReturn.stackLength, s2, atPC, BitVec.add_assoc]
  let s4 := moved s3 .rax .rsi
  have step3 := move_next c3 same
    (by decide : (32, .sequential (.movReg64 .rax .rsi)) ∈ Compiler.sites .gccSeparate) pc3
    ((((choices.drop 1).drop 1).drop 1) 0)
  have c4 : Current resource.descriptor shared s4 := step3.current c3
  have pc4 : s4.rip = resource.descriptor.frame.call.code + 35 := by
    simp [s4, moved, pc3, BitVec.add_assoc]
  have sp4 : s4.registers .rsp = resource.descriptor.frame.top - 16 := by
    change state.registers .rsp + 8 = _
    rw [inv.stack]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have slot4 : StackFrame.Slot resource.descriptor.frame (s4.registers .rsp) := by
    rw [sp4]
    exact depth_slot c4 capacity (by decide : 8 ≤ 16) (by decide)
  have read4 : readWord s4.memory (s4.registers .rsp) = .ok (initial.registers .rbx) := by
    rw [sp4]
    exact inv.saved.rbx
  let s5 := popped s4 .rbx (initial.registers .rbx)
  have step4 := pop_next c4 same
    (by decide : (35, .pop64 .rbx false) ∈ Compiler.sites .gccSeparate) pc4 slot4 read4
    (((((choices.drop 1).drop 1).drop 1).drop 1) 0)
  have c5 : Current resource.descriptor shared s5 := step4.current c4
  have pc5 : s5.rip = resource.descriptor.frame.call.code + 36 := by
    simp [s5, popped, CallReturn.popState, CallReturn.stackLength, pc4, BitVec.add_assoc]
  have sp5 : s5.registers .rsp = resource.descriptor.frame.top - 8 := by
    change s4.registers .rsp + 8 = _
    rw [sp4]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have slot5 : StackFrame.Slot resource.descriptor.frame (s5.registers .rsp) := by
    rw [sp5]
    exact depth_slot c5 capacity (by decide : 8 ≤ 8) (by decide)
  have read5 : readWord s5.memory (s5.registers .rsp) = .ok (initial.registers .rbp) := by
    rw [sp5]
    exact inv.saved.rbp
  let s6 := popped s5 .rbp (initial.registers .rbp)
  have step5 := pop_next c5 same
    (by decide : (36, .pop64 .rbp false) ∈ Compiler.sites .gccSeparate) pc5 slot5 read5
    ((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1) 0)
  have c6 : Current resource.descriptor shared s6 := step5.current c5
  have pc6 : s6.rip = resource.descriptor.frame.call.code + 37 := by
    simp [s6, popped, CallReturn.popState, CallReturn.stackLength, pc5, BitVec.add_assoc]
  have sp6 : s6.registers .rsp = resource.descriptor.frame.top := by
    change s5.registers .rsp + 8 = _
    rw [sp5, BitVec.sub_add_cancel]
  let final := finished s6 resource.descriptor.frame.call.returnAddress
  let result : CallReturn.Result := ⟨final, 7,
    [⟨.stack, s2.registers .rsp, 8⟩, ⟨.stack, s4.registers .rsp, 8⟩,
      ⟨.stack, s5.registers .rsp, 8⟩, ⟨.stack, s6.registers .rsp, 8⟩]⟩
  have execution : CoveredExecution resource.descriptor choices shared state shared result :=
    .next step0.step step0.fetch (.next step1.step step1.fetch (.next step2.step step2.fetch
      (.next step3.step step3.fetch (.next step4.step step4.fetch (.next step5.step step5.fetch
        (root_ret c6 same pc6 sp6 ((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1)))))))
  have frame : Frame initial final := inv.frame.trans ((frame_test state (choices 0)).trans
    ((frame_pc s1 _).trans ((frame_pop s2 .rdx pad (by decide)).trans
      ((frame_move s3 .rax .rsi (by decide)).trans ((frame_pop s4 .rbx _ (by decide)).trans
        ((frame_pop s5 .rbp _ (by decide)).trans (frame_finish s6 _)))))))
  have value : state.registers .rsi = resource.value + resource.count := by simpa using inv.total
  refine ⟨result, execution, rfl, ?_⟩
  refine ⟨value, ?_, rfl, ?_, frame.full rfl rfl, frame.flags⟩
  · change readWord state.memory resource.descriptor.target = _
    by_cases zero : resource.count = 0
    · simpa [zero] using inv.stored
    · have different : (0 : Nat) ≠ resource.count.toNat := by
        intro equal
        apply zero
        exact BitVec.eq_of_toNat_eq equal.symm
      simpa only [ite_eq_right zero, ite_eq_right different, value,
        target_predecessor _ _ zero] using inv.stored
  · change s6.registers .rsp + 8 = resource.descriptor.frame.top + 8
    rw [sp6]

end EDSL.CallMemoryLoop64.GCC
