/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.Clang.Loop

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Clang
open X86 OS

def front (s : State) (af : Bool) : State := test (mov s .rax .rsi) af

theorem front_pc {resource initial} (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (af : Bool) : (front initial af).rip = resource.descriptor.frame.call.code + 6 := by
  simp [front, test, mov, pre.entry, Compiler.program, BitVec.add_assoc]

theorem front_frame (s : State) (af : Bool) : Frame s (front s af) :=
  (frame_mov s .rax .rsi (by decide)).trans (frame_test _ af)

theorem front_block {resource initial} (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (choices : CallReturn.Choices) :
    Block resource.descriptor choices resource.shared initial resource.shared (front initial (choices 1)) 2 := by
  have pc0 : initial.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 0 := pre.entry
  have one1 := mov_one pre.current pre.code
    (by decide : (0, .sequential (.movReg64 .rax .rsi)) ∈ Compiler.sites .clangSeparate) pc0 (choices 0)
  have current := one1.current pre.current
  have pc1 : (mov initial .rax .rsi).rip = resource.descriptor.frame.call.code + 3 := by
    simp [mov, pre.entry, Compiler.program]
  have one2 : One resource.descriptor (choices 1) resource.shared resource.shared
      (mov initial .rax .rsi) (front initial (choices 1)) :=
    plain_one current pre.code
      (by decide : (3, .sequential (.test64 .rdx .rdx)) ∈ Compiler.sites .clangSeparate) pc1 rfl rfl rfl
  exact Block.cons one1 one2.block

theorem front_zero {resource initial} (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (af : Bool) : (front initial af).flags.getLsbD 6 = (resource.count == 0) := by
  change (Sequential.logicalFlags64 initial.flags
    ((mov initial .rax .rsi).registers .rdx &&& (mov initial .rax .rsi).registers .rdx) af).getLsbD 6 = _
  rw [Sequential.logicalFlags64_zero]
  simp [mov, State.writeRegister, pre.counter]

/-- Eight actual prologue instructions save arbitrary incoming R14/RBX and
establish the loop invariant without changing DATA. -/
theorem prologue {resource initial} (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (nonzero : resource.count ≠ 0) (choices : CallReturn.Choices) :
    ∃ evolved after, Block resource.descriptor choices resource.shared initial evolved after 8 ∧
      Loop resource.descriptor (initial.registers .r14) (initial.registers .rbx)
        resource.value resource.count.toNat after ∧ Frame initial after := by
  let d := resource.descriptor
  let s2 := front initial (choices 1)
  have block2 := front_block pre choices
  have c2 := block2.current pre.current
  have zero2 : s2.flags.getLsbD 6 = false := by
    rw [front_zero pre]
    exact beq_eq_false_iff_ne.mpr nonzero
  have one3 := jne_fallthrough c2 pre.code (front_pc pre _) zero2 (choices 2)
  let s3 := jump s2 (d.frame.call.code + 8)
  have c3 := one3.current c2
  have pc3 : s3.rip = d.frame.call.code + 8 := rfl
  have dest3 : CallReturn.stackDestination s3 = d.frame.top - 8 := by
    simp [s3, jump, s2, front, test, mov, CallReturn.stackDestination, State.writeRegister, pre.stack, d]
  have slot3 : StackFrame.Slot d.frame (CallReturn.stackDestination s3) := by
    rw [dest3]
    exact slot c3 pre.stackCapacity (by decide : 8 ≤ 8) (by decide)
  obtain ⟨w4, step4, effect4, read4⟩ := push_step c3 pre.code
    (by decide : (8, .push64 .r14 true) ∈ Compiler.sites .clangSeparate) pc3 slot3 (choices 3)
  let s4 := push s3 .r14 true
  have c4 := step4.current c3
  have one4 : One d (choices 3) resource.shared w4 s3 s4 :=
    ⟨[], step4, fetch c3 pre.code (by decide : (8, .push64 .r14 true) ∈ Compiler.sites .clangSeparate) pc3⟩
  have pc4 : s4.rip = d.frame.call.code + 10 := by
    simp [s4, push, CallReturn.pushState, CallReturn.stackLength, pc3, BitVec.add_assoc]
  have stack4 : s4.registers .rsp = d.frame.top - 8 := by
    simp [s4, push, CallReturn.pushState, State.writeRegister, dest3]
  have dest4 : CallReturn.stackDestination s4 = d.frame.top - 16 := by
    simp [CallReturn.stackDestination, stack4, BitVec.sub_sub]
  have slot4 : StackFrame.Slot d.frame (CallReturn.stackDestination s4) := by
    rw [dest4]
    exact slot c4 pre.stackCapacity (by decide : 8 ≤ 16) (by decide)
  obtain ⟨w5, step5, effect5, read5⟩ := push_step c4 pre.code
    (by decide : (10, .push64 .rbx false) ∈ Compiler.sites .clangSeparate) pc4 slot4 (choices 4)
  let s5 := push s4 .rbx false
  have c5 := step5.current c4
  have one5 : One d (choices 4) w4 w5 s4 s5 :=
    ⟨[], step5, fetch c4 pre.code (by decide : (10, .push64 .rbx false) ∈ Compiler.sites .clangSeparate) pc4⟩
  have pc5 : s5.rip = d.frame.call.code + 11 := by
    simp [s5, push, CallReturn.pushState, CallReturn.stackLength, pc4, BitVec.add_assoc]
  have stack5 : s5.registers .rsp = d.frame.top - 16 := by
    simp [s5, push, CallReturn.pushState, State.writeRegister, dest4]
  have dest5 : CallReturn.stackDestination s5 = d.frame.top - 24 := by
    simp [CallReturn.stackDestination, stack5, BitVec.sub_sub]
  have slot5 : StackFrame.Slot d.frame (CallReturn.stackDestination s5) := by
    rw [dest5]
    exact slot c5 pre.stackCapacity (by decide : 8 ≤ 24) (by decide)
  obtain ⟨w6, step6, effect6, _⟩ := push_step c5 pre.code
    (by decide : (11, .push64 .rax false) ∈ Compiler.sites .clangSeparate) pc5 slot5 (choices 5)
  let s6 := push s5 .rax false
  have c6 := step6.current c5
  have one6 : One d (choices 5) w5 w6 s5 s6 :=
    ⟨[], step6, fetch c5 pre.code (by decide : (11, .push64 .rax false) ∈ Compiler.sites .clangSeparate) pc5⟩
  have pc6 : s6.rip = d.frame.call.code + 12 := by
    simp [s6, push, CallReturn.pushState, CallReturn.stackLength, pc5, BitVec.add_assoc]
  let s7 := mov s6 .rbx .rdx
  have one7 := mov_one c6 pre.code
    (by decide : (12, .sequential (.movReg64 .rbx .rdx)) ∈ Compiler.sites .clangSeparate) pc6 (choices 6)
  have c7 := one7.current c6
  have pc7 : s7.rip = d.frame.call.code + 15 := by simp [s7, mov, pc6, BitVec.add_assoc]
  let s8 := mov s7 .r14 .rdi
  have one8 := mov_one c7 pre.code
    (by decide : (15, .sequential (.movReg64 .r14 .rdi)) ∈ Compiler.sites .clangSeparate) pc7 (choices 7)
  have high4 : readWord s4.memory (d.frame.top - 8) = .ok (initial.registers .r14) := by
    change readWord s4.memory (CallReturn.stackDestination s3) = .ok (s3.registers .r14) at read4
    rw [dest3] at read4
    exact read4
  have low5 : readWord s5.memory (d.frame.top - 16) = .ok (initial.registers .rbx) := by
    change readWord s5.memory (CallReturn.stackDestination s4) = .ok (s4.registers .rbx) at read5
    rw [dest4] at read5
    exact read5
  have write5 : Borrowing.StoreEffect64 w4 w5 (d.frame.top - 16) (s4.registers .rbx) := by
    change Borrowing.StoreEffect64 w4 w5 (CallReturn.stackDestination s4) (s4.registers .rbx) at effect5
    rwa [dest4] at effect5
  have high5 : readWord s5.memory (d.frame.top - 8) = .ok (initial.registers .r14) :=
    (OS.CallMemory64.store64_preserves_private c4 c5 write5
      (slot c4 pre.stackCapacity (by decide : 8 ≤ 8) (by decide))
      (slots_disjoint c4 pre.stackCapacity (by decide : 16 ≤ 32) (by decide : 8 ≤ 32)
        (by decide))).trans high4
  have saved5 : Saved d (initial.registers .r14) (initial.registers .rbx) s5 := ⟨high5, low5⟩
  have write6 : Borrowing.StoreEffect64 w5 w6 (d.frame.top - 24) (s5.registers .rax) := by
    change Borrowing.StoreEffect64 w5 w6 (CallReturn.stackDestination s5) (s5.registers .rax) at effect6
    rwa [dest5] at effect6
  have saved6 := saved5.private c5 c6 pre.stackCapacity (by decide : 24 ≤ 24) (by decide) write6
  refine ⟨w6, s8, ?_, ?_, ?_⟩
  · exact block2.trans (Block.cons one3 (Block.cons one4
      (Block.cons one5 (Block.cons one6 (Block.cons one7 one8.block)))))
  · have positive : resource.count.toNat ≠ 0 := by
      intro zero
      apply nonzero
      exact BitVec.eq_of_toNat_eq zero
    refine ⟨?_, ?_, ?_, ?_, ?_, saved6.sameMemory rfl⟩
    · simp [s8, mov, pc7, positive, BitVec.add_assoc]
      rfl
    · simp [s8, s7, mov, s6, push, CallReturn.pushState, State.writeRegister, dest5]
      rfl
    · simp [s8, mov, s7, s6, s5, s4, push, CallReturn.pushState, s3, jump, s2,
        front, test, State.writeRegister, pre.pointer]
    · simp [s8, s7, mov, s6, s5, s4, push, CallReturn.pushState, s3, jump, s2,
        front, test, State.writeRegister, pre.argument]
    · simp [s8, s7, mov, s6, s5, s4, push, CallReturn.pushState, s3, jump, s2,
        front, test, State.writeRegister, pre.counter]
  · exact (front_frame initial _).trans ((frame_jump s2 _).trans
      ((frame_push s3 .r14 true).trans ((frame_push s4 .rbx false).trans
        ((frame_push s5 .rax false).trans ((frame_mov s6 .rbx .rdx (by decide)).trans
          (frame_mov s7 .r14 .rdi (by decide)))))))

end EDSL.CallMemoryLoop64.Clang
