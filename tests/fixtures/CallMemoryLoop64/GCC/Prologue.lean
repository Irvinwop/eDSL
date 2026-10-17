/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC.Facts

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

/-- All three incoming words are pushed by actual checked mutations. The two
callee-save words survive later pushes at disjoint whole-qword depths. -/
theorem prologue {resource : Resources} {initial : State}
    (pre : ResourcePre (Compiler.program .gccSeparate) resource initial) (choices : CallReturn.Choices) :
    ∃ evolved middle, CoveredHistory resource.descriptor choices resource.shared initial evolved middle 5 [] ∧
      Current resource.descriptor evolved middle ∧ Invariant resource initial middle resource.count.toNat := by
  have entry : initial.rip = resource.descriptor.frame.call.code := by
    simpa [Compiler.program] using pre.entry
  have slot0 : StackFrame.Slot resource.descriptor.frame (CallReturn.stackDestination initial) := by
    rw [CallReturn.stackDestination, pre.stack]
    exact depth_slot pre.current pre.stackCapacity (by decide : 8 ≤ 8) (by decide)
  let s1 := pushed initial .rbp
  obtain ⟨w1, step0, success0, effect0, read0⟩ := push_next pre.current pre.code
    (by decide : (0, .push64 .rbp false) ∈ Compiler.sites .gccSeparate) pre.entry slot0 (choices 0)
  have c1 : Current resource.descriptor w1 s1 := step0.current pre.current
  have pc1 : s1.rip = resource.descriptor.frame.call.code + 1 := by
    simp [s1, pushed, CallReturn.pushState, CallReturn.stackLength, entry]
  have sp1 : s1.registers .rsp = resource.descriptor.frame.top - 8 := by
    simp [s1, pushed, CallReturn.pushState, CallReturn.stackDestination, State.writeRegister, pre.stack]
  let s2 := moved s1 .rbp .rdi
  have step1 := move_next c1 pre.code
    (by decide : (1, .sequential (.movReg64 .rbp .rdi)) ∈ Compiler.sites .gccSeparate) pc1 ((choices.drop 1) 0)
  have c2 : Current resource.descriptor w1 s2 := step1.current c1
  have pc2 : s2.rip = resource.descriptor.frame.call.code + 4 := by
    simp [s2, moved, pc1, BitVec.add_assoc]
  have sp2 : s2.registers .rsp = resource.descriptor.frame.top - 8 := by
    simpa [s2, moved, State.writeRegister] using sp1
  have slot2 : StackFrame.Slot resource.descriptor.frame (CallReturn.stackDestination s2) := by
    rw [CallReturn.stackDestination, sp2, BitVec.sub_sub]
    exact depth_slot c2 pre.stackCapacity (by decide : 8 ≤ 16) (by decide)
  let s3 := pushed s2 .rbx
  obtain ⟨w3, step2, success2, effect2, read2⟩ := push_next c2 pre.code
    (by decide : (4, .push64 .rbx false) ∈ Compiler.sites .gccSeparate) pc2 slot2 (((choices.drop 1).drop 1) 0)
  have c3 : Current resource.descriptor w3 s3 := step2.current c2
  have pc3 : s3.rip = resource.descriptor.frame.call.code + 5 := by
    simp [s3, pushed, CallReturn.pushState, CallReturn.stackLength, pc2, BitVec.add_assoc]
  have sp3 : s3.registers .rsp = resource.descriptor.frame.top - 16 := by
    simp [s3, pushed, CallReturn.pushState, CallReturn.stackDestination, State.writeRegister, sp2, BitVec.sub_sub]
  let s4 := moved s3 .rbx .rdx
  have step3 := move_next c3 pre.code
    (by decide : (5, .sequential (.movReg64 .rbx .rdx)) ∈ Compiler.sites .gccSeparate) pc3
    ((((choices.drop 1).drop 1).drop 1) 0)
  have c4 : Current resource.descriptor w3 s4 := step3.current c3
  have pc4 : s4.rip = resource.descriptor.frame.call.code + 8 := by
    simp [s4, moved, pc3, BitVec.add_assoc]
  have sp4 : s4.registers .rsp = resource.descriptor.frame.top - 16 := by
    simpa [s4, moved, State.writeRegister] using sp3
  have slot4 : StackFrame.Slot resource.descriptor.frame (CallReturn.stackDestination s4) := by
    rw [CallReturn.stackDestination, sp4, BitVec.sub_sub]
    exact depth_slot c4 pre.stackCapacity (by decide : 8 ≤ 24) (by decide)
  let s5 := pushed s4 .rcx
  obtain ⟨w5, step4, success4, effect4, _⟩ := push_next c4 pre.code
    (by decide : (8, .push64 .rcx false) ∈ Compiler.sites .gccSeparate) pc4 slot4
    (((((choices.drop 1).drop 1).drop 1).drop 1) 0)
  have c5 : Current resource.descriptor w5 s5 := step4.current c4
  have history : CoveredHistory resource.descriptor choices resource.shared initial w5 s5 5 [] :=
    .next step0.step step0.fetch (.next step1.step step1.fetch (.next step2.step step2.fetch
      (.next step3.step step3.fetch (.next step4.step step4.fetch .nil))))
  have saved1 : readWord s2.memory (resource.descriptor.frame.top - 8) = .ok (initial.registers .rbp) := by
    change readWord s1.memory (resource.descriptor.frame.top - 8) = _
    simpa only [CallReturn.stackDestination, pre.stack] using read0
  have effect2' : Borrowing.StoreEffect64 w1 w3 (resource.descriptor.frame.top - 16) (s2.registers .rbx) := by
    simpa [CallReturn.stackDestination, sp2, BitVec.sub_sub] using effect2
  have saved3 : readWord s4.memory (resource.descriptor.frame.top - 8) = .ok (initial.registers .rbp) :=
    (OS.CallMemory64.store64_preserves_private c2 c3 effect2'
      (depth_slot c2 pre.stackCapacity (by decide : 8 ≤ 8) (by decide))
      (depth_disjoint c2 pre.stackCapacity (by decide : 16 ≤ 32) (by decide : 8 ≤ 32) (by decide))).trans saved1
  have savedBx : readWord s4.memory (resource.descriptor.frame.top - 16) = .ok (initial.registers .rbx) := by
    change readWord s3.memory (resource.descriptor.frame.top - 16) = _
    have observed : readWord s3.memory (resource.descriptor.frame.top - 16) = .ok (s2.registers .rbx) := by
      simpa [CallReturn.stackDestination, sp2, BitVec.sub_sub] using read2
    have value : s2.registers .rbx = initial.registers .rbx := by
      simp [s2, moved, s1, pushed, CallReturn.pushState, State.writeRegister]
    exact observed.trans (congrArg Except.ok value)
  have effect4' : Borrowing.StoreEffect64 w3 w5 (resource.descriptor.frame.top - 24) (s4.registers .rcx) := by
    simpa [CallReturn.stackDestination, sp4, BitVec.sub_sub] using effect4
  have saved : Saved resource.descriptor initial s5 :=
    ⟨(OS.CallMemory64.store64_preserves_private c4 c5 effect4'
        (depth_slot c4 pre.stackCapacity (by decide : 8 ≤ 8) (by decide))
        (depth_disjoint c4 pre.stackCapacity (by decide : 24 ≤ 32) (by decide : 8 ≤ 32) (by decide))).trans saved3,
      (OS.CallMemory64.store64_preserves_private c4 c5 effect4'
        (depth_slot c4 pre.stackCapacity (by decide : 8 ≤ 16) (by decide))
        (depth_disjoint c4 pre.stackCapacity (by decide : 24 ≤ 32) (by decide : 16 ≤ 32) (by decide))).trans savedBx⟩
  have target0 := private_target pre.current c1 slot0 success0
  have target2 := private_target c2 c3 slot2 success2
  have target4 := private_target c4 c5 slot4 success4
  have target : readWord s5.memory resource.descriptor.target = readWord initial.memory resource.descriptor.target :=
    target4.trans (target2.trans target0)
  have frame : Frame initial s5 := (frame_push initial .rbp).trans
    ((frame_move s1 .rbp .rdi (by decide)).trans ((frame_push s2 .rbx).trans
      ((frame_move s3 .rbx .rdx (by decide)).trans (frame_push s4 .rcx))))
  refine ⟨w5, s5, history, c5, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, Nat.le_refl _, ?_, saved, frame⟩
  · simp [s5, pushed, CallReturn.pushState, CallReturn.stackLength, pc4, BitVec.add_assoc]
  · simp [s5, pushed, CallReturn.pushState, CallReturn.stackDestination, State.writeRegister, sp4, BitVec.sub_sub]
  · simpa [s5, pushed, s4, moved, s3, s2, s1, CallReturn.pushState, State.writeRegister] using pre.pointer
  · simpa [s5, pushed, s4, moved, s3, s2, s1, CallReturn.pushState, State.writeRegister] using congrArg BitVec.toNat pre.counter
  · simp [s5, pushed, s4, moved, s3, s2, s1, CallReturn.pushState, State.writeRegister, pre.argument]
  · simpa only [↓reduceIte] using target

end EDSL.CallMemoryLoop64.GCC
