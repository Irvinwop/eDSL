/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.ClosedForm.Steps

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.ClosedForm
open X86 OS

/-- Facts at the actual conditional branch, derived from the decoded prefix.
The prefix has performed no memory operation and leaves RDX as the count. -/
structure Front (profile : Profile) (resource : Resources) (initial middle : State) : Prop where
  pc : middle.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 (guardOffset profile)
  stack : middle.registers .rsp = resource.descriptor.frame.top
  pointer : middle.registers .rdi = resource.descriptor.target
  value : middle.registers .rax = resource.value + resource.count
  zero : middle.flags.getLsbD 6 = (resource.count == 0)
  memory : middle.memory = initial.memory
  frame : Frame initial middle

theorem front {profile resource initial}
    (pre : ResourcePre (program profile) resource initial) (choices : CallReturn.Choices) :
    ∃ middle, CoveredHistory resource.descriptor choices resource.shared initial
        resource.shared middle (frontCost profile) [] ∧ Front profile resource initial middle := by
  have entry : initial.rip = resource.descriptor.frame.call.code := by
    simpa [program] using pre.entry
  cases profile with
  | gcc =>
    let s1 := summed initial
    have one0 := sum_next pre.current pre.code entry (choices 0)
    have current1 : Current resource.descriptor resource.shared s1 := one0.current pre.current
    have pc1 : s1.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 (testOffset .gcc) := by
      simp [s1, summed, entry, testOffset]
    let s2 := tested s1 (choices 1)
    have one1 := test_next (profile := .gcc) current1 pre.code pc1 ((choices.drop 1) 0)
    have history : CoveredHistory resource.descriptor choices resource.shared initial
        resource.shared s2 2 [] := .next one0.step one0.fetch (.next one1.step one1.fetch .nil)
    refine ⟨s2, history, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, (frame_summed initial).trans (frame_tested s1 _)⟩
    · simp [s2, tested, pc1, testOffset, guardOffset, BitVec.add_assoc]
    · simp [s2, tested, s1, summed, State.writeRegister, pre.stack]
    · simp [s2, tested, s1, summed, State.writeRegister, pre.pointer]
    · simp [s2, tested, s1, summed, State.writeRegister, pre.argument, pre.counter]
    · simp only [s2, tested, Sequential.logicalFlags64_zero, BitVec.and_self]
      simp [s1, summed, State.writeRegister, pre.counter]
  | clang =>
    let s1 := moved initial
    have one0 := move_next pre.current pre.code entry (choices 0)
    have current1 : Current resource.descriptor resource.shared s1 := one0.current pre.current
    have pc1 : s1.rip = resource.descriptor.frame.call.code + 3 := by
      simp [s1, moved, entry]
    let s2 := added s1
    have one1 := add_next current1 pre.code pc1 ((choices.drop 1) 0)
    have current2 : Current resource.descriptor resource.shared s2 := one1.current current1
    have pc2 : s2.rip = resource.descriptor.frame.call.code + BitVec.ofNat 64 (testOffset .clang) := by
      simp [s2, added, pc1, testOffset, BitVec.add_assoc]
    let s3 := tested s2 (choices 2)
    have one2 := test_next (profile := .clang) current2 pre.code pc2 (((choices.drop 1).drop 1) 0)
    have history : CoveredHistory resource.descriptor choices resource.shared initial
        resource.shared s3 3 [] :=
      .next one0.step one0.fetch (.next one1.step one1.fetch (.next one2.step one2.fetch .nil))
    refine ⟨s3, history, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl,
      (frame_moved initial).trans ((frame_added s1).trans (frame_tested s2 _))⟩
    · simp [s3, tested, pc2, testOffset, guardOffset, BitVec.add_assoc]
    · simp [s3, tested, s2, added, s1, moved, State.writeRegister, pre.stack]
    · simp [s3, tested, s2, added, s1, moved, State.writeRegister, pre.pointer]
    · simp [s3, tested, s2, added, s1, moved, State.writeRegister, pre.argument, pre.counter]
    · simp only [s3, tested, Sequential.logicalFlags64_zero, BitVec.and_self]
      simp [s2, added, s1, moved, State.writeRegister, pre.counter]

end EDSL.CallMemoryLoop64.ClosedForm
