/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.Clang.Iteration

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Clang
open X86 OS

structure Outcome (d : OS.CallMemory64.Descriptor) (a b inputValue : Word) (n : Nat)
    (initial final : State) : Prop where
  value : final.registers .rax = inputValue + BitVec.ofNat 64 n
  stored : readWord final.memory d.target =
    if n = 0 then readWord initial.memory d.target else .ok (inputValue + BitVec.ofNat 64 (n - 1))
  r14 : final.registers .r14 = a
  rbx : final.registers .rbx = b
  pc : final.rip = d.frame.call.returnAddress
  stack : final.registers .rsp = d.frame.top + 8
  frame : Frame initial final

/-- The four-instruction epilogue restores both actual saved values, drops
the pad without reading it, and returns through the original caller loan. -/
theorem exit {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {a b value : Word} (current : OS.CallMemory64.Current d w s)
    (same : d.frame.call.bytes = text) (capacity : 32 ≤ d.frame.capacity)
    (inv : Loop d a b value 0 s) (choices : CallReturn.Choices) :
    ∃ result, OS.CallMemory64.CoveredExecution d choices w s w result ∧
      result.instructions = 4 ∧ Outcome d a b value 0 s result.state := by
  have pc0 : s.rip = d.frame.call.code + 37 := by simpa using inv.pc
  let s1 := addsp s
  have one1 : One d (choices 0) w w s s1 := plain_one current same
    (by decide : (37, .sequential (.addImm64 .rsp 8)) ∈ Compiler.sites .clangSeparate) pc0 rfl rfl rfl
  have c1 := one1.current current
  have pc1 : s1.rip = d.frame.call.code + 41 := by simp [s1, addsp, pc0, BitVec.add_assoc]
  have stack1 : s1.registers .rsp = d.frame.top - 16 := by
    simp [s1, addsp, State.writeRegister, inv.stack, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have slot1 : StackFrame.Slot d.frame (s1.registers .rsp) := by
    rw [stack1]
    exact slot c1 capacity (by decide : 8 ≤ 16) (by decide)
  have read1 : readWord s1.memory (s1.registers .rsp) = .ok b := by
    rw [stack1]
    exact inv.saved.low
  let s2 := pop s1 .rbx false b
  have step2 := pop_step c1 same
    (by decide : (41, .pop64 .rbx false) ∈ Compiler.sites .clangSeparate) pc1 slot1 read1 (choices 1)
  have c2 := step2.current c1
  have pc2 : s2.rip = d.frame.call.code + 42 := by
    simp [s2, pop, CallReturn.popState, CallReturn.stackLength, pc1, BitVec.add_assoc]
  have stack2 : s2.registers .rsp = d.frame.top - 8 := by
    simp [s2, pop, CallReturn.popState, State.writeRegister, stack1,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have slot2 : StackFrame.Slot d.frame (s2.registers .rsp) := by
    rw [stack2]
    exact slot c2 capacity (by decide : 8 ≤ 8) (by decide)
  have read2 : readWord s2.memory (s2.registers .rsp) = .ok a := by
    rw [stack2]
    exact inv.saved.high
  let s3 := pop s2 .r14 true a
  have step3 := pop_step c2 same
    (by decide : (42, .pop64 .r14 true) ∈ Compiler.sites .clangSeparate) pc2 slot2 read2 (choices 2)
  have c3 := step3.current c2
  have pc3 : s3.rip = d.frame.call.code + 44 := by
    simp [s3, pop, CallReturn.popState, CallReturn.stackLength, pc2, BitVec.add_assoc]
  have stack3 : s3.registers .rsp = d.frame.top := by
    simp [s3, pop, CallReturn.popState, State.writeRegister, stack2, BitVec.sub_add_cancel]
  let final := ret s3 d.frame.call.returnAddress
  have step4 := root_ret_step c3 same pc3 stack3 (choices 3)
  have fetch2 := fetch c1 same
    (by decide : (41, .pop64 .rbx false) ∈ Compiler.sites .clangSeparate) pc1
  have fetch3 := fetch c2 same
    (by decide : (42, .pop64 .r14 true) ∈ Compiler.sites .clangSeparate) pc2
  have fetch4 := fetch c3 same
    (by decide : (44, .sequential (.legacy .ret)) ∈ Compiler.sites .clangSeparate) pc3
  obtain ⟨_, step1, fetch1⟩ := one1
  refine ⟨_, .next step1 fetch1 (.next step2 fetch2 (.next step3 fetch3 (.ret step4 fetch4))), rfl, ?_⟩
  change Outcome d a b value 0 s final
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · simp [final, ret, s3, s2, pop, CallReturn.popState, s1, addsp, State.writeRegister, inv.accumulator]
  · simp [final, ret, s3, pop, CallReturn.popState, State.writeRegister]
  · simp [final, ret, s3, s2, pop, CallReturn.popState, State.writeRegister]
  · simp [final, ret, State.writeRegister, stack3]
  · exact (frame_addsp s).trans ((frame_pop s1 .rbx false b (by decide)).trans
      ((frame_pop s2 .r14 true a (by decide)).trans (frame_ret s3 _)))

theorem advance_value (value : Word) (n : Nat) :
    (value + 1) + BitVec.ofNat 64 n = value + BitVec.ofNat 64 (n + 1) := by
  rw [ofNat_succ]
  simp only [BitVec.add_assoc, BitVec.add_comm 1]

theorem advance_stored (value : Word) {n : Nat} (positive : 0 < n) :
    (value + 1) + BitVec.ofNat 64 (n - 1) = value + BitVec.ofNat 64 n := by
  have natural : n - 1 + 1 = n := by omega
  exact (advance_value value (n - 1)).trans (congrArg (fun k => value + BitVec.ofNat 64 k) natural)

/-- Natural induction constructs the entire actual mixed execution for every
full-width remaining count and every AF stream. No future run is assumed. -/
theorem loop_execution {d : OS.CallMemory64.Descriptor}
    (same : d.frame.call.bytes = text) (capacity : 32 ≤ d.frame.capacity)
    (n : Nat) : ∀ {w : Borrowing.State} {s : State} {a b value : Word},
      OS.CallMemory64.Current d w s → n < 2^64 → Loop d a b value n s →
      ∀ choices : CallReturn.Choices, ∃ evolved result,
        OS.CallMemory64.CoveredExecution d choices w s evolved result ∧
        result.instructions = 4 + 9 * n ∧ Outcome d a b value n s result.state := by
  induction n with
  | zero =>
    intro w s a b value current _ inv choices
    obtain ⟨result, execution, cost, post⟩ := exit current same capacity inv choices
    exact ⟨w, result, execution, cost, post⟩
  | succ n ih =>
    intro w s a b value current bound inv choices
    obtain ⟨middle, after, block, nextInv, frame, stored⟩ :=
      iteration current same capacity bound inv choices
    obtain ⟨evolved, result, execution, cost, post⟩ :=
      ih (block.current current) (by omega) nextInv (choices.drop 9)
    obtain ⟨combined, covered, endpoint, instructions⟩ := block.finish execution
    refine ⟨evolved, combined, covered, ?_, ?_⟩
    · omega
    · rw [endpoint]
      refine ⟨post.value.trans (advance_value value n), ?_, post.r14, post.rbx, post.pc,
        post.stack, frame.trans post.frame⟩
      by_cases empty : n = 0
      · subst n
        have kept := post.stored
        simp only [ite_true] at kept
        simpa using kept.trans stored
      · have finalData := post.stored
        simp only [ite_eq_right empty] at finalData
        simpa only [Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one,
          advance_stored value (by omega : 0 < n)] using finalData

end EDSL.CallMemoryLoop64.Clang
