/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.Clang.Prologue

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Clang
open X86 OS

theorem Frame.abi {initial final : State} (frame : Frame initial final)
    (r14 : final.registers .r14 = initial.registers .r14)
    (rbx : final.registers .rbx = initial.registers .rbx) :
    ∀ r, r ∉ CallStack.clobbers → final.registers r = initial.registers r := by
  intro r outside
  by_cases high : r = .r14
  · exact high ▸ r14
  by_cases low : r = .rbx
  · exact low ▸ rbx
  apply frame.registers r
  cases r <;> simp_all [changed, CallStack.clobbers]

theorem target_eq (value count : Word) (nonzero : count ≠ 0) :
    value + BitVec.ofNat 64 (count.toNat - 1) = targetWord value count := by
  have positive : 0 < count.toNat := by
    have notzero : count.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
    omega
  calc
    value + BitVec.ofNat 64 (count.toNat - 1) =
        BitVec.ofNat 64 (value.toNat + (count.toNat - 1)) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    _ = targetWord value count := congrArg (BitVec.ofNat 64) (by
      change value.toNat + (count.toNat - 1) = value.toNat + count.toNat - 1
      omega)

/-- The actual model instruction count is a conclusion of execution, entirely
separate from resource admission and the independent arithmetic contract. -/
def cost (count : Word) : Nat := if count = 0 then 4 else 12 + 9 * count.toNat

theorem zero_covered {resource initial}
    (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (zero : resource.count = 0) (choices : CallReturn.Choices) :
    ∃ result, OS.CallMemory64.CoveredExecution resource.descriptor choices
        resource.shared initial resource.shared result ∧
      result.instructions = 4 ∧ Post (resourceInput resource) initial result.state := by
  let d := resource.descriptor
  let s2 := front initial (choices 1)
  have block2 : Block d choices resource.shared initial resource.shared s2 2 := front_block pre choices
  have current2 : OS.CallMemory64.Current d resource.shared s2 := block2.current pre.current
  have flag2 : s2.flags.getLsbD 6 = true := by rw [front_zero pre, zero]; rfl
  let s3 := jump s2 (d.frame.call.code + 44)
  have one3 : One d (choices 2) resource.shared resource.shared s2 s3 :=
    je_one current2 pre.code (front_pc pre _) flag2 (choices 2)
  have current3 : OS.CallMemory64.Current d resource.shared s3 := one3.current current2
  have pc3 : s3.rip = d.frame.call.code + 44 := rfl
  have stack3 : s3.registers .rsp = d.frame.top := by
    simp [s3, jump, s2, front, test, mov, State.writeRegister, pre.stack, d]
  let final := ret s3 d.frame.call.returnAddress
  have step4 := root_ret_step current3 pre.code pc3 stack3 (choices 3)
  have fetch4 := fetch current3 pre.code
    (by decide : (44, .sequential (.legacy .ret)) ∈ Compiler.sites .clangSeparate) pc3
  obtain ⟨_, step3, fetch3⟩ := one3
  have tail : OS.CallMemory64.CoveredExecution d (choices.drop 2) resource.shared s2
      resource.shared ⟨final, 2, _⟩ :=
    .next (choices := choices.drop 2) step3 fetch3
      (.ret (choices := (choices.drop 2).drop 1) step4 fetch4)
  obtain ⟨result, execution, endpoint, instructions⟩ := block2.finish tail
  have memory := execution.memory_frame pre.current
  rw [endpoint] at memory
  have frame : Frame initial final :=
    (front_frame initial _).trans ((frame_jump s2 _).trans (frame_ret s3 _))
  refine ⟨result, execution, by omega, ?_⟩
  rw [endpoint]
  refine ⟨?_, ?_, memory.1, memory.2.1, memory.2.2, rfl, ?_, frame.abi rfl rfl, frame.flags⟩
  · change (final.registers .rax).toNat = resultNat resource.value resource.count
    have value : final.registers .rax = resource.value := by
      simp [final, ret, s3, jump, s2, front, test, mov, State.writeRegister, pre.argument]
    rw [value, zero]
    change resource.value.toNat = (resource.value.toNat + 0) % 2^64
    rw [Nat.add_zero, Nat.mod_eq_of_lt resource.value.isLt]
  · change readWord final.memory d.target =
      if resource.count = 0 then readWord initial.memory d.target else _
    rw [ite_eq_left zero]
    rfl
  · simp [final, ret, State.writeRegister, stack3, pre.stack, d]

theorem positive_covered {resource initial}
    (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (nonzero : resource.count ≠ 0) (choices : CallReturn.Choices) :
    ∃ evolved result, OS.CallMemory64.CoveredExecution resource.descriptor choices
        resource.shared initial evolved result ∧
      result.instructions = 12 + 9 * resource.count.toNat ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨world, after, block, inv, frame⟩ := prologue pre nonzero choices
  obtain ⟨evolved, result, execution, cost, post⟩ :=
    loop_execution pre.code pre.stackCapacity resource.count.toNat (block.current pre.current)
      resource.count.isLt inv (choices.drop 8)
  obtain ⟨combined, covered, endpoint, instructions⟩ := block.finish execution
  have memory := covered.memory_frame pre.current
  rw [endpoint] at memory
  have allFrame : Frame initial result.state := frame.trans post.frame
  have positive : resource.count.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
  refine ⟨evolved, combined, covered, by omega, ?_⟩
  rw [endpoint]
  refine ⟨?_, ?_, memory.1, memory.2.1, memory.2.2, post.pc, ?_,
    allFrame.abi post.r14 post.rbx, allFrame.flags⟩
  · change (result.state.registers .rax).toNat = resultNat resource.value resource.count
    rw [post.value, BitVec.ofNat_toNat]
    exact resultNat_add resource.value resource.count
  · change readWord result.state.memory resource.descriptor.target =
      if resource.count = 0 then _ else .ok (targetWord resource.value resource.count)
    rw [ite_eq_right nonzero]
    have stored := post.stored
    rw [ite_eq_right positive, target_eq resource.value resource.count nonzero] at stored
    exact stored
  · rw [post.stack, pre.stack]

/-- Every admitted current machine/resource state and every AF choice stream
has a returning covered mixed execution with the independent counted contract.
The full64 maximum and zero are included without a fuel or loop premise. -/
theorem covered {resource initial}
    (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved result, OS.CallMemory64.CoveredExecution resource.descriptor choices
        resource.shared initial evolved result ∧
      result.instructions = cost resource.count ∧ Post (resourceInput resource) initial result.state := by
  by_cases empty : resource.count = 0
  · obtain ⟨result, execution, instructions, post⟩ := zero_covered pre empty choices
    exact ⟨resource.shared, result, execution, by simpa only [cost, ite_eq_left empty] using instructions, post⟩
  · obtain ⟨evolved, result, execution, instructions, post⟩ := positive_covered pre empty choices
    exact ⟨evolved, result, execution, by simpa only [cost, ite_eq_right empty] using instructions, post⟩

theorem allinputsemantic_claim : SemanticClaim (Compiler.program .clangSeparate) := by
  intro resource initial pre choices
  obtain ⟨evolved, result, execution, _, post⟩ := covered pre choices
  exact ⟨evolved, result, execution, post⟩

/-- Useful nonvacuity comes from checked capacity-32 allocation independently
of the execution proof. This client fixture is outside foundational imports. -/
theorem claim : EDSL.CallMemoryLoop64.Claim (Compiler.program .clangSeparate) :=
  ⟨allinputsemantic_claim, domain_nonvacuous _ (Compiler.positive .clangSeparate)
    (Compiler.bounded .clangSeparate)⟩

/-- Exact evaluator success, current endpoint and checked mixed history all
refer to the same execution and its actual accumulated instruction count. -/
theorem evaluated {resource initial}
    (pre : ResourcePre (Compiler.program .clangSeparate) resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices (cost resource.count) initial = .ok result ∧
      OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved result ∧
      Returned resource initial choices evolved result ∧ result.instructions = cost resource.count := by
  obtain ⟨evolved, result, execution, instructions, post⟩ := covered pre choices
  have actual := execution.run (Nat.le_of_eq instructions)
  refine ⟨evolved, result, ?_, execution, Returned.of_covered pre execution post, instructions⟩
  simpa only [CallReturn.run, pre.stack] using actual

#print axioms allinputsemantic_claim
#print axioms claim
#print axioms evaluated

end EDSL.CallMemoryLoop64.Clang
