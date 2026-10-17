/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Verification

set_option warningAsError true

namespace EDSL.OS.CallMemory64.CPU
open X86

/-- In the accepted mixed relation, an actual step retains either RAX or the
complete RAM. Ordinary DATA64 stores and private CALL/PUSH writes retain RAX;
the unchanged-effect case requires full RAM equality, including for POP/LEA.
This is a policy-scoped fact, not a statement about arbitrary x86 operations. -/
theorem Step.rax_or_memory {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation) :
    after.registers .rax = before.registers .rax ∨ after.memory = before.memory := by
  obtain ⟨instruction, raw, _, actual, cpu, _, effect, _⟩ := step
  cases effect with
  | stack effect =>
    cases effect with
    | call _ _ =>
      obtain ⟨_, memory, _, same⟩ := CallReturn.execute_call_success_iff.mp actual
      subst raw
      have sameCpu := Option.some.inj cpu
      rw [← sameCpu]
      exact .inl (by simp [CallReturn.callState, State.writeRegister])
    | push _ _ =>
      obtain ⟨memory, _, same⟩ := CallReturn.execute_push_success_iff.mp actual
      subst raw
      have sameCpu := Option.some.inj cpu
      rw [← sameCpu]
      exact .inl (by simp [CallReturn.pushState, State.writeRegister])
    | unchanged _ memory => exact .inr memory
  | data64 intent _ =>
    rw [CallReturn.execute_sequential] at actual
    obtain ⟨memory, _, same⟩ := (Sequential.execute_storeIntent64_success_iff intent).mp actual
    subst raw
    have sameCpu := Option.some.inj cpu
    rw [← sameCpu]
    exact .inl rfl

/-- The terminal original-slot RET retains both RAX and complete RAM. -/
theorem Step.returned_preserves {descriptor shared evolved before after af reads}
    (step : Step descriptor shared evolved before after af ⟨.returned after, reads⟩) :
    after.registers .rax = before.registers .rax ∧ after.memory = before.memory := by
  obtain ⟨_, _, _, _, _, same, _⟩ := CallReturn.boundaryStep_terminal_iff.mp step.machine
  rw [same]
  exact ⟨by simp [State.writeRegister], rfl⟩

/-- Changing both outputs and returning takes at least three instructions in
the actual mixed relation. A trace of length two has only one pre-RET step. -/
theorem Execution.changed_rax_memory_needs_three
    {descriptor choices shared initial evolved result}
    (execution : Execution descriptor choices shared initial evolved result)
    (raxChanged : result.state.registers .rax ≠ initial.registers .rax)
    (memoryChanged : result.state.memory ≠ initial.memory) :
    3 ≤ result.instructions := by
  cases execution with
  | ret step => exact False.elim (raxChanged step.returned_preserves.1)
  | next step tail =>
    cases tail with
    | ret last =>
      rcases step.rax_or_memory with rax | memory
      · exact False.elim (raxChanged (last.returned_preserves.1.trans rax))
      · exact False.elim (memoryChanged (last.returned_preserves.2.trans memory))
    | next _ tail =>
      have positive := CallReturn.ExecutesFrom.positive tail.machine
      simp only [Sequential.Result.prepend]
      omega

end EDSL.OS.CallMemory64.CPU

namespace EDSL.CallMemory64
open X86

/-- Every accepted candidate needs at least three modeled instructions on an
admitted useful input. Fixed-choice determinism identifies this actual run
with the accepted covered mixed trace. The two changes follow from the
independent arithmetic and stored-word postconditions, not a future store or
instruction-shape premise. This bounds this resource policy's modeled count;
it asserts neither a bound for all raw ISA programs nor CPU cycles. -/
theorem minimum_modeled_instructions {program} (claim : Claim program)
    {resource initial choices result} (pre : ResourcePre program resource initial)
    (useful : Useful resource initial) (actual : CallReturn.Executes choices initial result) :
    3 ≤ result.instructions := by
  obtain ⟨evolved, returned⟩ := claim.1.all_results pre actual
  have raxChanged : result.state.registers .rax ≠ initial.registers .rax := by
    intro same
    exact useful.1 ((congrArg BitVec.toNat same).symm.trans returned.post.value)
  have memoryChanged : result.state.memory ≠ initial.memory := by
    intro same
    have stored := returned.post.stored
    rw [same] at stored
    exact useful.2 stored
  exact returned.covered.execution.changed_rax_memory_needs_three raxChanged memoryChanged

/-- Evaluator form of `minimum_modeled_instructions`, with arbitrary fuel. -/
theorem minimum_run {program} (claim : Claim program)
    {resource initial choices fuel result} (pre : ResourcePre program resource initial)
    (useful : Useful resource initial)
    (actual : CallReturn.run choices fuel initial = .ok result) :
    3 ≤ result.instructions :=
  minimum_modeled_instructions claim pre useful (CallReturn.run_sound actual)

end EDSL.CallMemory64
