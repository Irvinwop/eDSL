/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.LowerBound
import EDSL.StoreReturn32.Resources

set_option warningAsError true

/-! Costs count modeled decoded instructions, including RET, in the current
sequential ISA. These separate cost theorems do not change admission or claim
contracts, and do not count CPU cycles, micro-ops or source operations. -/

namespace EDSL.StoreReturn32
open X86 X86.Sequential
open Grading.Write32 (Input Pre Useful RawPolicy Resources ResourcePre ResourceReturn resourceInput)

/-- Every supported exact window attains three for every raw input and AF
stream. The actual result retains the original eight-byte stack-only read. -/
theorem exact_three {shape : Shape} {input : Input} {initial : State}
    (pre : Pre shape.bytes input initial) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post input initial result.state ∧ result.instructions = 3 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      RawPolicy shape.bytes input initial := by
  obtain ⟨result, execution, post, cost, reads⟩ := (raw_semantics pre).1 choices
  exact ⟨result, execution, post, cost, reads, (raw_semantics pre).2⟩

/-- The same actual result carries the existing resource return: its checked
world history, current RAM coupling, complete frame and original live loans.
Neither resource admission nor the returned-world predicate is strengthened. -/
theorem resource_exact_three {shape : Shape} {resource : Resources} {initial : State}
    (pre : ResourcePre shape.bytes resource initial) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result ∧ result.instructions = 3 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  obtain ⟨result, execution, contract, returned⟩ := (resource_semantics pre).1 choices
  exact ⟨result, execution, contract.1, returned, contract.2⟩

/-- Model-relative optimum for a useful input whose returned pointer must
change. Both the original shape and every compared candidate start with RAX
different from the target. ANY bytes, initial code/ABI state, AF stream and
actual returned result in the explicit candidate class are compared against
the same independent input, Post and unchanged registered RawPolicy. This is
not a global x86, physical-cycle or unrestricted-effect optimality claim. -/
theorem optimal_for_useful_input {shape : Shape} {input : Input} {initial : State}
    (pre : Pre shape.bytes input initial) (useful : Useful input)
    (needed : initial.registers .rax ≠ input.address) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Post input initial result.state ∧ result.instructions = 3 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      RawPolicy shape.bytes input initial ∧
      ∀ (candidateBytes : List Byte) (candidateInitial : State)
        (candidateChoices : Choices) (candidateResult : Result),
        Pre candidateBytes input candidateInitial →
        candidateInitial.registers .rax ≠ input.address →
        RawPolicy candidateBytes input candidateInitial →
        Sequential.Executes candidateChoices candidateInitial candidateResult →
        Post input candidateInitial candidateResult.state →
        result.instructions ≤ candidateResult.instructions := by
  obtain ⟨result, execution, post, cost, reads, policy⟩ := exact_three pre choices
  have attained : result.instructions = 3 := Nat.le_antisymm (Nat.le_of_eq cost)
    (minimum_modeled_instructions pre useful needed policy execution post)
  refine ⟨result, execution, post, attained, reads, policy, ?_⟩
  intro candidateBytes candidateInitial candidateChoices candidateResult
    candidatePre candidateNeeded candidatePolicy candidateExecution candidatePost
  rw [attained]
  exact minimum_modeled_instructions candidatePre useful candidateNeeded candidatePolicy
    candidateExecution candidatePost

end EDSL.StoreReturn32
