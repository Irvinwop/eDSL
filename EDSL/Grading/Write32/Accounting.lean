/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.X86.Sequential.Return

/-! Costs count retired modeled decoded instructions, including RET, in the
current sequential ISA. They do not count CPU cycles, micro-ops, instruction
bytes or source/IR operations. The lower bound is conditional on useful inputs
and the independent task contract; it does not establish unrestricted x86
optimality or add a cost constraint to grader acceptance. -/

namespace EDSL.Grading.Write32
open X86 X86.Sequential

/-- Independent raw Pre/Post plus Useful forces a changed target value. -/
theorem useful_requires_memory_change {candidateBytes : List Byte} {input : Write32.Input}
    {initial final : State} (pre : Write32.Pre candidateBytes input initial)
    (useful : Write32.Useful input) (post : Write32.Post input initial final) :
    final.memory ≠ initial.memory := by
  intro same
  have value := post.value
  rw [same, pre.oldValue] at value
  exact useful (Except.ok.inj value)

/-- Universal candidate lower bound in the present modeled sequential ISA.
No RawPolicy premise is needed, so this includes every policy-admitted candidate.
It does not assert return or correctness of candidates that lack these premises. -/
theorem minimum_modeled_instructions {candidateBytes : List Byte}
    {input : Write32.Input} {choices : Choices} {initial : State} {result : Result}
    (pre : Write32.Pre candidateBytes input initial) (useful : Write32.Useful input)
    (execution : Sequential.Executes choices initial result)
    (post : Write32.Post input initial result.state) : 2 ≤ result.instructions :=
  Sequential.Executes.memory_change_needs_two execution (useful_requires_memory_change pre useful post)

/-- The fixed registered claim supplies Post for ANY actual execution on a
useful admitted input. Candidates do not supply a different cost contract. -/
theorem claim_minimum {candidateBytes : List Byte} {input : Input}
    {choices : Choices} {initial : State} {result : Result}
    (claim : Grading.Claim .write32 candidateBytes)
    (pre : Pre candidateBytes input initial) (useful : Useful input)
    (execution : Sequential.Executes choices initial result) : 2 ≤ result.instructions := by
  obtain ⟨covered, checked, post⟩ := (claim.1.machine input initial pre).1 choices
  have same := Sequential.Executes.fixed_choices_unique checked execution
  rw [same] at post
  exact minimum_modeled_instructions pre useful execution post

/-- The existing exact 89 37 C3 implementation attains two for every raw Pre
and choice stream. Its independently proved Post and raw trace policy are kept.
The explicit actual steps expose the cost hidden by raw_semantics' interface. -/
theorem exact_two {input : Write32.Input} {initial : State}
    (pre : Write32.Pre Write32.bytes input initial) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Write32.Post input initial result.state ∧ result.instructions = 2 ∧
      Write32.RawPolicy Write32.bytes input initial := by
  obtain ⟨result, execution, post⟩ := (Write32.raw_semantics pre).1 choices
  have concrete : Sequential.Executes choices initial
      ((⟨Write32.returned initial input.returnAddress, 1,
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ : Result).prepend 1 []) :=
    .next (Write32.store_step pre (choices 0))
      (.ret (Write32.ret_step pre ((choices.drop 1) 0)))
  have same := Sequential.Executes.fixed_choices_unique execution concrete
  refine ⟨result, execution, post, ?_, (Write32.raw_semantics pre).2⟩
  rw [same]
  rfl

/-- The counted managed execution retains the same actual returned resource
history, current RAM coupling and complete frame as the registered task. -/
theorem resource_exact_two {resource : Resources} {initial : State}
    (pre : ResourcePre bytes resource initial) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result ∧ result.instructions = 2 := by
  obtain ⟨result, execution, post, cost, _⟩ := exact_two pre.machine choices
  exact ⟨result, execution, post, (resource_policy pre).returned, cost⟩

/-- Model-relative optimum on useful inputs, comparing against ANY candidate
bytes and actual returning execution satisfying this same mathematical input.
Candidate initial code/ABI states may differ; both must satisfy their raw Pre. -/
theorem optimal_for_useful_input {input : Write32.Input} {initial : State}
    (pre : Write32.Pre Write32.bytes input initial) (useful : Write32.Useful input)
    (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      Write32.Post input initial result.state ∧ result.instructions = 2 ∧
      Write32.RawPolicy Write32.bytes input initial ∧
      ∀ (candidateBytes : List Byte) (candidateInitial : State)
        (candidateChoices : Choices) (candidateResult : Result),
        Write32.Pre candidateBytes input candidateInitial →
        Sequential.Executes candidateChoices candidateInitial candidateResult →
        Write32.Post input candidateInitial candidateResult.state →
        result.instructions ≤ candidateResult.instructions := by
  obtain ⟨result, execution, post, cost, policy⟩ := exact_two pre choices
  refine ⟨result, execution, post, cost, policy, ?_⟩
  intro candidateBytes candidateInitial candidateChoices candidateResult
    candidatePre candidateExecution candidatePost
  rw [cost]
  exact minimum_modeled_instructions candidatePre useful candidateExecution candidatePost

end EDSL.Grading.Write32
