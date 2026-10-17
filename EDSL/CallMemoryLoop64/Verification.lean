/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemoryLoop64.Contract
import EDSL.OS.CallMemory64.Coverage

set_option warningAsError true

namespace EDSL.CallMemoryLoop64
open X86 OS

/-- Nonvacuity witnesses a nonzero count requiring both observable outputs to
change. The universally quantified admission itself still includes zero. -/
def Useful (resource : Resources) (initial : State) : Prop :=
  (initial.registers .rax).toNat ≠ resultNat resource.value resource.count ∧
    resource.count ≠ 0 ∧
    readWord initial.memory resource.descriptor.target ≠
      .ok (targetWord resource.value resource.count)

/-- Every current admitted input must have an actual returning, fully covered
mixed CPU/OS execution, with the independent arithmetic and frame contract.
The candidate cannot replace this with a graph evaluator or a future-run premise. -/
def SemanticClaim (program : Program) : Prop :=
  ∀ resource initial, ResourcePre program resource initial →
    ∀ choices, ∃ evolved result,
      OS.CallMemory64.CoveredExecution resource.descriptor choices
        resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state

def Nonvacuous (program : Program) : Prop :=
  ∃ resource initial, ResourcePre program resource initial ∧ Useful resource initial

def Claim (program : Program) : Prop := SemanticClaim program ∧ Nonvacuous program

structure Returned (resource : Resources) (initial : State) (choices : CallReturn.Choices)
    (evolved : Borrowing.State) (result : CallReturn.Result) : Prop where
  covered : OS.CallMemory64.CoveredExecution resource.descriptor choices
    resource.shared initial evolved result
  current : OS.CallMemory64.Current resource.descriptor evolved result.state
  history : OS.CallMemory64.History resource.descriptor resource.shared evolved
  preservation : OS.CallMemory64.Preservation resource.descriptor resource.shared evolved
  post : Post (resourceInput resource) initial result.state

theorem Returned.of_covered {program resource initial choices evolved result}
    (pre : ResourcePre program resource initial)
    (covered : OS.CallMemory64.CoveredExecution resource.descriptor choices
      resource.shared initial evolved result)
    (post : Post (resourceInput resource) initial result.state) :
    Returned resource initial choices evolved result :=
  ⟨covered, covered.current pre.current, covered.mixedHistory, covered.preserves, post⟩

/-- The nonzero final word is loaded through its actual current owner ticket
in the endpoint world used by the same machine execution. -/
theorem Returned.target_read_nonzero {resource initial choices evolved result}
    (returned : Returned resource initial choices evolved result) (count : resource.count ≠ 0) :
    Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
      resource.descriptor.target = .ok (targetWord resource.value resource.count) := by
  obtain ⟨value, owned, observed, _⟩ := returned.current.contract.data_read
  have actual : readWord result.state.memory resource.descriptor.target = .ok value := by
    rw [returned.current.coupled]
    exact observed
  have stored := returned.post.stored
  simp only [resourceInput, CallMemory64.resourceInput, count, ↓reduceIte] at stored
  have same := Except.ok.inj (actual.symm.trans stored)
  simpa only [same] using owned

/-- Zero count retains the independently observed initial target word through
current authority too; it does not manufacture a new target read loan. -/
theorem Returned.target_read_zero {resource initial choices evolved result old}
    (returned : Returned resource initial choices evolved result) (count : resource.count = 0)
    (before : readWord initial.memory resource.descriptor.target = .ok old) :
    Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
      resource.descriptor.target = .ok old := by
  obtain ⟨value, owned, observed, _⟩ := returned.current.contract.data_read
  have actual : readWord result.state.memory resource.descriptor.target = .ok value := by
    rw [returned.current.coupled]
    exact observed
  have stored := returned.post.stored
  simp only [resourceInput, CallMemory64.resourceInput, count, ↓reduceIte, before] at stored
  have same := Except.ok.inj (actual.symm.trans stored)
  simpa only [same] using owned

theorem SemanticClaim.run {program} (claim : SemanticClaim program)
    {resource initial} (pre : ResourcePre program resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result, CallReturn.run choices result.instructions initial = .ok result ∧
      Returned resource initial choices evolved result := by
  obtain ⟨evolved, result, covered, post⟩ := claim resource initial pre choices
  have machine : CallReturn.Executes choices initial result := by
    simpa only [CallReturn.Executes, pre.stack] using covered.machine
  exact ⟨evolved, result, CallReturn.run_complete machine (Nat.le_refl _),
    Returned.of_covered pre covered post⟩

theorem SemanticClaim.all_results {program} (claim : SemanticClaim program)
    {resource initial choices result} (pre : ResourcePre program resource initial)
    (actual : CallReturn.Executes choices initial result) :
    ∃ evolved, Returned resource initial choices evolved result := by
  obtain ⟨evolved, expected, covered, post⟩ := claim resource initial pre choices
  have machine : CallReturn.Executes choices initial expected := by
    simpa only [CallReturn.Executes, pre.stack] using covered.machine
  have same := CallReturn.ExecutesFrom.fixed_choices_unique machine actual
  subst expected
  exact ⟨evolved, Returned.of_covered pre covered post⟩

theorem SemanticClaim.actual {program} (claim : SemanticClaim program)
    {resource initial choices fuel result} (pre : ResourcePre program resource initial)
    (actual : CallReturn.run choices fuel initial = .ok result) :
    ∃ evolved, Returned resource initial choices evolved result :=
  claim.all_results pre (CallReturn.run_sound actual)

theorem Claim.run {program} (claim : Claim program)
    {resource initial} (pre : ResourcePre program resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result, CallReturn.run choices result.instructions initial = .ok result ∧
      Returned resource initial choices evolved result := claim.1.run pre choices

end EDSL.CallMemoryLoop64
