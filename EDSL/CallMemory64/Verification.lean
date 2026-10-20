/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Contract
import EDSL.OS.CallMemory64.Coverage

set_option warningAsError true

namespace EDSL.CallMemory64
open X86 OS

/-- A useful witness requires changes to both caller-visible results. -/
def Useful (resource : Resources) (initial : State) : Prop :=
  (initial.registers .rax).toNat ≠ resultNat resource.value ∧
    readWord initial.memory resource.descriptor.target ≠ .ok resource.value

/-- Fixed independent functional and resource contract. Present admission is
separate from the actual covered CPU/OS trace required for every AF stream.
Neither instruction selection, access order nor cost is an acceptance rule. -/
def SemanticClaim (program : Program) : Prop :=
  ∀ resource initial, ResourcePre program resource initial →
    ∀ choices, ∃ evolved result,
      OS.CallMemory64.CoveredExecution resource.descriptor choices
        resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state

def Nonvacuous (program : Program) : Prop :=
  ∃ resource initial, ResourcePre program resource initial ∧ Useful resource initial

def Claim (program : Program) : Prop := SemanticClaim program ∧ Nonvacuous program

/-- The result retains the endpoint and history of its actual execution.
Private stores and DATA stores share one evolved, fully coupled world. -/
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

/-- The functional postcondition is observed through the same current owner
handle in the actual endpoint world; no target read loan is manufactured. -/
theorem Returned.target_read {resource initial choices evolved result}
    (returned : Returned resource initial choices evolved result) :
    Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
      resource.descriptor.target = .ok resource.value := by
  obtain ⟨value, owned, observed, _⟩ := returned.current.contract.data_read
  have actual : readWord result.state.memory resource.descriptor.target = .ok value := by
    rw [returned.current.coupled]
    exact observed
  have same : value = resource.value := Except.ok.inj (actual.symm.trans returned.post.stored)
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

/-- Determinism relates every actual returning run to the same certified
current endpoint, including its entire result, read list and cost. -/
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

end EDSL.CallMemory64
