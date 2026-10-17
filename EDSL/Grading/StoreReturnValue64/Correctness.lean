/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.StoreReturnValue64.Resources

set_option warningAsError true

namespace EDSL.Grading.StoreReturnValue64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading.Trace

/-- Independent policy evidence for the existing seven-byte binary. The
functional result theorem alone does not establish its prefix obligations. -/
theorem raw_policy {input initial} (pre : Pre EDSL.StoreLoad64.bytes input initial) :
    RawPolicy EDSL.StoreLoad64.bytes input initial := by
  refine ⟨(fun _ before => before = initial ∨ before = EDSL.StoreLoad64.stageOne initial ∨
    before = EDSL.StoreLoad64.stageTwo initial), Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same | same
  · subst before
    refine ⟨True.intro, .storeMem64 (.base .rdi) .rsi, EDSL.StoreLoad64.first_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (EDSL.StoreLoad64.stageOne initial), []⟩, (),
      EDSL.StoreLoad64.first_step pre af, ?_,
      ⟨EDSL.StoreLoad64.fetch_at pre 0 (by simp) (by decide), .store64 (value := input.argument) ?_⟩,
      Or.inr (Or.inl rfl)⟩
    · simp
    · simp [Sequential.Instruction.storeIntent64, Address.eval, pre.pointer, pre.source]
  · subst before
    refine ⟨True.intro, .loadMem64 .rax (.base .rdi), EDSL.StoreLoad64.second_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (EDSL.StoreLoad64.stageTwo initial), [⟨.data, input.address, 8⟩]⟩, (),
      EDSL.StoreLoad64.second_step pre af, ?_,
      ⟨EDSL.StoreLoad64.fetch_at pre 3 rfl (by decide), .readOnly rfl⟩,
      Or.inr (Or.inr rfl)⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    exact ⟨Or.inr rfl, input.argument, EDSL.StoreLoad64.stageOne_value pre⟩
  · subst before
    refine ⟨True.intro, .legacy .ret, EDSL.StoreLoad64.ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (EDSL.StoreLoad64.finalState initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), EDSL.StoreLoad64.ret_step pre af, ?_,
      ⟨EDSL.StoreLoad64.fetch_at pre 6 rfl (by decide), .readOnly rfl⟩, True.intro⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    refine ⟨⟨rfl, rfl⟩, rfl, input.returnAddress, ?_⟩
    simpa [EDSL.StoreLoad64.stageTwo, EDSL.StoreLoad64.stageOne, State.writeRegister] using
      EDSL.StoreLoad64.stageTwo_stack pre

/-- Full64 functional correctness projects from the strict binary proof;
the independent broader raw policy is additional evidence. -/
theorem raw_semantics {input initial} (pre : Pre EDSL.StoreLoad64.bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state) ∧
      RawPolicy EDSL.StoreLoad64.bytes input initial := by
  refine ⟨?_, raw_policy pre⟩
  intro choices
  obtain ⟨result, execution, post⟩ := EDSL.StoreLoad64.raw_semantics pre choices
  exact ⟨result, execution, post_of_strict post.1⟩

theorem resource_policy {resource initial} (pre : ResourcePre EDSL.StoreLoad64.bytes resource initial) :
    ResourcePolicy resource initial :=
  resourcePolicy_of_strict (EDSL.StoreLoad64.resource_policy pre)

/-- The new return predicate uses its own real lifted history under broader
span rules, while functional correctness drops the strict count/read gates. -/
theorem resource_semantics {resource initial} (pre : ResourcePre EDSL.StoreLoad64.bytes resource initial) :
    AllExecutions initial (fun result =>
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result) ∧
      ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, ResourcePolicy.returned pre policy⟩

end EDSL.Grading.StoreReturnValue64
