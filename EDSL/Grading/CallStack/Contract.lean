/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Domain
import EDSL.CallStack.Coverage
import EDSL.CallStack.Certificates

set_option warningAsError true

namespace EDSL.Grading.CallStack
open X86 OS EDSL.CallStack

/-- A witness must require a change to the incoming result register. -/
def Useful (resource : Resources) (initial : State) : Prop :=
  (initial.registers .rax).toNat ≠ resultNat resource.value

/-- The fixed resource-first task. Every choice stream must produce an actual
returning CPU/OS trace whose complete instruction encodings stay within the
selected window. Admission contains only present resources. The independent
postcondition fixes the full64 answer, ABI and memory frame, without fixing
instruction selection, call shape, execution cost or operand-read order.

The machine profile is the actual `CallReturn` relation in this theorem type.
This asserts correctness on OS-admitted worlds, not on every raw `Pre` state. -/
def SemanticClaim (program : Program) : Prop :=
  ∀ resource initial, ResourcePre program resource initial →
    ∀ choices, ∃ evolved result,
      CoveredExecution resource.frame choices resource.shared initial evolved result ∧
      Post (resourceInput resource) initial result.state

def Nonvacuous (program : Program) : Prop :=
  ∃ resource initial, ResourcePre program resource initial ∧ Useful resource initial

/-- Closed task type: neither admission nor the expected result is supplied
by the candidate certificate. -/
def Claim (program : Program) : Prop := SemanticClaim program ∧ Nonvacuous program

/-- Every arbitrary bounded byte window, including undecodable bytes, has a
useful full64 resource witness. This theorem supplies no execution premise. -/
theorem domain_nonvacuous (program : Program)
    (entry : program.entry < program.bytes.length) (bound : program.bytes.length ≤ 4096) :
    Nonvacuous program := by
  refine ⟨Domain.resource program 0xfffffffffffffffe,
    Domain.initial program 0xfffffffffffffffe,
    Domain.resource_pre program entry bound _, ?_⟩
  change (0xfedcba9876543210 : Word).toNat ≠ resultNat 0xfffffffffffffffe
  decide

/-- The returned world is the endpoint of the very same covered execution.
Its history and authority are consequences of real checked private stores. -/
structure Returned (resource : Resources) (initial : State)
    (choices : CallReturn.Choices) (evolved : StackFrame.Shared)
    (result : CallReturn.Result) : Prop where
  covered : CoveredExecution resource.frame choices resource.shared initial evolved result
  current : StackFrame.Current resource.frame evolved result.state
  privateHistory : StackFrame.PrivateHistory resource.frame resource.shared evolved
  preservation : StackFrame.Preservation resource.frame resource.shared evolved
  post : Post (resourceInput resource) initial result.state

theorem Returned.of_covered {program resource initial choices evolved result}
    (pre : ResourcePre program resource initial)
    (covered : CoveredExecution resource.frame choices resource.shared initial evolved result)
    (post : Post (resourceInput resource) initial result.state) :
    Returned resource initial choices evolved result :=
  ⟨covered, covered.current pre.current, covered.privateHistory, covered.preserves, post⟩

/-- Every contained slot still has actual current owner/epoch and whole-word
permissions at the returned endpoint. -/
theorem Returned.currentRW {resource initial choices evolved result}
    (returned : Returned resource initial choices evolved result) {address : Word}
    (slot : StackFrame.Slot resource.frame address) :
    WordResources64.WordValid evolved resource.frame.owner resource.frame.ticket address :=
  returned.current.contract.currentRW slot

/-- The returned allocation is reusable for any full64 value. This derives
a real successful OS mutation, readback and a current coupled successor;
the original live loans retain their cells. It is not an admission callback. -/
theorem Returned.store64 {resource initial choices evolved result}
    (returned : Returned resource initial choices evolved result) {address : Word}
    (slot : StackFrame.Slot resource.frame address) (value : Word) :
    ∃ next, Borrowing.mutate evolved
        (.store64 resource.frame.owner resource.frame.ticket address value) = .ok (next, none) ∧
      StackFrame.Current resource.frame next (StackFrame.recouple result.state next) ∧
      Borrowing.StoreEffect64 evolved next address value ∧
      Borrowing.loadOwnedWord64 next resource.frame.owner resource.frame.ticket address = .ok value ∧
      readWord (StackFrame.recouple result.state next).memory address = .ok value ∧
      (∀ identifier loan, evolved.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          next.resources.space.cells query = evolved.resources.space.cells query) :=
  StackFrame.current_store64 returned.current slot value

/-- Every choice stream has a successful concrete run. Fuel is derived from
the actual returning trace and is not a task/admission parameter. -/
theorem SemanticClaim.run {program} (claim : SemanticClaim program)
    {resource initial} (pre : ResourcePre program resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved result, CallReturn.run choices result.instructions initial = .ok result ∧
      Returned resource initial choices evolved result := by
  obtain ⟨evolved, result, covered, post⟩ := claim resource initial pre choices
  have machine : CallReturn.Executes choices initial result := by
    simpa only [CallReturn.Executes, pre.stack] using covered.machine
  exact ⟨evolved, result, CallReturn.run_complete machine (Nat.le_refl _),
    Returned.of_covered pre covered post⟩

/-- Fixed-choice determinism identifies every actual returning result with
the certified result, including its reads and cost as well as its CPU state. -/
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

/-- Soundness for any successful actual run, with arbitrary supplied fuel.
The returned OS authority is coupled to that actual result's memory. -/
theorem SemanticClaim.actual {program} (claim : SemanticClaim program)
    {resource initial choices fuel result} (pre : ResourcePre program resource initial)
    (actual : CallReturn.run choices fuel initial = .ok result) :
    ∃ evolved, Returned resource initial choices evolved result :=
  claim.all_results pre (CallReturn.run_sound actual)

theorem Claim.run {program} (claim : Claim program)
    {resource initial} (pre : ResourcePre program resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved result, CallReturn.run choices result.instructions initial = .ok result ∧
      Returned resource initial choices evolved result := claim.1.run pre choices

theorem Claim.all_results {program} (claim : Claim program)
    {resource initial choices result} (pre : ResourcePre program resource initial)
    (actual : CallReturn.Executes choices initial result) :
    ∃ evolved, Returned resource initial choices evolved result := claim.1.all_results pre actual

theorem Claim.actual {program} (claim : Claim program)
    {resource initial choices fuel result} (pre : ResourcePre program resource initial)
    (actual : CallReturn.run choices fuel initial = .ok result) :
    ∃ evolved, Returned resource initial choices evolved result := claim.1.actual pre actual

end EDSL.Grading.CallStack
