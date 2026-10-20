/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.StoreReturnValue64Upper
import EDSL.Grading.StoreReturnValue64.Domain
import EDSL.StoreLoad64.Artifact
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreReturnValue64Upper
open EDSL X86 X86.Sequential OS Grading Grading.Trace Grading.StoreReturnValue64

/-- The exact seven-byte convenience profile remains a separate boundary. -/
theorem direct_checker_rejects_client : StoreLoad64.Artifact.check EDSL.StoreReturnValue64Upper.bytes = false := by decide

/-- All admitted raw executions satisfy the closed registered contract.
Six-step accounting and the initial upper-word snapshot are separate evidence. -/
theorem actual_returns {input initial choices result}
    (pre : Pre EDSL.StoreReturnValue64Upper.bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.registers .rax = input.argument ∧
      loadQWord result.state.memory input.address = .ok input.argument ∧
      result.state.rip = input.returnAddress ∧
      result.state.registers .rsp = initial.registers .rsp + 8 ∧
      (∀ register ∈ calleeSaved, result.state.registers register = initial.registers register) ∧
      result.state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask ∧
      result.instructions = 6 ∧
      result.reads = [⟨.data, input.address + 4, 4⟩, ⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 12 ∧
      ∃ upper, loadDWord initial.memory (input.address + 4) = .ok upper ∧
        result.state.registers .rdx = upper.setWidth 64 := by
  have post := AllExecutions.project (EDSL.StoreReturnValue64Upper.claim.1.machine input initial pre).1 ⟨choices, execution⟩
  exact ⟨post.result, post.value, post.returnAddress, post.stackPointer, post.preserved,
    post.flags, EDSL.StoreReturnValue64Upper.modeled_accounting pre execution⟩

/-- The returning world belongs to the SAME actual six-step lifted execution.
A second different full64 mutation retains all original loans and their bytes. -/
theorem caller_can_write_again {resource initial}
    (pre : ResourcePre EDSL.StoreReturnValue64Upper.bytes resource initial) (choices : Choices)
    (nextValue : Word) (different : nextValue ≠ resource.argument) :
    ∃ result evolved nextWorld,
      Sequential.run choices 6 initial = .ok result ∧
      result.state.registers .rax = resource.argument ∧
      loadQWord result.state.memory resource.call.targetPointer = .ok resource.argument ∧
      WordResources64.Current resource.call evolved result.state ∧
      LiftedExecutes (resourceRules resource.call) choices initial resource.seed result evolved ∧
      ReadAllowed resource.call evolved result.state ⟨.data, resource.call.targetPointer, 8⟩ ∧
      Borrowing.mutate evolved (.store64 (Threads.principal resource.call.worker)
        resource.call.ticket resource.call.targetPointer nextValue) = .ok (nextWorld, none) ∧
      loadQWord (AddressSpace.toMemory nextWorld.resources.space) resource.call.targetPointer = .ok nextValue ∧
      nextValue ≠ resource.argument ∧ nextWorld.loans = resource.seed.loans ∧
      nextWorld.resources.allocations = resource.seed.resources.allocations ∧
      (∀ query, (nextWorld.resources.space.cells query).map AddressSpace.Cell.permissions =
        (resource.seed.resources.space.cells query).map AddressSpace.Cell.permissions) ∧
      (∀ identifier loan, resource.seed.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          nextWorld.resources.space.cells query = resource.seed.resources.space.cells query) := by
  obtain ⟨result, execution, post, returned⟩ := (EDSL.StoreReturnValue64Upper.claim.1.resource resource initial pre).1 choices
  obtain ⟨evolved, lifted, current, frame, _, again⟩ := returned choices execution
  obtain ⟨nextWorld, stored⟩ := again nextValue
  have effect := Borrowing.store64_effect stored
  have loans : nextWorld.loans = resource.seed.loans := effect.loans.trans frame.loans
  have history := WordResources64.history_trans frame.history
    (Borrowing.History.next (.mutate stored) .refl)
  refine ⟨result, evolved, nextWorld,
    run_complete execution (Nat.le_of_eq (EDSL.StoreReturnValue64Upper.modeled_accounting pre.machine execution).1),
    post.result, post.value, current, lifted, (current_target_read current).1,
    stored, effect.readback, different, loans, effect.allocations.trans frame.allocations, ?_, ?_⟩
  · intro query
    exact (effect.permissions query).trans (frame.permissions query)
  · intro identifier loan live query inside
    exact (history.loan_stable pre.current.contract.wellFormed identifier
      (pre.current.contract.wellFormed.2 identifier loan live).1 loan
      ((congrFun loans identifier).trans live)).2 query inside

/-- Same low32 arguments produce distinct complete stored and returned words;
this would detect truncating either the RAX copy or the full-width store. -/
theorem high32_distinguishes_inputs (choices : Choices) :
    ∃ first second,
      Sequential.run choices 6 (EDSL.Grading.StoreReturnValue64.Domain.initial EDSL.StoreReturnValue64Upper.bytes 0x100000000) = .ok first ∧
      Sequential.run choices 6 (EDSL.Grading.StoreReturnValue64.Domain.initial EDSL.StoreReturnValue64Upper.bytes 0x200000000) = .ok second ∧
      (first.state.registers .rax).setWidth 32 = (second.state.registers .rax).setWidth 32 ∧
      first.state.registers .rax ≠ second.state.registers .rax ∧
      loadQWord first.state.memory 262144 = .ok 0x100000000 ∧
      loadQWord second.state.memory 262144 = .ok 0x200000000 := by
  have preA := EDSL.Grading.StoreReturnValue64.Domain.raw_pre EDSL.StoreReturnValue64Upper.bytes (by decide) (by decide) (argument := 0x100000000)
  have preB := EDSL.Grading.StoreReturnValue64.Domain.raw_pre EDSL.StoreReturnValue64Upper.bytes (by decide) (by decide) (argument := 0x200000000)
  obtain ⟨first, execA, postA⟩ := (EDSL.StoreReturnValue64Upper.claim.1.machine _ _ preA).1 choices
  obtain ⟨second, execB, postB⟩ := (EDSL.StoreReturnValue64Upper.claim.1.machine _ _ preB).1 choices
  have ranA := run_complete (fuel := 6) execA
    (Nat.le_of_eq (EDSL.StoreReturnValue64Upper.modeled_accounting preA execA).1)
  have ranB := run_complete (fuel := 6) execB
    (Nat.le_of_eq (EDSL.StoreReturnValue64Upper.modeled_accounting preB execB).1)
  refine ⟨first, second, ranA, ranB, ?_, ?_, postA.value, postB.value⟩
  · rw [postA.result, postB.result]
    decide
  · rw [postA.result, postB.result]
    decide

/-- An admitted actual return changes flags. The independent ABI
Post accepts it, while the stricter full-flags Post does not. -/
theorem admitted_flags_change :
    ∃ resource initial result,
      ResourcePre EDSL.StoreReturnValue64Upper.bytes resource initial ∧
      Sequential.run (fun _ => false) 6 initial = .ok result ∧
      ResourceReturn resource initial result ∧ Post (resourceInput resource) initial result.state ∧
      result.state.flags ≠ initial.flags ∧
      ¬ StoreLoad64.Post (resourceInput resource) initial result.state := by
  have pre := EDSL.Grading.StoreReturnValue64.Domain.resource_pre EDSL.StoreReturnValue64Upper.bytes (by decide) (by decide) (flags := 0x40)
  obtain ⟨result, execution, post, returned⟩ := (EDSL.StoreReturnValue64Upper.claim.1.resource _ _ pre).1 (fun _ => false)
  have changed : result.state.flags ≠ (EDSL.Grading.StoreReturnValue64.Domain.initial EDSL.StoreReturnValue64Upper.bytes (flags := 0x40)).flags := by
    rw [EDSL.StoreReturnValue64Upper.actual_flags pre.machine execution]
    change addFlags64 0x40 262144 4 ≠ (0x40 : Word)
    decide
  exact ⟨_, _, result, pre,
    run_complete execution (Nat.le_of_eq (EDSL.StoreReturnValue64Upper.modeled_accounting pre.machine execution).1),
    returned, post, changed, fun strict => changed strict.flags⟩

end EDSL.Tests.StoreReturnValue64Upper

#print axioms EDSL.StoreReturnValue64Upper.claim
#print axioms EDSL.StoreReturnValue64Upper.modeled_accounting
#print axioms EDSL.Tests.StoreReturnValue64Upper.actual_returns
#print axioms EDSL.Tests.StoreReturnValue64Upper.caller_can_write_again
#print axioms EDSL.Tests.StoreReturnValue64Upper.high32_distinguishes_inputs
#print axioms EDSL.Tests.StoreReturnValue64Upper.admitted_flags_change
#audit_edsl
