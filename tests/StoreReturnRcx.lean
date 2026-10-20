/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.StoreReturnRcx
import EDSL.StoreReturn32.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreReturnRcx
open EDSL X86 X86.Sequential OS Grading Grading.Write32

/-- The independently registered task accepts a proved client even though
its longer RCX implementation is outside every direct-adapter shape. -/
theorem direct_checker_rejects_client : StoreReturn32.check EDSL.StoreReturnRcx.bytes = none := by decide

/-- Every actual returned result meets the independent contract through the
closed registered Claim. Its four-step accounting remains separate evidence,
so registration cannot accidentally impose the direct adapter's three steps. -/
theorem actual_returns {input initial choices result}
    (pre : Pre EDSL.StoreReturnRcx.bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.registers .rax = input.address ∧
      loadDWord result.state.memory input.address = .ok (input.argument.setWidth 32) ∧
      result.instructions = 4 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 8 := by
  have post := AllExecutions.project
    (EDSL.StoreReturnRcx.claim.1.machine input initial pre).1 ⟨choices, execution⟩
  exact ⟨post.pointer, post.value, EDSL.StoreReturnRcx.modeled_accounting pre execution⟩

/-- The actual lifted client return leaves its returned pointer readable by
current owner authority, and usable for a second checked mutation. This catches
loss of evolved RAM coupling or a new target loan that would block mutation. -/
theorem caller_can_write_again {resource : Resources} {initial : State}
    (pre : ResourcePre EDSL.StoreReturnRcx.bytes resource initial)
    (choices : Choices) (nextValue : BitVec 32) :
    ∃ result evolved next,
      Sequential.run choices 4 initial = .ok result ∧
      result.state.registers .rax = resource.call.targetPointer ∧
      loadDWord result.state.memory (result.state.registers .rax) = .ok (resource.argument.setWidth 32) ∧
      WordResources.Current resource.call evolved result.state ∧
      ReadAllowed resource.call evolved result.state ⟨.data, result.state.registers .rax, 4⟩ ∧
      Borrowing.mutate evolved (.store (Threads.principal resource.call.worker)
        resource.call.ticket (result.state.registers .rax) nextValue) = .ok (next, none) ∧
      loadDWord (AddressSpace.toMemory next.resources.space) (result.state.registers .rax) = .ok nextValue ∧
      next.loans = resource.seed.loans := by
  obtain ⟨result, execution, post, returned⟩ :=
    (EDSL.StoreReturnRcx.claim.1.resource resource initial pre).1 choices
  obtain ⟨evolved, _, current, frame⟩ := returned choices execution
  have pointer : result.state.registers .rax = resource.call.targetPointer := post.pointer
  obtain ⟨next, stored⟩ := WordResources.current_store_enabled current nextValue
  have effect := Mutex.store_effect stored
  have accounting := EDSL.StoreReturnRcx.modeled_accounting pre.machine execution
  refine ⟨result, evolved, next, run_complete execution (Nat.le_of_eq accounting.1), pointer,
    ?_, current, ?_, ?_, ?_, effect.loans.trans frame.loans⟩
  · simpa only [pointer, registered, storeReturnTask, resourceInput] using post.value
  · simpa only [pointer] using (current_target_read current).1
  · simpa only [pointer] using stored
  · simpa only [pointer] using effect.readback

end EDSL.Tests.StoreReturnRcx

#print axioms EDSL.StoreReturnRcx.claim
#print axioms EDSL.StoreReturnRcx.modeled_accounting
#print axioms EDSL.Tests.StoreReturnRcx.actual_returns
#print axioms EDSL.Tests.StoreReturnRcx.caller_can_write_again
#audit_edsl
