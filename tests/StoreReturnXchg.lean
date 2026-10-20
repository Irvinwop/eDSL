/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.StoreReturnXchg
import EDSL.StoreReturn32.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreReturnXchg
open EDSL X86 X86.Sequential OS Grading Grading.Write32

/-- A fresh compiler proof is accepted by the registered task while the
unchanged convenience adapter deliberately keeps its three known shapes. -/
theorem direct_checker_rejects_client : StoreReturn32.check EDSL.StoreReturnXchg.bytes = none := by decide

/-- The same actual execution satisfies the independent store/pointer Post,
three-step accounting, and the second half of the exchange on volatile RDI. -/
theorem actual_returns {input initial choices result}
    (pre : Pre EDSL.StoreReturnXchg.bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.registers .rax = input.address ∧
      loadDWord result.state.memory input.address = .ok (input.argument.setWidth 32) ∧
      result.instructions = 3 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 8 ∧ result.state.registers .rdi = initial.registers .rax := by
  have post := AllExecutions.project
    (EDSL.StoreReturnXchg.claim.1.machine input initial pre).1 ⟨choices, execution⟩
  exact ⟨post.pointer, post.value, EDSL.StoreReturnXchg.modeled_accounting pre execution⟩

/-- Current owner authority survives the actual XCHG/store/RET execution,
allowing a second checked write through its returned pointer without a new loan. -/
theorem caller_can_write_again {resource : Resources} {initial : State}
    (pre : ResourcePre EDSL.StoreReturnXchg.bytes resource initial)
    (choices : Choices) (nextValue : BitVec 32) :
    ∃ result evolved next,
      Sequential.run choices 3 initial = .ok result ∧
      result.state.registers .rax = resource.call.targetPointer ∧
      loadDWord result.state.memory (result.state.registers .rax) = .ok (resource.argument.setWidth 32) ∧
      WordResources.Current resource.call evolved result.state ∧
      ReadAllowed resource.call evolved result.state ⟨.data, result.state.registers .rax, 4⟩ ∧
      Borrowing.mutate evolved (.store (Threads.principal resource.call.worker)
        resource.call.ticket (result.state.registers .rax) nextValue) = .ok (next, none) ∧
      loadDWord (AddressSpace.toMemory next.resources.space) (result.state.registers .rax) = .ok nextValue ∧
      next.loans = resource.seed.loans := by
  obtain ⟨result, execution, post, returned⟩ :=
    (EDSL.StoreReturnXchg.claim.1.resource resource initial pre).1 choices
  obtain ⟨evolved, _, current, frame⟩ := returned choices execution
  have pointer : result.state.registers .rax = resource.call.targetPointer := post.pointer
  obtain ⟨next, stored⟩ := WordResources.current_store_enabled current nextValue
  have effect := Mutex.store_effect stored
  have accounting := EDSL.StoreReturnXchg.modeled_accounting pre.machine execution
  refine ⟨result, evolved, next, run_complete execution (Nat.le_of_eq accounting.1), pointer,
    ?_, current, ?_, ?_, ?_, effect.loans.trans frame.loans⟩
  · simpa only [pointer, registered, storeReturnTask, resourceInput] using post.value
  · simpa only [pointer] using (current_target_read current).1
  · simpa only [pointer] using stored
  · simpa only [pointer] using effect.readback

end EDSL.Tests.StoreReturnXchg

#print axioms EDSL.StoreReturnXchg.claim
#print axioms EDSL.StoreReturnXchg.modeled_accounting
#print axioms EDSL.StoreReturnXchg.minimum_attained
#print axioms EDSL.Tests.StoreReturnXchg.actual_returns
#print axioms EDSL.Tests.StoreReturnXchg.caller_can_write_again
#audit_edsl
