/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.Resources
import EDSL.Grading.Write32.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreReturn32Resources
open EDSL X86 X86.Sequential OS Grading.Write32 StoreReturn32

/-- Integrate the returned pointer with current owner authorization and a
second checked OS write. This catches a resource proof that loses the current
RAM world or introduces a target read loan that would block later mutation. -/
theorem caller_can_write_again {shape : Shape} {resource : Resources} {initial : State}
    (pre : ResourcePre shape.bytes resource initial) (choices : Choices) (nextValue : BitVec 32) :
    ∃ result evolved next,
      Sequential.Executes choices initial result ∧
      result.state.registers .rax = resource.call.targetPointer ∧
      loadDWord result.state.memory (result.state.registers .rax) =
        .ok (resource.argument.setWidth 32) ∧
      WordResources.Current resource.call evolved result.state ∧
      ReadAllowed resource.call evolved result.state ⟨.data, result.state.registers .rax, 4⟩ ∧
      Borrowing.mutate evolved (.store (Threads.principal resource.call.worker)
        resource.call.ticket (result.state.registers .rax) nextValue) = .ok (next, none) ∧
      loadDWord (AddressSpace.toMemory next.resources.space) (result.state.registers .rax) = .ok nextValue ∧
      next.loans = resource.seed.loans := by
  obtain ⟨result, execution, contract, returned⟩ := (StoreReturn32.resource_semantics pre).1 choices
  obtain ⟨evolved, _, current, frame⟩ := returned choices execution
  have pointer : result.state.registers .rax = resource.call.targetPointer := contract.1.pointer
  obtain ⟨next, stored⟩ := WordResources.current_store_enabled current nextValue
  have effect := Mutex.store_effect stored
  refine ⟨result, evolved, next, execution, pointer, ?_, current, ?_, ?_, ?_,
    effect.loans.trans frame.loans⟩
  · simpa only [pointer, resourceInput] using contract.1.value
  · simpa only [pointer] using (current_target_read current).1
  · simpa only [pointer] using stored
  · simpa only [pointer] using effect.readback

/-- All three exact windows have a real changing-value current-resource
admission, and complete using the original code/stack/input loans. Expected
stored value and eight-byte caller slot come from independent input data. -/
theorem admitted_store_and_return (shape : Shape) (choices : Choices) :
    ∃ resource initial result evolved,
      ResourcePre shape.bytes resource initial ∧
      Sequential.run choices 3 initial = .ok result ∧
      result.state.registers .rax = 262144 ∧
      loadDWord result.state.memory (result.state.registers .rax) = .ok 0x89abcdef ∧
      result.state.registers .rsp = 65552 ∧ result.state.rip = 8192 ∧
      result.instructions = 3 ∧ result.reads = [⟨.stack, 65544, 8⟩] ∧
      WordResources.Current resource.call evolved result.state ∧
      evolved.loans = resource.seed.loans ∧
      (∀ identifier loan, resource.seed.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = resource.seed.resources.space.cells query) := by
  let witness := Domain.candidate shape.bytes (by cases shape <;> decide) (by cases shape <;> decide)
  let resource : Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : ResourcePre shape.bytes resource witness.initial :=
    ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
      witness.raw.targetPointer, rfl, witness.raw.old⟩
  have semantics := StoreReturn32.resource_semantics pre
  obtain ⟨result, execution, contract, _⟩ := semantics.1 choices
  obtain ⟨returnedWorld, _, returnedCurrent, frame⟩ := semantics.2.returned choices execution
  refine ⟨resource, witness.initial, result, returnedWorld, pre, ?_, ?_, ?_, ?_, ?_,
    contract.2.1, ?_, returnedCurrent, frame.loans, ?_⟩
  · exact Sequential.run_complete execution (Nat.le_of_eq contract.2.1)
  · exact contract.1.pointer
  · rw [contract.1.pointer]
    simpa [resourceInput, resource, witness, Domain.candidate, Domain.initial] using contract.1.value
  · exact contract.1.stackPointer
  · exact contract.1.returnAddress
  · exact contract.2.2
  · intro identifier loan live query inside
    have below := (pre.current.contract.wellFormed.2 identifier loan live).1
    have retained : returnedWorld.loans identifier = some loan := by rw [frame.loans]; exact live
    exact (frame.history.loan_stable pre.current.contract.wellFormed identifier below loan retained).2 query inside

end EDSL.Tests.StoreReturn32Resources

#print axioms EDSL.StoreReturn32.resource_policy
#print axioms EDSL.StoreReturn32.resource_semantics
#print axioms EDSL.Tests.StoreReturn32Resources.caller_can_write_again
#print axioms EDSL.Tests.StoreReturn32Resources.admitted_store_and_return
#audit_edsl
