/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreDirect64
import tests.fixtures.CountedStoreFinal64.Accounting
import EDSL.CountedStore64.Domain
import EDSL.CountedStore64.Artifact
import EDSL.CountedStore64.Clang.Artifact
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CountedStoreDirect64
open EDSL X86 X86.Sequential CountedStore64 EDSL.CountedStoreDirect64

private def observe (variant : Variant) (argument count : Word) (fuel : Nat) (af : Bool) :
    Except Error (Nat × Word × Except Error Word × Word × Word × List Read) := do
  let result ← Sequential.run (fun _ => af) fuel (Domain.initial (bytes variant) argument count)
  return (result.instructions,result.state.registers .rax,loadQWord result.state.memory 262144,
    result.state.rip,result.state.registers .rsp,result.reads)

/-- The actual evaluator uses the complete count, not its low32 bits. Literal
expected values also check RET, stack adjustment and its unique operand read. -/
theorem high_count (af : Bool) :
    (observe .gcc 0 0x100000000 5 af,observe .clang 0 0x100000000 6 af) =
    (.ok (5,0x100000000,.ok 0x100000000,8192,65552,[⟨.stack,65544,8⟩]),
      .ok (6,0x100000000,.ok 0x100000000,8192,65552,[⟨.stack,65544,8⟩])) := by
  cases af <;> rfl

theorem maximum_count (af : Bool) :
    (observe .gcc 1 0xffffffffffffffff 5 af,observe .clang 1 0xffffffffffffffff 6 af) =
    (.ok (5,0,.ok 0,8192,65552,[⟨.stack,65544,8⟩]),
      .ok (6,0,.ok 0,8192,65552,[⟨.stack,65544,8⟩])) := by
  cases af <;> rfl

theorem zero_retains_target (af : Bool) :
    (observe .gcc 0xfeedface89abcdef 0 4 af,observe .clang 0xfeedface89abcdef 0 5 af) =
    (.ok (4,0xfeedface89abcdef,.ok 0,8192,65552,[⟨.stack,65544,8⟩]),
      .ok (5,0xfeedface89abcdef,.ok 0,8192,65552,[⟨.stack,65544,8⟩])) := by
  cases af <;> rfl

/-- The actual evaluator must still execute RET. A positive GCC input needs
five instructions and Clang needs six, even when the result wraps to zero. -/
theorem fuel_short :
    Sequential.run (fun _ => false) 4 (Domain.initial (bytes .gcc) 1 0xffffffffffffffff) =
      .error .exhaustedFuel ∧
    Sequential.run (fun _ => false) 5 (Domain.initial (bytes .clang) 1 0xffffffffffffffff) =
      .error .exhaustedFuel := by constructor <;> rfl

/-- Returned authority belongs to the same actual evolved world and permits
another arbitrary store. Loan and allocation identities survive both writes. -/
theorem store_again {variant resource initial} (pre : ResourcePre (bytes variant) resource initial)
    (choices : Choices) (nextValue : Word) :
    ∃ result evolved nextWorld,
      Sequential.Executes choices initial result ∧
      OS.WordResources64.Current resource.memory.call evolved result.state ∧
      Grading.Trace.LiftedExecutes
        (Grading.StoreReturnValue64.resourceRules resource.memory.call)
        choices initial resource.memory.seed result evolved ∧
      OS.Borrowing.mutate evolved (.store64 (OS.Threads.principal resource.memory.call.worker)
        resource.memory.call.ticket resource.memory.call.targetPointer nextValue) = .ok (nextWorld,none) ∧
      loadQWord (OS.AddressSpace.toMemory nextWorld.resources.space)
        resource.memory.call.targetPointer = .ok nextValue ∧
      nextWorld.resources.allocations = resource.memory.seed.resources.allocations ∧
      nextWorld.loans = resource.memory.seed.loans := by
  obtain ⟨result,actual,_,returned,_,_⟩ := (resource_semantics pre).1 choices
  obtain ⟨evolved,lifted,current,frame,_,again⟩ := returned choices actual
  obtain ⟨nextWorld,checked⟩ := again nextValue
  have effect := OS.Borrowing.store64_effect checked
  exact ⟨result,evolved,nextWorld,actual,current,lifted,checked,effect.readback,
    effect.allocations.trans frame.allocations,effect.loans.trans frame.loans⟩

/-- A concrete comparison within the same independent task. These equations
do not bound other instruction sets, source effects, cycles or global optima. -/
theorem concrete_costs (count : Word) :
    cost .clang count = cost .gcc count + 1 ∧
      cost .gcc count ≤ CountedStoreFinal64.cost count.toNat ∧
      (count ≠ 0 → cost .clang count < CountedStoreFinal64.cost count.toNat) := by
  by_cases zero : count = 0
  · subst count
    simp [cost,prefixCost,CountedStoreFinal64.cost]
  · have positive := BitVec.toNat_pos_of_ne_zero zero
    simp only [cost,prefixCost,zero,ite_false]
    have natural : count.toNat ≠ 0 := by omega
    simp only [CountedStoreFinal64.cost,natural,ite_false]
    exact ⟨True.intro,by omega,fun _ => by omega⟩

example (variant : Variant) :
    Artifact.check (bytes variant) = false ∧ Clang.Artifact.check (bytes variant) = false := by
  cases variant <;> decide

private def wrongIndex : List Byte :=
  [0x48,0x8d,0x04,0x36,0x48,0x85,0xd2,0x74,0x03,0x48,0x89,0x07,0xc3]
private def wrongInitial := Domain.initial wrongIndex 0 1
private def wrongBefore := atPC (test
  { wrongInitial.writeRegister .rax 0 with rip := wrongInitial.rip + 4 } false)
  (wrongInitial.rip + 9)
private def wrongResult : Result :=
  ⟨finish (store wrongBefore) 8192,
    5,[⟨.stack,65544,8⟩]⟩

/-- A fully supported synthetic LEA uses RSI twice instead of the count.
It returns normally from an admitted world; the independent result rejects it. -/
theorem wrong_index_fails_result :
    ResourcePre wrongIndex (Domain.resource wrongIndex 0 1) wrongInitial ∧
      ¬AllExecutions wrongInitial
        (fun result => Post (resourceInput (Domain.resource wrongIndex 0 1)) wrongInitial result.state) := by
  refine ⟨Domain.resource_pre wrongIndex (by decide) (by decide) 0 1,?_⟩
  intro correct
  have actual : Sequential.run (fun _ => false) 5 wrongInitial = .ok wrongResult := by rfl
  have wrong := (correct.project ⟨_,run_sound actual⟩).result
  change (0 : Word) = 1 at wrong
  exact (by decide : (0 : Word) ≠ 1) wrong

private def missingStore : List Byte :=
  [0x48,0x8d,0x04,0x16,0x48,0x85,0xd2,0x74,0x03,0x48,0x8d,0x00,0xc3]
private def missingInitial := Domain.initial missingStore 0 1
private def missingResult : Result :=
  ⟨finish { (atStore .gcc missingInitial false).writeRegister .rax
      ((atStore .gcc missingInitial false).registers .rax) with rip := missingInitial.rip + 12 } 8192,
    5,[⟨.stack,65544,8⟩]⟩

/-- A supported LEA identity replaces the store. RAX is correct, but returning
without publishing the result violates the independent eight-byte contract. -/
theorem missing_store_fails_memory :
    ResourcePre missingStore (Domain.resource missingStore 0 1) missingInitial ∧
      ¬AllExecutions missingInitial
        (fun result => Post (resourceInput (Domain.resource missingStore 0 1)) missingInitial result.state) := by
  refine ⟨Domain.resource_pre missingStore (by decide) (by decide) 0 1,?_⟩
  intro correct
  have actual : Sequential.run (fun _ => false) 5 missingInitial = .ok missingResult := by rfl
  have wrong := (correct.project ⟨_,run_sound actual⟩).value
  change (Except.ok (0 : Word) : Except Error Word) = .ok 1 at wrong
  exact (by decide : (0 : Word) ≠ 1) (Except.ok.inj wrong)

end EDSL.Tests.CountedStoreDirect64

#print axioms EDSL.Grading.StoreReturnValue64.StackPolicy.resources
#print axioms EDSL.CountedStoreDirect64.gccClaim
#print axioms EDSL.CountedStoreDirect64.clangClaim
#print axioms EDSL.Tests.CountedStoreDirect64.maximum_count
#print axioms EDSL.Tests.CountedStoreDirect64.store_again
#print axioms EDSL.Tests.CountedStoreDirect64.wrong_index_fails_result
#print axioms EDSL.Tests.CountedStoreDirect64.missing_store_fails_memory
#audit_edsl
