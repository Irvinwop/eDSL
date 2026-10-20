/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreFinal64
import EDSL.CountedStore64.Domain
import EDSL.CountedStore64.Artifact
import EDSL.CountedStore64.Clang.Artifact
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CountedStoreFinal64
open EDSL X86 X86.Sequential CountedStore64
open EDSL.CountedStoreFinal64

/-- The zero-count branch preserves arbitrary old contents and returns the
initial full-width value for every admitted state and every AF stream. -/
theorem zero_keeps_old {input initial} (pre : Pre bytes input initial)
    (zero : input.count = 0) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      result.instructions = 4 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      result.state.registers .rax = input.argument ∧
      loadQWord result.state.memory input.address = .ok input.oldValue := by
  obtain ⟨result, actual, post, _⟩ := raw_semantics pre choices
  obtain ⟨exactCost, reads⟩ := execution_exact pre actual
  refine ⟨result, actual, ?_, reads, ?_, ?_⟩
  · simpa [cost, zero] using exactCost
  · simpa [zero] using post.result
  · simpa [expectedValue, zero] using post.value

/-- Counts with no low32 bits contribute fully, independently of any finite
native workload. The return retains usable authority over the same OS world. -/
theorem high_count (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial bytes 0 0x100000000) result ∧
      result.instructions = 12884901893 ∧
      result.state.registers .rax = 0x100000000 ∧
      loadQWord result.state.memory 262144 = .ok 0x100000000 ∧
      ResourceReturn (Domain.resource bytes 0 0x100000000)
        (Domain.initial bytes 0 0x100000000) result := by
  have pre := Domain.resource_pre bytes (by decide) (by decide) 0 0x100000000
  obtain ⟨result, actual, post, returned, exactCost, _, _⟩ := resource_exact pre choices
  exact ⟨result, actual, exactCost, post.result, post.value, returned⟩

/-- Maximum counts terminate and wrap only the mathematical word result. -/
theorem maximum_count (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial bytes 1 0xffffffffffffffff) result ∧
      result.instructions = 55340232221128654850 ∧
      result.state.registers .rax = 0 ∧ loadQWord result.state.memory 262144 = .ok 0 ∧
      ResourceReturn (Domain.resource bytes 1 0xffffffffffffffff)
        (Domain.initial bytes 1 0xffffffffffffffff) result := by
  have pre := Domain.resource_pre bytes (by decide) (by decide) 1 0xffffffffffffffff
  obtain ⟨result, actual, post, returned, exactCost, _, _⟩ := resource_exact pre choices
  exact ⟨result, actual, exactCost, post.result, post.value, returned⟩

/-- The final STORE is required before RET; seven instructions cannot return
from the admitted one-iteration call. -/
theorem one_fuel_short :
    ResourcePre bytes (Domain.resource bytes 0 1) (Domain.initial bytes 0 1) ∧
      Sequential.run (fun _ => false) 7 (Domain.initial bytes 0 1) = .error .exhaustedFuel :=
  ⟨Domain.resource_pre bytes (by decide) (by decide) 0 1, by rfl⟩

/-- The returned ownership and loans support a further arbitrary checked64
mutation, coupled to the same evolved RAM as the actual execution. -/
theorem store_again {resource initial} (pre : ResourcePre bytes resource initial)
    (choices : Choices) (nextValue : Word) :
    ∃ result evolved nextWorld,
      Sequential.Executes choices initial result ∧
      OS.WordResources64.Current resource.memory.call evolved result.state ∧
      Grading.Trace.LiftedExecutes
        (Grading.StoreReturnValue64.resourceRules resource.memory.call)
        choices initial resource.memory.seed result evolved ∧
      OS.Borrowing.mutate evolved (.store64 (OS.Threads.principal resource.memory.call.worker)
        resource.memory.call.ticket resource.memory.call.targetPointer nextValue) = .ok (nextWorld, none) ∧
      loadQWord (OS.AddressSpace.toMemory nextWorld.resources.space)
        resource.memory.call.targetPointer = .ok nextValue ∧
      nextWorld.resources.allocations = resource.memory.seed.resources.allocations ∧
      nextWorld.loans = resource.memory.seed.loans := by
  obtain ⟨result, actual, _, returned, _⟩ := (resource_semantics pre).1 choices
  obtain ⟨evolved, lifted, current, frame, _, again⟩ := returned choices actual
  obtain ⟨nextWorld, checked⟩ := again nextValue
  have effect := OS.Borrowing.store64_effect checked
  exact ⟨result, evolved, nextWorld, actual, current, lifted, checked, effect.readback,
    effect.allocations.trans frame.allocations, effect.loans.trans frame.loans⟩

/-- The generic task is broader than either convenience profile. -/
example : Artifact.check bytes = false ∧ Clang.Artifact.check bytes = false := by decide

private def inverted : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x85, 0xd2, 0x74, 0x0b,
  0x48, 0xff, 0xc0, 0x48, 0xff, 0xca, 0x74, 0xf8, 0x48, 0x89, 0x07, 0xc3]
private def invertedInitial := Domain.initial inverted 0 2
private def invertedResult : Result :=
  ⟨finish (storedState invertedInitial.rip
      (body invertedInitial.rip (move invertedInitial) false)) 8192,
    8, [⟨.stack, 65544, 8⟩]⟩

/-- Supported JZ-for-JNZ code is admitted but stores the wrong result after
one iteration when two were required. Rejection is a semantic counterexample. -/
theorem inverted_branch_fails_result :
    ResourcePre inverted (Domain.resource inverted 0 2) invertedInitial ∧
      ¬AllExecutions invertedInitial
        (fun result => Post (resourceInput (Domain.resource inverted 0 2)) invertedInitial result.state) := by
  refine ⟨Domain.resource_pre inverted (by decide) (by decide) 0 2, ?_⟩
  intro claim
  have actual : Sequential.run (fun _ => false) 8 invertedInitial = .ok invertedResult := by rfl
  have wrong := (claim.project ⟨_, run_sound actual⟩).result
  change (1 : Word) = 2 at wrong
  exact (by decide : (1 : Word) ≠ 2) wrong

private def missingStore : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x85, 0xd2, 0x74, 0x0b,
  0x48, 0xff, 0xc0, 0x48, 0xff, 0xca, 0x75, 0xf8, 0x48, 0x89, 0xc0, 0xc3]
private def missingInitial := Domain.initial missingStore 0 1
private def beforeMissing := toStore missingInitial.rip
  (body missingInitial.rip (move missingInitial) false)
private def missingResult : Result :=
  ⟨finish { beforeMissing.writeRegister .rax (beforeMissing.registers .rax) with
      rip := beforeMissing.rip + 3 } 8192,
    8, [⟨.stack, 65544, 8⟩]⟩

/-- Replacing the final store by a supported register move still returns the
right RAX. The independent memory postcondition detects the missing effect. -/
theorem missing_store_fails_memory :
    ResourcePre missingStore (Domain.resource missingStore 0 1) missingInitial ∧
      ¬AllExecutions missingInitial
        (fun result => Post (resourceInput (Domain.resource missingStore 0 1)) missingInitial result.state) := by
  refine ⟨Domain.resource_pre missingStore (by decide) (by decide) 0 1, ?_⟩
  intro claim
  have actual : Sequential.run (fun _ => false) 8 missingInitial = .ok missingResult := by rfl
  have wrong := (claim.project ⟨_, run_sound actual⟩).value
  change (Except.ok (0 : Word) : Except Error Word) = .ok 1 at wrong
  exact (by decide : (0 : Word) ≠ 1) (Except.ok.inj wrong)

end EDSL.Tests.CountedStoreFinal64

#print axioms EDSL.CountedStoreFinal64.claim
#print axioms EDSL.CountedStoreFinal64.resource_exact
#print axioms EDSL.Tests.CountedStoreFinal64.maximum_count
#print axioms EDSL.Tests.CountedStoreFinal64.inverted_branch_fails_result
#print axioms EDSL.Tests.CountedStoreFinal64.missing_store_fails_memory
#audit_edsl
