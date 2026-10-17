/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Artifact
import EDSL.CountedStore64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CountedStore64
open EDSL X86 X86.Sequential CountedStore64

/-- Zero count must retain any admitted old value, even if RSI differs. -/
theorem zero_keeps_old {input initial} (pre : Pre GCC.bytes input initial)
    (zero : input.count = 0) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      result.state.registers .rax = input.argument ∧
      loadQWord result.state.memory input.address = .ok input.oldValue := by
  obtain ⟨result, actual, post, _⟩ := GCC.raw_semantics pre choices
  refine ⟨result, actual, ?_, ?_⟩
  · simpa [zero] using post.result
  · simpa only [expectedValue, zero, ite_true] using post.value

/-- A high-half-only count must not be truncated to a zero low32 count.
This symbolic theorem does not execute four billion native iterations. -/
theorem high_count (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial GCC.bytes 0 0x100000000) result ∧
      result.state.registers .rax = 0x100000000 ∧
      loadQWord result.state.memory 262144 = .ok 0x100000000 ∧
      ResourceReturn (Domain.resource GCC.bytes 0 0x100000000)
        (Domain.initial GCC.bytes 0 0x100000000) result := by
  have pre := Domain.resource_pre GCC.bytes (by decide) (by decide) 0 0x100000000
  obtain ⟨result, actual, post, returned, _⟩ := (GCC.resource_semantics pre).1 choices
  exact ⟨result, actual, post.result, post.value, returned⟩

/-- Maximum full64 count is admitted and terminates, including value wrap.
The literal expected result is independent of the iteration implementation. -/
theorem maximum_count (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial GCC.bytes 1 0xffffffffffffffff) result ∧
      result.state.registers .rax = 0 ∧ loadQWord result.state.memory 262144 = .ok 0 ∧
      ResourceReturn (Domain.resource GCC.bytes 1 0xffffffffffffffff)
        (Domain.initial GCC.bytes 1 0xffffffffffffffff) result := by
  have pre := Domain.resource_pre GCC.bytes (by decide) (by decide) 1 0xffffffffffffffff
  obtain ⟨result, actual, post, returned, _⟩ := (GCC.resource_semantics pre).1 choices
  exact ⟨result, actual, post.result, post.value, returned⟩

/-- Every independently admitted execution retains arbitrary neighboring bytes
and both complete permission maps, regardless of the number of stores. -/
theorem complete_frame {input initial choices result} (pre : Pre GCC.bytes input initial)
    (actual : Sequential.Executes choices initial result) :
    (∀ query, 8 ≤ (query - input.address).toNat →
      result.state.memory.read query = initial.memory.read query) ∧
    result.state.memory.writable = initial.memory.writable ∧
    result.state.memory.executable = initial.memory.executable := by
  have post := (GCC.raw_semantics pre).project ⟨choices, actual⟩
  exact ⟨post.1.outside, post.1.writable, post.1.executable⟩

/-- Returned ownership can perform an arbitrary subsequent full64 store on
the same evolved world, with the actual RAM projection and original frames. -/
theorem store_again {resource initial} (pre : ResourcePre GCC.bytes resource initial)
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
  obtain ⟨result, actual, _, returned, _⟩ := (GCC.resource_semantics pre).1 choices
  obtain ⟨evolved, lifted, current, frame, _, again⟩ := returned choices actual
  obtain ⟨nextWorld, checked⟩ := again nextValue
  have effect := OS.Borrowing.store64_effect checked
  exact ⟨result, evolved, nextWorld, actual, current, lifted, checked, effect.readback,
    effect.allocations.trans frame.allocations, effect.loans.trans frame.loans⟩

private def missing : List Byte := [0x48, 0x89, 0xf0, 0xc3]
private def missingInitial := Domain.initial missing 0 1
private def missingResult : Result :=
  ⟨GCC.finish (GCC.move missingInitial) 8192, 2, [⟨.stack, 65544, 8⟩]⟩

/-- The no-store counterexample has genuine current admission. A byte-shape
rejection alone would not establish this independent semantic failure. -/
theorem missing_has_admission :
    ResourcePre missing (Domain.resource missing 0 1) missingInitial :=
  Domain.resource_pre missing (by decide) (by decide) 0 1

theorem missing_fails_result :
    ¬AllExecutions missingInitial
      (fun result => Post (resourceInput (Domain.resource missing 0 1)) missingInitial result.state) := by
  intro claim
  have actual : Sequential.run (fun _ => false) 2 missingInitial = .ok missingResult := by rfl
  have contract := claim.project ⟨_, run_sound actual⟩
  have wrong := contract.result
  change (0 : Word) = 1 at wrong
  exact (by decide : (0 : Word) ≠ 1) wrong

private def narrow : List Byte := [0x89, 0xd2] ++ GCC.bytes
private def narrowInitial := Domain.initial narrow 0 0x100000000
private def narrowed : State := { narrowInitial.writeRegister .rdx 0 with rip := narrowInitial.rip + 2 }
private def narrowResult : Result :=
  ⟨GCC.finish (GCC.exitState narrowed.rip (GCC.move narrowed) false) 8192,
    5, [⟨.stack, 65544, 8⟩]⟩

/-- The owned MOV EDX,EDX mutant clears the high count bits and returns early.
This checks a real supported execution, rather than unsupported decoding. -/
theorem narrow_count_fails_result :
    ResourcePre narrow (Domain.resource narrow 0 0x100000000) narrowInitial ∧
    ¬AllExecutions narrowInitial
      (fun result => Post (resourceInput (Domain.resource narrow 0 0x100000000)) narrowInitial result.state) := by
  refine ⟨Domain.resource_pre narrow (by decide) (by decide) 0 0x100000000, ?_⟩
  intro claim
  have actual : Sequential.run (fun _ => false) 5 narrowInitial = .ok narrowResult := by rfl
  have contract := claim.project ⟨_, run_sound actual⟩
  have wrong := contract.result
  change (0 : Word) = 0x100000000 at wrong
  exact (by decide : (0 : Word) ≠ 0x100000000) wrong

end EDSL.Tests.CountedStore64

#print axioms EDSL.CountedStore64.GCC.raw_semantics
#print axioms EDSL.CountedStore64.GCC.resource_semantics
#print axioms EDSL.Tests.CountedStore64.high_count
#print axioms EDSL.Tests.CountedStore64.maximum_count
#print axioms EDSL.Tests.CountedStore64.narrow_count_fails_result
#audit_edsl
