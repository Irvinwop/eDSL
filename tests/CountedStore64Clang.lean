/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Clang.Artifact
import EDSL.CountedStore64.Artifact
import EDSL.CountedStore64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CountedStore64Clang
open EDSL X86 X86.Sequential CountedStore64

/-- Zero count skips all stores and still executes the real four-instruction
entry/return path, for any admitted old target and undefined AF choices. -/
theorem zero_keeps_old {input initial} (pre : Pre Clang.bytes input initial)
    (zero : input.count = 0) (choices : Choices) :
    ∃ result, Sequential.run choices 4 initial = .ok result ∧
      result.instructions = 4 ∧ result.state.registers .rax = input.argument ∧
      loadQWord result.state.memory input.address = .ok input.oldValue ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  obtain ⟨result, run, post, cost, reads⟩ :=
    Clang.Artifact.raw_exact_run (by decide) pre choices
  refine ⟨result, ?_, ?_, ?_, ?_, reads⟩
  · simpa [zero] using run
  · simpa [zero] using cost
  · simpa [zero] using post.result
  · simpa only [expectedValue, zero, ite_true] using post.value

/-- Counts with no low32 bits still contribute fully to result and exact cost. -/
theorem high_count (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial Clang.bytes 0 0x100000000) result ∧
      result.instructions = 17179869188 ∧ result.state.registers .rax = 0x100000000 ∧
      loadQWord result.state.memory 262144 = .ok 0x100000000 ∧
      ResourceReturn (Domain.resource Clang.bytes 0 0x100000000)
        (Domain.initial Clang.bytes 0 0x100000000) result := by
  have pre := Domain.resource_pre Clang.bytes (by decide) (by decide) 0 0x100000000
  obtain ⟨result, actual, post, returned, cost, _, _⟩ := Clang.resource_exact pre choices
  exact ⟨result, actual, cost, post.result, post.value, returned⟩

/-- Natural instruction counts cannot wrap even at the maximum admitted count. -/
theorem maximum_count (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial Clang.bytes 1 0xffffffffffffffff) result ∧
      result.instructions = 73786976294838206464 ∧ result.state.registers .rax = 0 ∧
      loadQWord result.state.memory 262144 = .ok 0 ∧
      ResourceReturn (Domain.resource Clang.bytes 1 0xffffffffffffffff)
        (Domain.initial Clang.bytes 1 0xffffffffffffffff) result := by
  have pre := Domain.resource_pre Clang.bytes (by decide) (by decide) 1 0xffffffffffffffff
  obtain ⟨result, actual, post, returned, cost, _, _⟩ := Clang.resource_exact pre choices
  exact ⟨result, actual, cost, post.result, post.value, returned⟩

/-- A single admitted iteration needs eight instructions; fuel seven must
not silently omit RET. This checks the actual evaluator, not a shape gate. -/
theorem one_fuel_short :
    ResourcePre Clang.bytes (Domain.resource Clang.bytes 0 1) (Domain.initial Clang.bytes 0 1) ∧
      Sequential.run (fun _ => false) 7 (Domain.initial Clang.bytes 0 1) = .error .exhaustedFuel :=
  ⟨Domain.resource_pre Clang.bytes (by decide) (by decide) 0 1, by rfl⟩

/-- Returned authority operates on the same evolved RAM and original loans,
and permits an arbitrary subsequent full64 checked store. -/
theorem store_again {resource initial} (pre : ResourcePre Clang.bytes resource initial)
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
  obtain ⟨result, actual, _, returned, _⟩ := (Clang.resource_semantics pre).1 choices
  obtain ⟨evolved, lifted, current, frame, _, again⟩ := returned choices actual
  obtain ⟨nextWorld, checked⟩ := again nextValue
  have effect := OS.Borrowing.store64_effect checked
  exact ⟨result, evolved, nextWorld, actual, current, lifted, checked, effect.readback,
    effect.allocations.trans frame.allocations, effect.loans.trans frame.loans⟩

/-- The separate compiler profiles retain their different exact costs. -/
example : Artifact.check Clang.bytes = false ∧ Clang.Artifact.check GCC.bytes = false := by decide

private def inverted : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x85, 0xd2, 0x74, 0x0b,
  0x48, 0xff, 0xc0, 0x48, 0x89, 0x07, 0x48, 0xff, 0xca, 0x74, 0xf5, 0xc3]
private def invertedInitial := Domain.initial inverted 0 2
private def invertedResult : Result :=
  ⟨Clang.finish (Clang.exited invertedInitial.rip
      (Clang.body invertedInitial.rip (Clang.move invertedInitial) false)) 8192,
    8, [⟨.stack, 65544, 8⟩]⟩

/-- Owned JZ-for-JNZ code is genuinely admitted and executes supported
instructions, but returns after one iteration when two are required. -/
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

end EDSL.Tests.CountedStore64Clang

#print axioms EDSL.CountedStore64.Clang.resource_exact
#print axioms EDSL.Tests.CountedStore64Clang.maximum_count
#print axioms EDSL.Tests.CountedStore64Clang.inverted_branch_fails_result
#audit_edsl
