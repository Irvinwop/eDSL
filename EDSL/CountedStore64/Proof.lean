/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Certificate

set_option warningAsError true

namespace EDSL.CountedStore64.GCC
open EDSL X86 X86.Sequential Grading.Trace

/-- All decoded prefixes use only the admitted code span, ordinary contained
full64 stores and the original caller's complete eight-byte return slot. -/
theorem raw_policy {input initial} (pre : Pre bytes input initial) :
    RawPolicy bytes input initial :=
  (certificate pre (rawSupport input initial)).policy (entry := .entry) (seed := ())
    rfl ⟨True.intro, rfl⟩

/-- Present caller facts imply actual all-AF termination and the independent
mathematical result for every full64 count. The conservative instruction bound
is separate from the result and is not a time or optimality claim. -/
theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state ∧
      result.instructions ≤ 7 * (input.count.toNat + 2)) := by
  intro choices
  obtain ⟨result, _, actual, post, _, _, bound⟩ :=
    (certificate pre (rawSupport input initial)).execution (entry := .entry) (seed := ())
      rfl ⟨True.intro, rfl⟩ choices
  refine ⟨result, actual, post, ?_⟩
  change result.instructions ≤ 7 * ((initial.registers .rdx).toNat + 1 + 1) at bound
  simpa only [pre.count, Nat.add_assoc,
    show 1 + 1 = 2 from rfl] using bound

/-- Every actual STORE is the checked owner mutation in the same evolved OS
world. No successful mutation or future evaluator run is an admission fact. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial :=
  (certificate pre.machine (resourceSupport pre)).policy
    (entry := .entry) (seed := resource.memory.seed) rfl ⟨pre.memory.current, rfl⟩

/-- Current-world termination, result, complete frames and usable returned
authority hold together for every count and every modeled undefined AF choice. -/
theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result =>
      Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result ∧
      result.instructions ≤ 7 * (resource.count.toNat + 2)) ∧ ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post, bound⟩ := raw_semantics pre.machine choices
  exact ⟨result, execution, post,
    Grading.StoreReturnValue64.ResourcePolicy.returned pre.memory policy, bound⟩

end EDSL.CountedStore64.GCC
