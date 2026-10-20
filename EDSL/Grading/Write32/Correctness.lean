/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Resources
import EDSL.Grading.Write32.RawProof
import EDSL.OS.WordResources.Bridge

set_option warningAsError true

namespace EDSL.Grading.Write32
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.Grading.Trace

/-- All-input managed policy for the concrete two-instruction binary. The
seed first executes the checked real OS store; the same evolved world then
supplies RET authority. All other actual prefixes follow from Policy lifting. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  have decoded := store_decoded raw
  have intent : Sequential.Instruction.storeIntent (.legacy .storeEsiRdi) initial =
      some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent, pre.pointer]
  obtain ⟨evolved, stored, actual, currentStore, _, _⟩ :=
    EDSL.OS.WordResources.current_store_step pre.current decoded intent false
  have middleEq : EDSL.OS.WordResources.storeAfter initial evolved = afterStore initial := by
    have same := Except.ok.inj (actual.symm.trans (store_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  change EDSL.OS.WordResources.Current resource.call evolved
    (EDSL.OS.WordResources.storeAfter initial evolved) at currentStore
  rw [middleEq] at currentStore
  have currentReturn : EDSL.OS.WordResources.Current resource.call evolved
      (returned initial (resourceInput resource).returnAddress) :=
    ⟨currentStore.contract, currentStore.coupled⟩
  have storeFetch : FetchAllowed resource.call.code resource.call.bytes.length initial
      (.legacy .storeEsiRdi) := by
    rw [pre.code, ← pre.entry]
    exact store_fetch raw
  have retFetch : FetchAllowed resource.call.code resource.call.bytes.length (afterStore initial)
      (.legacy .ret) := by
    rw [pre.code, ← pre.entry]
    exact ret_fetch raw
  refine ⟨(fun shared before =>
    (shared = resource.seed ∧ before = initial) ∨
      (shared = evolved ∧ before = afterStore initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, .legacy .storeEsiRdi, decoded, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, evolved, store_step raw af, ?_, ?_,
      Or.inr ⟨rfl, rfl⟩⟩
    · simp
    · exact ⟨storeFetch, .store intent stored⟩
  · subst shared
    subst before
    refine ⟨currentStore, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (returned initial (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, evolved, ret_step raw af, ?_,
      ⟨retFetch, .readOnly rfl⟩, currentReturn⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    refine ⟨?_, rfl, _, afterStore_stack raw⟩
    change initial.registers .rsp = resource.call.stack ∧ 8 = 8 ∧
      ArrayResources.ReadPermission evolved resource.call.worker ⟨.stack, initial.registers .rsp, 8⟩
    exact ⟨pre.stack, rfl, pre.stack ▸ EDSL.OS.WordResources.stackRead_permission currentStore.contract⟩

/-- Both halves use the same independent Post. Managed returning witnesses
are obtained from the policy and the ACTUAL execution, never a Pre callback. -/
theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result =>
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result) ∧
      ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned⟩

end EDSL.Grading.Write32
