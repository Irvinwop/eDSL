/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Clang.Machine
import EDSL.CountedStore64.Bridges
import EDSL.Grading.Trace.ResourceCutpoints

set_option warningAsError true

namespace EDSL.CountedStore64.Clang
open EDSL X86 X86.Sequential OS Grading.Trace

/-- Instantiated below by ordinary RAM rules and by checked current ownership.
The common loop proof uses the same actual machine states in either case. -/
structure Support {Ghost : Type} (input : Input) (initial : State) (rules : Rules Ghost) where
  sameMemory : ∀ {shared before after}, rules.Current shared before →
    after.memory = before.memory → rules.Current shared after
  readOnly : ∀ shared before instruction observation,
    CFG.readOnly instruction = true →
    Grading.StoreReturnValue64.FetchAllowed initial.rip bytes.length before instruction →
    rules.Effect shared before instruction observation shared
  store : ∀ shared before,
    rules.Current shared before →
    Sequential.decodeAt before = .ok (instruction .store) →
    before.registers .rdi = input.address →
    canStoreQWord before.memory input.address = true →
    Grading.StoreReturnValue64.FetchAllowed initial.rip bytes.length before (instruction .store) →
    ∃ evolved, rules.Current evolved (Clang.store before) ∧
      rules.Effect shared before (instruction .store) ⟨.next (Clang.store before), []⟩ evolved
  stack : ∀ shared before,
    rules.Current shared before → before.registers .rsp = initial.registers .rsp →
    readWord before.memory (initial.registers .rsp) = .ok input.returnAddress →
    rules.ReadAllowed shared before ⟨.stack, initial.registers .rsp, 8⟩ ∧
      OperandReadSucceeds before ⟨.stack, initial.registers .rsp, 8⟩

/-- Ordinary-RAM support keeps the original full-width store and caller-slot
read rules. It does not manufacture a current OS authority. -/
theorem rawSupport (input : Input) (initial : State) :
    Support input initial (Grading.StoreReturnValue64.rawRules bytes input.toInput initial) where
  sameMemory _ _ := True.intro
  readOnly _ _ _ _ allowed fetch := ⟨fetch, .readOnly allowed⟩
  store shared before _ _ pointer _ fetch := by
    refine ⟨shared, True.intro, fetch, .store64 (value := before.registers .rax) ?_⟩
    simpa only [pointer] using store_intent before
  stack _ _ _ _ loaded := ⟨⟨rfl, rfl⟩, rfl, input.returnAddress, loaded⟩

/-- Current ownership derives a checked mutation and the same actual STORE
successor as the common machine proof. Fetches and stack reads retain the
original live code/caller loans. -/
theorem resourceSupport {resource initial} (pre : ResourcePre bytes resource initial) :
    Support (resourceInput resource) initial
      (Grading.StoreReturnValue64.resourceRules resource.memory.call) where
  sameMemory current unchanged := current.sameMemory unchanged
  readOnly _ _ _ _ allowed fetch := by
    refine ⟨?_, .readOnly allowed⟩
    simpa only [Grading.StoreReturnValue64.FetchAllowed, pre.memory.entry,
      pre.memory.code] using fetch
  store shared before current decoded pointer allowed fetch := by
    change before.registers .rdi = resource.memory.call.targetPointer at pointer
    change canStoreQWord before.memory resource.memory.call.targetPointer = true at allowed
    have intent : (instruction .store).storeIntent64 before =
        some (resource.memory.call.targetPointer, before.registers .rax) := by
      simpa only [pointer] using store_intent before
    obtain ⟨evolved, checked, actual, present, _, _⟩ :=
      WordResources64.current_store64_step current decoded intent false
    have rawStep : step false before = .ok ⟨.next (Clang.store before), []⟩ := by
      rw [step_eq_execute false decoded]
      exact execute_store before false (by simpa only [pointer] using allowed)
    have same : WordResources64.storeAfterLength before evolved (instruction .store).length =
        Clang.store before := by
      have observation := Except.ok.inj (actual.symm.trans rawStep)
      exact StepResult.next.inj (congrArg Observation.result observation)
    refine ⟨evolved, ?_, ?_, .store64 intent checked⟩
    · change WordResources64.Current resource.memory.call evolved (Clang.store before)
      rw [← same]
      exact present
    · simpa only [Grading.StoreReturnValue64.FetchAllowed, pre.memory.entry,
        pre.memory.code] using fetch
  stack _ _ current _ loaded := by
    refine ⟨⟨pre.memory.stack, rfl, ?_⟩, rfl, (resourceInput resource).returnAddress, loaded⟩
    rw [pre.memory.stack]
    exact WordResources64.stackRead_permission current.contract

end EDSL.CountedStore64.Clang
