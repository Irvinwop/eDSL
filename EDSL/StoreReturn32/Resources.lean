/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.RawProof
import EDSL.OS.WordResources.Bridge

set_option warningAsError true

namespace EDSL.StoreReturn32
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.Grading.Trace
open EDSL.Grading.Write32 (Resources ResourcePre ResourcePolicy ResourceReturn resourceInput resourceRules)

/-- Both instruction orderings carry the actual OS world through their first
and second machine transitions. In the store-first case the copy uses the
already evolved world, and in the copy-first cases the store uses the copied
full-width address. No target loan or new admission premise is introduced. -/
private theorem current_prefixes {shape : Shape} {resource : Resources} {initial : State}
    (pre : ResourcePre shape.bytes resource initial) :
    ∃ middle evolved,
      WordResources.Current resource.call middle (stageOne shape initial) ∧
      WordResources.Current resource.call evolved (stageTwo initial) ∧
      WordResources.WordEffect (Threads.principal resource.call.worker) resource.call.ticket
        resource.call.targetPointer resource.seed initial (firstInstruction shape)
        ⟨.next (stageOne shape initial), []⟩ middle ∧
      WordResources.WordEffect (Threads.principal resource.call.worker) resource.call.ticket
        resource.call.targetPointer middle (stageOne shape initial) (secondInstruction shape)
        ⟨.next (stageTwo initial), []⟩ evolved := by
  have raw := pre.machine
  cases shape with
  | storeCopy =>
    have intent : Sequential.Instruction.storeIntent (firstInstruction .storeCopy) initial =
        some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
      simp [firstInstruction, Sequential.Instruction.storeIntent, X86.Instruction.storeIntent, pre.pointer]
    obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
      WordResources.current_store_step pre.current (first_decoded raw) intent false
    have storeEq : WordResources.storeAfterLength initial evolved
        (firstInstruction .storeCopy).length = stageOne .storeCopy initial := by
      have same := Except.ok.inj (actualStore.symm.trans (first_step raw false))
      exact StepResult.next.inj (congrArg Observation.result same)
    rw [storeEq] at currentStore
    have copyDecoded : Sequential.decodeAt (stageOne .storeCopy initial) = .ok (.movReg64 .rax .rdi) :=
      second_decoded raw
    obtain ⟨after, actualCopy, currentCopy, _, _, _, _, _⟩ :=
      WordResources.current_movReg64_step currentStore copyDecoded false
    have copyEq : after = stageTwo initial := by
      have same := Except.ok.inj (actualCopy.symm.trans (second_step raw false))
      exact StepResult.next.inj (congrArg Observation.result same)
    rw [copyEq] at currentCopy
    exact ⟨evolved, evolved, currentStore, currentCopy, .store intent stored, .readOnly rfl⟩
  | copyStore =>
    have copyDecoded : Sequential.decodeAt initial = .ok (.movReg64 .rax .rdi) := first_decoded raw
    obtain ⟨after, actualCopy, currentCopy, _, _, _, _, _⟩ :=
      WordResources.current_movReg64_step pre.current copyDecoded false
    have copyEq : after = stageOne .copyStore initial := by
      have same := Except.ok.inj (actualCopy.symm.trans (first_step raw false))
      exact StepResult.next.inj (congrArg Observation.result same)
    rw [copyEq] at currentCopy
    have intent : Sequential.Instruction.storeIntent (secondInstruction .copyStore)
        (stageOne .copyStore initial) =
        some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
      simp [secondInstruction, Sequential.Instruction.storeIntent, X86.Instruction.storeIntent,
        stageOne, State.writeRegister, pre.pointer]
    obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
      WordResources.current_store_step currentCopy (second_decoded raw) intent false
    have storeEq : WordResources.storeAfterLength (stageOne .copyStore initial) evolved
        (secondInstruction .copyStore).length = stageTwo initial := by
      have same := Except.ok.inj (actualStore.symm.trans (second_step raw false))
      exact StepResult.next.inj (congrArg Observation.result same)
    rw [storeEq] at currentStore
    exact ⟨resource.seed, evolved, currentCopy, currentStore, .readOnly rfl, .store intent stored⟩
  | copyStoreRax =>
    have copyDecoded : Sequential.decodeAt initial = .ok (.movReg64 .rax .rdi) := first_decoded raw
    obtain ⟨after, actualCopy, currentCopy, assigned, other, _, _, _⟩ :=
      WordResources.current_movReg64_step pre.current copyDecoded false
    have copyEq : after = stageOne .copyStoreRax initial := by
      have same := Except.ok.inj (actualCopy.symm.trans (first_step raw false))
      exact StepResult.next.inj (congrArg Observation.result same)
    rw [copyEq] at currentCopy assigned other
    have intent : Sequential.Instruction.storeIntent (secondInstruction .copyStoreRax)
        (stageOne .copyStoreRax initial) =
        some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
      simp only [secondInstruction, Sequential.Instruction.storeIntent, Address.eval]
      rw [assigned, pre.pointer, other .rsi (by decide)]
    obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
      WordResources.current_store_step currentCopy (second_decoded raw) intent false
    have storeEq : WordResources.storeAfterLength (stageOne .copyStoreRax initial) evolved
        (secondInstruction .copyStoreRax).length = stageTwo initial := by
      have same := Except.ok.inj (actualStore.symm.trans (second_step raw false))
      exact StepResult.next.inj (congrArg Observation.result same)
    rw [storeEq] at currentStore
    exact ⟨resource.seed, evolved, currentCopy, currentStore, .readOnly rfl, .store intent stored⟩

/-- Current owner authority produces the actual checked store and complete
RAM coupling at each stage. The current original caller loan and the preserved
machine RSP derive RET; actual prefix/return witnesses follow the same worlds. -/
theorem resource_policy {shape : Shape} {resource : Resources} {initial : State}
    (pre : ResourcePre shape.bytes resource initial) : ResourcePolicy resource initial := by
  have raw := pre.machine
  obtain ⟨middle, evolved, currentOne, currentTwo, firstEffect, secondEffect⟩ := current_prefixes pre
  have stackBinding : (stageTwo initial).registers .rsp = resource.call.stack := by
    simpa [stageTwo, State.writeRegister] using pre.stack
  have returnAfterEq : WordResources.returnAfter (stageTwo initial) resource.call.returnAddress =
      finalState initial (resourceInput resource).returnAddress := by
    simp [WordResources.returnAfter, finalState, stageTwo, State.writeRegister, resourceInput]
  have retActual (af : Bool) :=
    WordResources.current_ret_step currentTwo (ret_decoded raw) stackBinding af
  have currentReturn := (retActual false).2.1
  rw [returnAfterEq] at currentReturn
  have fetch {before instruction} (offset : Nat)
      (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
      (span : offset + instruction.length ≤ shape.bytes.length) :
      Grading.Write32.FetchAllowed resource.call.code resource.call.bytes.length before instruction := by
    rw [pre.code, ← pre.entry]
    exact fetch_at raw offset pc span
  refine ⟨(fun shared before =>
    (shared = resource.seed ∧ before = initial) ∨
    (shared = middle ∧ before = stageOne shape initial) ∨
    (shared = evolved ∧ before = stageTwo initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, firstInstruction shape, first_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (stageOne shape initial), []⟩, middle, first_step raw af, ?_, ?_,
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch 0 (by simp) (by cases shape <;> decide), firstEffect⟩
  · subst shared
    subst before
    refine ⟨currentOne, secondInstruction shape, second_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (stageTwo initial), []⟩, evolved, second_step raw af, ?_, ?_,
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch (firstLength shape) (by cases shape <;> rfl)
        (by cases shape <;> decide), secondEffect⟩
  · subst shared
    subst before
    refine ⟨currentTwo, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, evolved, ?_, ?_,
      ⟨fetch 5 rfl (by cases shape <;> decide), .readOnly rfl⟩, currentReturn⟩
    · simpa only [returnAfterEq, pre.stack] using (retActual af).1
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      refine ⟨?_, ?_⟩
      · exact ⟨pre.stack, rfl, pre.stack ▸ (retActual af).2.2.1⟩
      · simpa only [pre.stack] using (retActual af).2.2.2

/-- Universal managed correctness retains the stronger pointer result, exact
three-instruction accounting, and the unchanged current-resource return
history, including all original loans and the complete outside-target frame. -/
theorem resource_semantics {shape : Shape} {resource : Resources} {initial : State}
    (pre : ResourcePre shape.bytes resource initial) :
    AllExecutions initial (fun result =>
      ResultContract (resourceInput resource) initial result ∧ ResourceReturn resource initial result) ∧
      ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned⟩

end EDSL.StoreReturn32
