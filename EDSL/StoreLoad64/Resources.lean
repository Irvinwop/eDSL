/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreLoad64.RawProof
import EDSL.OS.WordResources64.Bridge
import EDSL.Grading.Trace

set_option warningAsError true

namespace EDSL.StoreLoad64
open X86 X86.Sequential OS Grading.Trace
open OS.WordResources64

/-- Immutable input and an ordinary current Borrowing world, shared with all
existing 32-bit resources and loans. -/
structure Resources where
  seed : Borrowing.State
  call : WordResources64.Call
  argument : Word
  oldValue : Word

def resourceInput (resource : Resources) : Input :=
  ⟨resource.call.targetPointer, resource.argument, resource.oldValue, resource.call.returnAddress⟩

structure ResourcePre (bytes : List Byte) (resource : Resources) (initial : State) : Prop where
  current : WordResources64.Current resource.call resource.seed initial
  code : resource.call.bytes = bytes
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  pointer : initial.registers .rdi = resource.call.targetPointer
  source : initial.registers .rsi = resource.argument
  oldValue : loadQWord initial.memory resource.call.targetPointer = .ok resource.oldValue

theorem ResourcePre.machine {bytes resource initial} (pre : ResourcePre bytes resource initial) :
    Pre bytes (resourceInput resource) initial := by
  have contract := pre.current.contract
  refine ⟨?_, pre.pointer, pre.source, pre.oldValue, ?_, ?_, ?_, ?_,
    contract.returnCanonical, ?_, ?_⟩
  · rw [pre.current.coupled, pre.entry, ← pre.code]
    exact contract.code
  · rw [pre.current.coupled]
    exact contract.word.writable
  · rw [pre.entry, ← pre.code]
    exact contract.codeDisjoint
  · rw [pre.stack]
    exact contract.stackDisjoint
  · rw [pre.current.coupled, pre.stack]
    exact contract.stack
  · rw [pre.stack]
    exact contract.stackBound
  · rw [pre.stack]
    exact contract.postStackCanonical

/-- Current resources derive one actual mutation, the following current load,
and RET, all coupled to the SAME evolved world. -/
theorem checked_steps {resource initial} (pre : ResourcePre bytes resource initial) :
    ∃ evolved,
      Borrowing.mutate resource.seed (.store64 (Threads.principal resource.call.worker)
        resource.call.ticket resource.call.targetPointer resource.argument) = .ok (evolved, none) ∧
      WordResources64.Current resource.call evolved (stageOne initial) ∧
      WordResources64.Current resource.call evolved (stageTwo initial) ∧
      WordResources64.Current resource.call evolved (finalState initial resource.call.returnAddress) ∧
      Borrowing.StoreEffect64 resource.seed evolved resource.call.targetPointer resource.argument ∧
      (∀ identifier loan, resource.seed.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = resource.seed.resources.space.cells query) := by
  have raw := pre.machine
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rsi) initial =
      some (resource.call.targetPointer, resource.argument) := by
    simp [Sequential.Instruction.storeIntent64, Address.eval, pre.pointer, pre.source]
  obtain ⟨evolved, stored, actualStore, currentOne, effect, loans⟩ :=
    current_store64_step pre.current (first_decoded raw) intent false
  have storeEq : storeAfterLength initial evolved 3 = stageOne initial := by
    have same := Except.ok.inj (actualStore.symm.trans (first_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  change WordResources64.Current resource.call evolved (storeAfterLength initial evolved 3) at currentOne
  rw [storeEq] at currentOne
  have effective : (Address.base .rdi).eval (stageOne initial) = resource.call.targetPointer := pre.pointer
  obtain ⟨value, after, actualLoad, _, _, _, _, currentTwo, _, _, _, _⟩ :=
    current_load64_step currentOne (second_decoded raw) effective false
  have loadEq : after = stageTwo initial := by
    have same := Except.ok.inj (actualLoad.symm.trans (second_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [loadEq] at currentTwo
  have stackBinding : (stageTwo initial).registers .rsp = resource.call.stack := by
    simpa [stageTwo, stageOne, State.writeRegister] using pre.stack
  have ret := current_ret_step currentTwo (ret_decoded raw) stackBinding false
  have returnEq : returnAfter (stageTwo initial) resource.call.returnAddress =
      finalState initial resource.call.returnAddress := by
    simp [returnAfter, finalState, stageTwo, stageOne, State.writeRegister]
  rw [returnEq] at ret
  exact ⟨evolved, stored, currentOne, currentTwo, ret.2.1, effect, loans⟩

/-- Trace rules require present resource authority, actual decoded intent and
checked mutation. They do not introduce a new grader task or admission. -/
def resourceRules (call : WordResources64.Call) : Rules Borrowing.State where
  Current := WordResources64.Current call
  ReadAllowed := WordResources64.ReadAllowed call
  Effect shared before instruction observation evolved :=
    Borrowing.Subregion ⟨before.rip, instruction.length⟩ ⟨call.code, call.bytes.length⟩ ∧
      WordResources64.WordEffect (Threads.principal call.worker) call.ticket call.targetPointer
        shared before instruction observation evolved

def ResourcePolicy (resource : Resources) (initial : State) : Prop :=
  Policy (resourceRules resource.call) resource.seed initial

/-- Each actual prefix uses its current authority and RAM. The DATA8 load is
justified by the evolved owner's full target permission; RET uses the retained
original STACK8 loan and its actual machine RSP binding. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  obtain ⟨evolved, stored, currentOne, currentTwo, currentReturn, _, _⟩ := checked_steps pre
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rsi) initial =
      some (resource.call.targetPointer, resource.argument) := by
    simp [Sequential.Instruction.storeIntent64, Address.eval, pre.pointer, pre.source]
  have stackBinding : (stageTwo initial).registers .rsp = resource.call.stack := by
    simpa [stageTwo, stageOne, State.writeRegister] using pre.stack
  have returnEq : returnAfter (stageTwo initial) resource.call.returnAddress =
      finalState initial (resourceInput resource).returnAddress := by
    simp [returnAfter, finalState, stageTwo, stageOne, State.writeRegister, resourceInput]
  have retActual (af : Bool) := current_ret_step currentTwo (ret_decoded raw) stackBinding af
  have fetch {before : State} {instruction : Sequential.Instruction} (offset : Nat)
      (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
      (span : offset + instruction.length ≤ bytes.length) :
      Borrowing.Subregion ⟨before.rip, instruction.length⟩
        ⟨resource.call.code, resource.call.bytes.length⟩ := by
    rw [pre.code, ← pre.entry]
    exact fetch_at raw offset pc span
  refine ⟨(fun shared before =>
    (shared = resource.seed ∧ before = initial) ∨
    (shared = evolved ∧ before = stageOne initial) ∨
    (shared = evolved ∧ before = stageTwo initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, .storeMem64 (.base .rdi) .rsi, first_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (stageOne initial), []⟩, evolved, first_step raw af, ?_,
      ⟨fetch 0 (by simp) (by decide), .store64 intent stored⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    simp
  · subst shared
    subst before
    refine ⟨currentOne, .loadMem64 .rax (.base .rdi), second_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (stageTwo initial), [⟨.data, resource.call.targetPointer, 8⟩]⟩,
      evolved, second_step raw af, ?_, ⟨fetch 3 rfl (by decide), .readOnly rfl⟩,
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    obtain ⟨allocation, authorized, fits⟩ := currentOne.contract.word.authorize
    have loaded := stageOne_value raw
    exact ⟨⟨rfl, rfl, allocation, resource.argument, authorized, fits, loaded⟩,
      resource.argument, loaded⟩
  · subst shared
    subst before
    refine ⟨currentTwo, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial (resourceInput resource).returnAddress),
      [⟨.stack, resource.call.stack, 8⟩]⟩, evolved, ?_, ?_,
      ⟨fetch 6 rfl (by decide), .readOnly rfl⟩, currentReturn⟩
    · simpa only [returnEq] using (retActual af).1
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨(retActual af).2.2.1, (retActual af).2.2.2⟩

/-- Returned authority belongs to the same actual machine/ghost trace. All
original loan contents survive and the owner can perform another checked
full-width mutation immediately, with an arbitrary next value. -/
def ResourceReturn (resource : Resources) (initial : State) (result : Result) : Prop :=
  ∀ choices, Sequential.Executes choices initial result →
    ∃ evolved,
      LiftedExecutes (resourceRules resource.call) choices initial resource.seed result evolved ∧
      WordResources64.Current resource.call evolved result.state ∧
      WordResources64.Frame resource.call.targetPointer resource.seed evolved ∧
      (∀ identifier loan, resource.seed.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = resource.seed.resources.space.cells query) ∧
      (∀ nextValue : Word, ∃ nextWorld,
        Borrowing.mutate evolved (.store64 (Threads.principal resource.call.worker)
          resource.call.ticket resource.call.targetPointer nextValue) = .ok (nextWorld, none))

theorem ResourcePolicy.returned {resource initial} (pre : ResourcePre bytes resource initial)
    (policy : ResourcePolicy resource initial) {result : Result} :
    ResourceReturn resource initial result := by
  intro choices execution
  obtain ⟨evolved, lifted, current⟩ := policy_return policy execution
  have frame : WordResources64.Frame resource.call.targetPointer resource.seed evolved :=
    LiftedExecutes.fold (rules := resourceRules resource.call) (Frame.refl resource.call.targetPointer)
      (fun _ _ _ first last => Frame.trans first last)
      (fun _ _ _ _ _ effect => wordEffect_frame effect.2) lifted
  exact ⟨evolved, lifted, current, frame,
    fun _ _ live => frame.loan_contents pre.current.contract.wellFormed live,
    fun value => current_store64_enabled current value⟩

/-- Universal functional correctness, exact accounting and actual checked
current-world semantics, including usable returned owner authority. -/
theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result =>
      ResultContract (resourceInput resource) initial result ∧ ResourceReturn resource initial result) ∧
      ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := raw_semantics pre.machine choices
  exact ⟨result, execution, post, ResourcePolicy.returned pre policy⟩

end EDSL.StoreLoad64
