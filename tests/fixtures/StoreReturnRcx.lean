/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.OS.WordResources.Bridge

set_option warningAsError true

namespace EDSL.StoreReturnRcx
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading EDSL.Grading.Trace
open EDSL.Grading.Write32

/-- A separate client: copy the full pointer through RCX, store through RCX,
copy RCX to the full-width return register, and return through the caller slot. -/
def bytes : List Byte := [0x48, 0x89, 0xf9, 0x89, 0x31, 0x48, 0x89, 0xc8, 0xc3]

def afterCopy (initial : State) : State :=
  { initial.writeRegister .rcx (initial.registers .rdi) with rip := initial.rip + 3 }

def afterStore (initial : State) : State :=
  { afterCopy initial with
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 5 }

def afterReturnCopy (initial : State) : State :=
  { (afterStore initial).writeRegister .rax (initial.registers .rdi) with rip := initial.rip + 8 }

def finalState (initial : State) (target : Word) : State :=
  { (afterReturnCopy initial).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

private theorem decode_from_code {memory base} (code : CodeAt memory base bytes)
    (offset : Nat) (inside : offset < bytes.length) {state instruction}
    (mem : state.memory = memory) (pc : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction :=
  decodeAt_transport (code_fetch_transport code (by decide) offset inside state mem pc) decoded

private theorem stored_code {input initial} (pre : Pre bytes input initial) :
    CodeAt (afterStore initial).memory initial.rip bytes := by
  apply writeDWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

private theorem copy_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.movReg64 .rcx .rdi) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

private theorem store_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterCopy initial) = .ok (.storeMem32 (.base .rcx) .rsi) :=
  decode_from_code pre.code 3 (by decide) rfl rfl rfl

private theorem returnCopy_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterStore initial) = .ok (.movReg64 .rax .rcx) :=
  decode_from_code (stored_code pre) 5 (by decide) rfl rfl rfl

private theorem ret_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterReturnCopy initial) = .ok (.legacy .ret) :=
  decode_from_code (stored_code pre) 8 (by decide) rfl rfl rfl

private theorem copy_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterCopy initial), []⟩ := by
  rw [step_eq_execute af (copy_decoded pre)]
  rfl

private theorem store_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterCopy initial) = .ok ⟨.next (afterStore initial), []⟩ := by
  rw [step_eq_execute af (store_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [execute_storeMem32, Address.eval, afterCopy, afterStore, State.writeRegister,
    storeDWord, writable, Sequential.Instruction.length, BitVec.add_assoc]

private theorem returnCopy_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterStore initial) = .ok ⟨.next (afterReturnCopy initial), []⟩ := by
  rw [step_eq_execute af (returnCopy_decoded pre)]
  simp [execute_movReg64, afterReturnCopy, afterStore, afterCopy, State.writeRegister,
    BitVec.add_assoc]

private theorem stored_stack {input initial} (pre : Pre bytes input initial) :
    readWord (afterReturnCopy initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

private theorem ret_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterReturnCopy initial) =
      .ok ⟨.returned (finalState initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (afterReturnCopy initial).memory ((afterReturnCopy initial).registers .rsp) =
      .ok input.returnAddress := by
    simpa [afterReturnCopy, afterStore, afterCopy, State.writeRegister] using stored_stack pre
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [afterReturnCopy, afterStore, afterCopy, State.writeRegister]

/-- Independent pointer/store/caller contract for arbitrary original inputs,
full-width addresses and source high bits; no instruction accounting is assumed. -/
theorem final_post {input initial} (pre : Pre bytes input initial) :
    StoreReturn32.Post input initial (finalState initial input.returnAddress) := by
  have noWrap : input.address.toNat + 3 < 2^64 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp pre.target_addressable).1
  refine ⟨⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩, ?_⟩
  · have readback := load_after_write initial.memory input.address
      (input.argument.setWidth 32) pre.target_addressable
    simpa only [finalState, State.writeRegister, afterReturnCopy, afterStore,
      pre.pointer, pre.source] using readback
  · intro query outside
    have large : 4 ≤ (query - input.address).toNat := by
      have excluded := mt (AddressSpace.word_contains_iff input.address query noWrap).mpr outside
      omega
    exact writeDWord_frame initial.memory _ query _ (by rwa [pre.pointer])
  · simp [finalState, afterReturnCopy, afterStore, afterCopy, State.writeRegister]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same; subst register; simp [calleeSaved] at member
    have notRcx : register ≠ .rcx := by
      intro same; subst register; simp [calleeSaved] at member
    have notRax : register ≠ .rax := by
      intro same; subst register; simp [calleeSaved] at member
    simp [finalState, afterReturnCopy, afterStore, afterCopy, State.writeRegister,
      notStack, notRcx, notRax]
  · simpa [finalState, afterReturnCopy, afterStore, afterCopy, State.writeRegister] using pre.pointer

/-- Every AF stream follows four actual instructions with one stack operand. -/
theorem executions {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial input.returnAddress, 4, [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (copy_step pre (choices 0))
    (Sequential.Executes.next (store_step pre ((choices.drop 1) 0))
      (Sequential.Executes.next (returnCopy_step pre (((choices.drop 1).drop 1) 0))
        (Sequential.Executes.ret (ret_step pre ((((choices.drop 1).drop 1).drop 1) 0)))))
  simpa only [Result.prepend, List.nil_append] using execution

private theorem fetch_at {input initial before instruction} (pre : Pre bytes input initial)
    (offset : Nat) (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    FetchAllowed initial.rip bytes.length before instruction := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 9 ≤ 2^64 at limit
  change offset + instruction.length ≤ 9 at span
  have small : offset < 2^64 := by omega
  have total : initial.rip.toNat + offset < 2^64 := by omega
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 9
  rw [pc, natural]
  omega

/-- Every actual prefix obeys the unchanged fixed-target and current-fetch
raw policies. The client invariant is proved evidence, not domain admission. -/
theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  refine ⟨(fun (_ : Unit) state => state = initial ∨ state = afterCopy initial ∨
    state = afterStore initial ∨ state = afterReturnCopy initial), Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same | same | same
  · subst before
    refine ⟨True.intro, .movReg64 .rcx .rdi, copy_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterCopy initial), []⟩, (), copy_step pre af, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · simp
    · exact ⟨fetch_at pre 0 (by simp) (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .storeMem32 (.base .rcx) .rsi, store_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, (), store_step pre af, ?_, ?_,
      Or.inr (Or.inr (Or.inl rfl))⟩
    · simp
    · refine ⟨fetch_at pre 3 rfl (by decide), Or.inr ⟨(initial.registers .rsi).setWidth 32, ?_⟩⟩
      simp [Sequential.Instruction.storeIntent, Address.eval, afterCopy, State.writeRegister, pre.pointer]
  · subst before
    refine ⟨True.intro, .movReg64 .rax .rcx, returnCopy_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterReturnCopy initial), []⟩, (), returnCopy_step pre af, ?_, ?_,
      Or.inr (Or.inr (Or.inr rfl))⟩
    · simp
    · exact ⟨fetch_at pre 5 rfl (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre af, ?_, ?_, True.intro⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, stored_stack pre⟩
    · exact ⟨fetch_at pre 8 rfl (by decide), Or.inl rfl⟩

/-- All raw inputs satisfy the independent registered pointer-return contract. -/
theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => StoreReturn32.Post input initial result.state) ∧
      RawPolicy bytes input initial :=
  ⟨fun choices => ⟨_, executions pre choices, final_post pre⟩, raw_policy pre⟩

/-- Copies and the actual checked mutation share current OS resources. The
second copy uses the evolved world; its preserved RSP supplies RET's separate
caller-slot binding. No mutation-blocking target loan is created. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  obtain ⟨copied, actualCopy, currentCopy, assigned, preservedCopy, _, _, _⟩ :=
    WordResources.current_movReg64_step pre.current (copy_decoded raw) false
  have copyEq : copied = afterCopy initial := by
    have same := Except.ok.inj (actualCopy.symm.trans (copy_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [copyEq] at currentCopy assigned preservedCopy
  have intent : Sequential.Instruction.storeIntent (.storeMem32 (.base .rcx) .rsi)
      (afterCopy initial) = some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
    simp only [Sequential.Instruction.storeIntent, Address.eval]
    rw [assigned, pre.pointer, preservedCopy .rsi (by decide)]
  obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
    WordResources.current_store_step currentCopy (store_decoded raw) intent false
  have storeEq : WordResources.storeAfterLength (afterCopy initial) evolved
      (Sequential.Instruction.storeMem32 (.base .rcx) .rsi).length = afterStore initial := by
    have same := Except.ok.inj (actualStore.symm.trans (store_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [storeEq] at currentStore
  obtain ⟨returnCopied, actualReturnCopy, currentReturnCopy, _, preservedReturnCopy, _, _, _⟩ :=
    WordResources.current_movReg64_step currentStore (returnCopy_decoded raw) false
  have returnCopyEq : returnCopied = afterReturnCopy initial := by
    have same := Except.ok.inj (actualReturnCopy.symm.trans (returnCopy_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [returnCopyEq] at currentReturnCopy preservedReturnCopy
  have storedStack : (afterStore initial).registers .rsp = resource.call.stack := by
    have frame := congrArg (fun state : State => state.registers .rsp) storeEq
    change (afterCopy initial).registers .rsp = (afterStore initial).registers .rsp at frame
    exact frame.symm.trans ((preservedCopy .rsp (by decide)).trans pre.stack)
  have stackBinding : (afterReturnCopy initial).registers .rsp = resource.call.stack :=
    (preservedReturnCopy .rsp (by decide)).trans storedStack
  have returnAfterEq : WordResources.returnAfter (afterReturnCopy initial)
      resource.call.returnAddress = finalState initial (resourceInput resource).returnAddress := by
    simp [WordResources.returnAfter, finalState, afterReturnCopy, afterStore, afterCopy,
      State.writeRegister, resourceInput]
  have retActual (af : Bool) :=
    WordResources.current_ret_step currentReturnCopy (ret_decoded raw) stackBinding af
  have currentReturn := (retActual false).2.1
  rw [returnAfterEq] at currentReturn
  have fetch {before instruction} (offset : Nat)
      (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
      (span : offset + instruction.length ≤ bytes.length) :
      FetchAllowed resource.call.code resource.call.bytes.length before instruction := by
    rw [pre.code, ← pre.entry]
    exact fetch_at raw offset pc span
  refine ⟨(fun shared before =>
    (shared = resource.seed ∧ before = initial) ∨
    (shared = resource.seed ∧ before = afterCopy initial) ∨
    (shared = evolved ∧ before = afterStore initial) ∨
    (shared = evolved ∧ before = afterReturnCopy initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ |
    ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, .movReg64 .rcx .rdi, copy_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterCopy initial), []⟩, resource.seed, copy_step raw af, ?_, ?_,
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch 0 (by simp) (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentCopy, .storeMem32 (.base .rcx) .rsi, store_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, evolved, store_step raw af, ?_, ?_,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · simp
    · exact ⟨fetch 3 rfl (by decide), .store intent stored⟩
  · subst shared
    subst before
    refine ⟨currentStore, .movReg64 .rax .rcx, returnCopy_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterReturnCopy initial), []⟩, evolved, returnCopy_step raw af, ?_, ?_,
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · simp
    · exact ⟨fetch 5 rfl (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentReturnCopy, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, evolved, ?_, ?_,
      ⟨fetch 8 rfl (by decide), .readOnly rfl⟩, currentReturn⟩
    · simpa only [returnAfterEq, pre.stack] using (retActual af).1
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      refine ⟨?_, ?_⟩
      · exact ⟨pre.stack, rfl, pre.stack ▸ (retActual af).2.2.1⟩
      · simpa only [pre.stack] using (retActual af).2.2.2

/-- Every raw/current-resource input satisfies the same independent Post,
with coherent lifted actual histories and the original complete loan frame. -/
theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result => StoreReturn32.Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result) ∧ ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned⟩

/-- Accounting follows actual execution uniqueness, separately from the task's
mathematical Post. It counts modeled instructions and stack bytes, not cycles. -/
theorem modeled_accounting {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 4 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 8 := by
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre choices)
  subst result
  simp

/-- Independent current domains include useful changing-value inputs. -/
theorem useful_domain : Nonvacuous (registered .storeReturn32) bytes :=
  domain_nonvacuous .storeReturn32 bytes (by decide) (by decide)

/-- Closed client proof exported to the unchanged trusted grader. This module
is compiled as a submission and is not part of the trusted import snapshot. -/
theorem claim : EDSL.Grading.Claim .storeReturn32 bytes :=
  ⟨⟨fun _ _ pre => raw_semantics pre, fun _ _ pre => resource_semantics pre⟩, useful_domain⟩

end EDSL.StoreReturnRcx
