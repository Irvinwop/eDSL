/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.Grading.StoreReturnValue64.Resources

set_option warningAsError true

namespace EDSL.StoreReturnValue64Upper
open EDSL X86 X86.Sequential OS Grading Grading.Trace Grading.StoreReturnValue64

/-- MOV RCX,RDI; ADD RCX,4; MOV EDX,DWORD[RCX]; MOV RAX,RSI;
MOV QWORD[RDI],RAX; RET. The DATA4 read precedes the write. -/
def bytes : List Byte :=
  [0x48, 0x89, 0xf9, 0x48, 0x83, 0xc1, 0x04, 0x8b, 0x11,
    0x48, 0x89, 0xf0, 0x48, 0x89, 0x07, 0xc3]

def afterCopy (initial : State) : State :=
  { initial.writeRegister .rcx (initial.registers .rdi) with rip := initial.rip + 3 }

def afterAdd (initial : State) : State :=
  { (afterCopy initial).writeRegister .rcx (initial.registers .rdi + 4) with
    rip := initial.rip + 7
    flags := addFlags64 initial.flags (initial.registers .rdi) 4 }

def afterRead (initial : State) (upper : BitVec 32) : State :=
  { (afterAdd initial).writeRegister .rdx (upper.setWidth 64) with rip := initial.rip + 9 }

def afterResult (initial : State) (upper : BitVec 32) : State :=
  { (afterRead initial upper).writeRegister .rax (initial.registers .rsi) with rip := initial.rip + 12 }

def afterStore (initial : State) (upper : BitVec 32) : State :=
  { afterResult initial upper with
    memory := writeQWordUnchecked initial.memory (initial.registers .rdi) (initial.registers .rsi)
    rip := initial.rip + 15 }

def finalState (initial : State) (upper : BitVec 32) (target : Word) : State :=
  { (afterStore initial upper).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

/-- The complete eight-byte admission entails a nonwrapping, canonical
full-width address for the upper four-byte load. -/
theorem upper_address {input initial} (pre : Pre bytes input initial) :
    (input.address + 4).toNat = input.address.toNat + 4 ∧
      canonical (input.address + 4) = true ∧
      Borrowing.Subregion (AddressSpace.wordRegion (input.address + 4))
        (AddressSpace.qwordRegion input.address) := by
  have addr := pre.target_addressable
  simp only [qwordAddressable, Bool.and_eq_true, decide_eq_true_eq] at addr
  have natural : (input.address + 4).toNat = input.address.toNat + 4 := by
    change (input.address.toNat + 4) % 2^64 = input.address.toNat + 4
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨natural, addr.2.1.1.1.2, ?_⟩
  change input.address.toNat ≤ (input.address + 4).toNat ∧
    (input.address + 4).toNat + 4 ≤ input.address.toNat + 8
  rw [natural]
  omega

private theorem decode_from_code {memory base} (code : CodeAt memory base bytes)
    (offset : Nat) (inside : offset < bytes.length) {state instruction}
    (mem : state.memory = memory) (pc : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction :=
  decodeAt_transport (code_fetch_transport code (by decide) offset inside state mem pc) decoded

private theorem stored_code {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    CodeAt (afterStore initial upper).memory initial.rip bytes := by
  apply writeQWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

private theorem copy_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.movReg64 .rcx .rdi) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

private theorem add_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterCopy initial) = .ok (.addImm64 .rcx 4) :=
  decode_from_code pre.code 3 (by decide) rfl rfl rfl

private theorem read_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterAdd initial) = .ok (.loadMem32 .rdx (.base .rcx)) :=
  decode_from_code pre.code 7 (by decide) rfl rfl rfl

private theorem result_decoded {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    Sequential.decodeAt (afterRead initial upper) = .ok (.movReg64 .rax .rsi) :=
  decode_from_code pre.code 9 (by decide) rfl rfl rfl

private theorem store_decoded {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    Sequential.decodeAt (afterResult initial upper) = .ok (.storeMem64 (.base .rdi) .rax) :=
  decode_from_code pre.code 12 (by decide) rfl rfl rfl

private theorem ret_decoded {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    Sequential.decodeAt (afterStore initial upper) = .ok (.legacy .ret) :=
  decode_from_code (stored_code pre upper) 15 (by decide) rfl rfl rfl

private theorem copy_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterCopy initial), []⟩ := by
  rw [step_eq_execute af (copy_decoded pre)]
  rfl

private theorem add_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterCopy initial) = .ok ⟨.next (afterAdd initial), []⟩ := by
  rw [step_eq_execute af (add_decoded pre)]
  simp [execute_addImm64, afterAdd, afterCopy, State.writeRegister, BitVec.add_assoc]

private theorem read_step {input initial upper} (pre : Pre bytes input initial)
    (loaded : loadDWord initial.memory (input.address + 4) = .ok upper) (af : Bool) :
    Sequential.step af (afterAdd initial) =
      .ok ⟨.next (afterRead initial upper), [⟨.data, input.address + 4, 4⟩]⟩ := by
  rw [step_eq_execute af (read_decoded pre)]
  have observed : loadDWord (afterAdd initial).memory ((Address.base .rcx).eval (afterAdd initial)) =
      .ok upper := by
    simpa [Address.eval, afterAdd, afterCopy, State.writeRegister, pre.pointer] using loaded
  rw [execute_loadMem32, observed]
  simp [afterRead, afterAdd, afterCopy, Address.eval, State.writeRegister,
    Sequential.Instruction.length, BitVec.add_assoc, pre.pointer]

private theorem result_step {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) (af : Bool) :
    Sequential.step af (afterRead initial upper) = .ok ⟨.next (afterResult initial upper), []⟩ := by
  rw [step_eq_execute af (result_decoded pre upper)]
  simp [execute_movReg64, afterResult, afterRead, afterAdd, afterCopy,
    State.writeRegister, BitVec.add_assoc]

private theorem store_step {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) (af : Bool) :
    Sequential.step af (afterResult initial upper) = .ok ⟨.next (afterStore initial upper), []⟩ := by
  rw [step_eq_execute af (store_decoded pre upper)]
  have writable : canStoreQWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [execute_storeMem64, Address.eval, afterStore, afterResult, afterRead, afterAdd,
    afterCopy, State.writeRegister, storeQWord, writable, Sequential.Instruction.length, BitVec.add_assoc]

private theorem stored_stack {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    readWord (afterStore initial upper).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeQWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

private theorem ret_step {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) (af : Bool) :
    Sequential.step af (afterStore initial upper) =
      .ok ⟨.returned (finalState initial upper input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre upper)]
  have stack : readWord (afterStore initial upper).memory ((afterStore initial upper).registers .rsp) =
      .ok input.returnAddress := by
    simpa [afterStore, afterResult, afterRead, afterAdd, afterCopy, State.writeRegister] using stored_stack pre upper
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [afterStore, afterResult, afterRead, afterAdd, afterCopy, State.writeRegister]

/-- All six actual instructions execute, recording the original upper DATA4
address and width before the original caller STACK8. -/
theorem executions {input initial upper} (pre : Pre bytes input initial)
    (loaded : loadDWord initial.memory (input.address + 4) = .ok upper) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial upper input.returnAddress, 6,
        [⟨.data, input.address + 4, 4⟩, ⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (copy_step pre (choices 0))
    (Sequential.Executes.next (add_step pre (choices.drop 1 0))
      (Sequential.Executes.next (read_step pre loaded ((choices.drop 1).drop 1 0))
        (Sequential.Executes.next (result_step pre upper (((choices.drop 1).drop 1).drop 1 0))
          (Sequential.Executes.next (store_step pre upper ((((choices.drop 1).drop 1).drop 1).drop 1 0))
            (Sequential.Executes.ret (ret_step pre upper (((((choices.drop 1).drop 1).drop 1).drop 1).drop 1 0)))))))
  simpa only [Result.prepend, List.nil_append, List.cons_append] using execution

/-- The volatile loaded word is absent from this independent ordinary ABI
contract, while its actual value remains in the concrete execution state. -/
theorem final_post {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    Post input initial (finalState initial upper input.returnAddress) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [finalState, afterStore, afterResult, State.writeRegister] using pre.source
  · simpa only [finalState, afterStore, State.writeRegister, pre.pointer, pre.source] using
      qword_load_after_write initial.memory input.address input.argument pre.target_addressable
  · intro query outside
    exact writeQWord_frame initial.memory _ query _ (by simpa only [pre.pointer] using outside)
  · simp [finalState, afterStore, afterResult, afterRead, afterAdd, afterCopy, State.writeRegister]
  · intro register member
    have notStack : register ≠ .rsp := by intro same; subst register; simp [calleeSaved, EDSL.StoreLoad64.calleeSaved] at member
    have notRax : register ≠ .rax := by intro same; subst register; simp [calleeSaved, EDSL.StoreLoad64.calleeSaved] at member
    have notRdx : register ≠ .rdx := by intro same; subst register; simp [calleeSaved, EDSL.StoreLoad64.calleeSaved] at member
    have notRcx : register ≠ .rcx := by intro same; subst register; simp [calleeSaved, EDSL.StoreLoad64.calleeSaved] at member
    simp [finalState, afterStore, afterResult, afterRead, afterAdd, afterCopy,
      State.writeRegister, notStack, notRax, notRdx, notRcx]
  · exact addFlags64_preserves ..

private theorem upper_read_exists {input initial} (pre : Pre bytes input initial) :
    ∃ upper, loadDWord initial.memory (input.address + 4) = .ok upper :=
  WordResources64.loadDWord_of_canStoreQWord pre.writable (upper_address pre).2.2

private theorem fetch_at {input : Input} {initial before : State} {instruction : Sequential.Instruction}
    (pre : Pre bytes input initial) (offset : Nat)
    (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    FetchAllowed initial.rip bytes.length before instruction := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 16 ≤ 2^64 at limit
  change offset + instruction.length ≤ 16 at span
  have offsetLt : offset < 16 :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right positive) span
  have total : initial.rip.toNat + offset < 2^64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left offsetLt _) limit
  have small : offset < 2^64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) total
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 16
  rw [pc, natural]
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left span _

private theorem store_intent {input initial} (pre : Pre bytes input initial) (upper : BitVec 32) :
    Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rax)
      (afterResult initial upper) = some (input.address, initial.registers .rsi) := by
  change some (initial.registers .rdi, initial.registers .rsi) =
    some (input.address, initial.registers .rsi)
  rw [pre.pointer]

/-- DATA4 is authorized at its actual upper-word address, before the store.
All register-only arithmetic outcomes are covered by the actual execution. -/
private def rawInvariant (initial : State) (upper : BitVec 32) (_ : Unit) (before : State) : Prop :=
  before = initial ∨ before = afterCopy initial ∨
    before = afterAdd initial ∨ before = afterRead initial upper ∨
    before = afterResult initial upper ∨ before = afterStore initial upper

private def rawAt (input : Input) (initial : State) (upper : BitVec 32) (before : State) : Prop :=
  (rawRules bytes input initial).Current () before ∧
    ∃ instruction, Sequential.decodeAt before = .ok instruction ∧
      ∀ af, ∃ observation evolved,
        step af before = .ok observation ∧
        (∀ read ∈ observation.reads,
          (rawRules bytes input initial).ReadAllowed () before read ∧ OperandReadSucceeds before read) ∧
        (rawRules bytes input initial).Effect () before instruction observation evolved ∧
        match observation.result with
        | .next after => rawInvariant initial upper evolved after
        | .returned after => (rawRules bytes input initial).Current evolved after
        | .atomic _ _ | .syscall _ => False

private theorem raw_initial {input initial} {upper : BitVec 32} (pre : Pre bytes input initial) :
    rawAt input initial upper initial := by
  refine ⟨True.intro, .movReg64 .rcx .rdi, copy_decoded pre, ?_⟩
  intro af
  refine ⟨⟨.next (afterCopy initial), []⟩, (), copy_step pre af, ?_,
    ⟨fetch_at pre 0 (by simp) (by decide), .readOnly rfl⟩, Or.inr (Or.inl rfl)⟩
  simp

private theorem raw_copy {input initial} {upper : BitVec 32} (pre : Pre bytes input initial) :
    rawAt input initial upper (afterCopy initial) := by
  refine ⟨True.intro, .addImm64 .rcx 4, add_decoded pre, ?_⟩
  intro af
  refine ⟨⟨.next (afterAdd initial), []⟩, (), add_step pre af, ?_,
    ⟨fetch_at pre 3 rfl (by decide), .readOnly rfl⟩, Or.inr (Or.inr (Or.inl rfl))⟩
  simp

private theorem raw_add {input initial} {upper : BitVec 32} (pre : Pre bytes input initial)
    (loaded : loadDWord initial.memory (input.address + 4) = .ok upper) :
    rawAt input initial upper (afterAdd initial) := by
  refine ⟨True.intro, .loadMem32 .rdx (.base .rcx), read_decoded pre, ?_⟩
  intro af
  refine ⟨⟨.next (afterRead initial upper), [⟨.data, input.address + 4, 4⟩]⟩, (),
    read_step pre loaded af, ?_, ⟨fetch_at pre 7 rfl (by decide), .readOnly rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  refine List.forall_mem_singleton.mpr ?_
  exact ⟨Or.inl rfl, rfl, upper, loaded⟩

private theorem raw_read {input initial} {upper : BitVec 32} (pre : Pre bytes input initial) :
    rawAt input initial upper (afterRead initial upper) := by
  refine ⟨True.intro, .movReg64 .rax .rsi, result_decoded pre upper, ?_⟩
  intro af
  refine ⟨⟨.next (afterResult initial upper), []⟩, (), result_step pre upper af, ?_,
    ⟨fetch_at pre 9 rfl (by decide), .readOnly rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  simp

private theorem raw_result {input initial} {upper : BitVec 32} (pre : Pre bytes input initial) :
    rawAt input initial upper (afterResult initial upper) := by
  refine ⟨True.intro, .storeMem64 (.base .rdi) .rax, store_decoded pre upper, ?_⟩
  intro af
  refine ⟨⟨.next (afterStore initial upper), []⟩, (), store_step pre upper af, ?_,
    ⟨fetch_at pre 12 rfl (by decide), .store64 (value := initial.registers .rsi) ?_⟩,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  · simp
  · exact store_intent pre upper

private theorem raw_store {input initial} {upper : BitVec 32} (pre : Pre bytes input initial) :
    rawAt input initial upper (afterStore initial upper) := by
  refine ⟨True.intro, .legacy .ret, ret_decoded pre upper, ?_⟩
  intro af
  refine ⟨⟨.returned (finalState initial upper input.returnAddress),
    [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre upper af, ?_,
    ⟨fetch_at pre 15 rfl (by decide), .readOnly rfl⟩, True.intro⟩
  refine List.forall_mem_singleton.mpr ?_
  exact ⟨⟨rfl, rfl⟩, rfl, _, stored_stack pre upper⟩

theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  obtain ⟨upper, loaded⟩ := upper_read_exists pre
  refine ⟨rawInvariant initial upper, Or.inl rfl, ?_⟩
  intro ghost before inside
  change rawAt input initial upper before
  exact inside.elim
    (fun same => Eq.mpr (congrArg (rawAt input initial upper) same) (raw_initial pre))
    (fun tail => tail.elim
      (fun same => Eq.mpr (congrArg (rawAt input initial upper) same) (raw_copy pre))
      (fun tail => tail.elim
        (fun same => Eq.mpr (congrArg (rawAt input initial upper) same) (raw_add pre loaded))
        (fun tail => tail.elim
          (fun same => Eq.mpr (congrArg (rawAt input initial upper) same) (raw_read pre))
          (fun tail => tail.elim
            (fun same => Eq.mpr (congrArg (rawAt input initial upper) same) (raw_result pre))
            (fun same => Eq.mpr (congrArg (rawAt input initial upper) same) (raw_store pre))))))

theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state) ∧ RawPolicy bytes input initial := by
  obtain ⟨upper, loaded⟩ := upper_read_exists pre
  exact ⟨fun choices => ⟨_, executions pre loaded choices, final_post pre upper⟩, raw_policy pre⟩

/-- Independent accounting retains the true DATA4 width and original address;
the read value comes from the actual initial source/address snapshot. -/
theorem modeled_accounting {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 6 ∧
      result.reads = [⟨.data, input.address + 4, 4⟩, ⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 12 ∧
      ∃ upper, loadDWord initial.memory (input.address + 4) = .ok upper ∧
        result.state.registers .rdx = upper.setWidth 64 := by
  obtain ⟨upper, loaded⟩ := upper_read_exists pre
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre loaded choices)
  subst result
  refine ⟨rfl, rfl, rfl, upper, loaded, ?_⟩
  simp [finalState, afterStore, afterResult, afterRead, State.writeRegister]

theorem actual_flags {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.flags = addFlags64 initial.flags (initial.registers .rdi) 4 := by
  obtain ⟨upper, loaded⟩ := upper_read_exists pre
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre loaded choices)
  subst result
  rfl

/-- The upper DATA4 uses present owner authority at the actual pre-store
address. The later checked full64 store and RET retain one coherent world. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  obtain ⟨upper, loaded⟩ := upper_read_exists raw
  have currentAdd : WordResources64.Current resource.call resource.seed (afterAdd initial) :=
    pre.current.sameMemory rfl
  have currentResult : WordResources64.Current resource.call resource.seed (afterResult initial upper) :=
    pre.current.sameMemory rfl
  have span : Borrowing.Subregion (AddressSpace.wordRegion (resource.call.targetPointer + 4))
      (AddressSpace.qwordRegion resource.call.targetPointer) := (upper_address raw).2.2
  have permitted := current_subword_read currentAdd span
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rax)
      (afterResult initial upper) = some (resource.call.targetPointer, resource.argument) := by
    simp [Sequential.Instruction.storeIntent64, Address.eval, afterResult, afterRead,
      afterAdd, afterCopy, State.writeRegister, pre.pointer, pre.source]
  obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
    WordResources64.current_store64_step currentResult (store_decoded raw upper) intent false
  have storeEq : WordResources64.storeAfterLength (afterResult initial upper) evolved 3 =
      afterStore initial upper := by
    have same := Except.ok.inj (actualStore.symm.trans (store_step raw upper false))
    exact StepResult.next.inj (congrArg Observation.result same)
  change WordResources64.Current resource.call evolved
    (WordResources64.storeAfterLength (afterResult initial upper) evolved 3) at currentStore
  rw [storeEq] at currentStore
  have stackBinding : (afterStore initial upper).registers .rsp = resource.call.stack := by
    simpa [afterStore, afterResult, afterRead, afterAdd, afterCopy, State.writeRegister] using pre.stack
  have returnEq : WordResources64.returnAfter (afterStore initial upper) resource.call.returnAddress =
      finalState initial upper (resourceInput resource).returnAddress := by
    simp [WordResources64.returnAfter, finalState, afterStore, afterResult, afterRead,
      afterAdd, afterCopy, State.writeRegister, resourceInput, EDSL.StoreLoad64.resourceInput]
  have retActual (af : Bool) :=
    WordResources64.current_ret_step currentStore (ret_decoded raw upper) stackBinding af
  have fetch {before instruction} (offset : Nat)
      (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
      (inside : offset + instruction.length ≤ bytes.length) :
      FetchAllowed resource.call.code resource.call.bytes.length before instruction := by
    rw [pre.code, ← pre.entry]
    exact fetch_at raw offset pc inside
  refine ⟨(fun shared before => (shared = resource.seed ∧ before = initial) ∨
    (shared = resource.seed ∧ before = afterCopy initial) ∨
    (shared = resource.seed ∧ before = afterAdd initial) ∨
    (shared = resource.seed ∧ before = afterRead initial upper) ∨
    (shared = resource.seed ∧ before = afterResult initial upper) ∨
    (shared = evolved ∧ before = afterStore initial upper)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, same⟩ | ⟨sameShared, same⟩ | ⟨sameShared, same⟩ |
    ⟨sameShared, same⟩ | ⟨sameShared, same⟩ | ⟨sameShared, same⟩
  · subst shared; subst before
    refine ⟨pre.current, .movReg64 .rcx .rdi, copy_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterCopy initial), []⟩, resource.seed, copy_step raw af, ?_,
      ⟨fetch 0 (by simp) (by decide), .readOnly rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    simp
  · subst shared; subst before
    refine ⟨pre.current.sameMemory rfl, .addImm64 .rcx 4, add_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterAdd initial), []⟩, resource.seed, add_step raw af, ?_,
      ⟨fetch 3 rfl (by decide), .readOnly rfl⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    simp
  · subst shared; subst before
    refine ⟨currentAdd, .loadMem32 .rdx (.base .rcx), read_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterRead initial upper), [⟨.data, (resourceInput resource).address + 4, 4⟩]⟩,
      resource.seed, read_step raw loaded af, ?_, ⟨fetch 7 rfl (by decide), .readOnly rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    exact permitted
  · subst shared; subst before
    refine ⟨pre.current.sameMemory rfl, .movReg64 .rax .rsi, result_decoded raw upper, ?_⟩
    intro af
    refine ⟨⟨.next (afterResult initial upper), []⟩, resource.seed, result_step raw upper af, ?_,
      ⟨fetch 9 rfl (by decide), .readOnly rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    simp
  · subst shared; subst before
    refine ⟨currentResult, .storeMem64 (.base .rdi) .rax, store_decoded raw upper, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial upper), []⟩, evolved, store_step raw upper af, ?_,
      ⟨fetch 12 rfl (by decide), .store64 intent stored⟩,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩
    simp
  · subst shared; subst before
    refine ⟨currentStore, .legacy .ret, ret_decoded raw upper, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial upper (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, evolved, ret_step raw upper af, ?_,
      ⟨fetch 15 rfl (by decide), .readOnly rfl⟩, ?_⟩
    · refine List.forall_mem_singleton.mpr ?_
      refine ⟨?_, ?_⟩
      · change ReadAllowed resource.call evolved (afterStore initial upper)
          ⟨.stack, initial.registers .rsp, 8⟩
        simpa only [pre.stack] using readAllowed_of_strict (retActual af).2.2.1
      · simpa only [pre.stack] using (retActual af).2.2.2
    · change WordResources64.Current resource.call evolved
        (finalState initial upper (resourceInput resource).returnAddress)
      rw [← returnEq]
      exact (retActual af).2.1

theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result => Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result) ∧ ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned pre⟩

/-- Reusable domain construction supplies useful inputs independently of
the read, decoder, arithmetic, and success of this particular program. -/
theorem useful_domain : Nonvacuous (registered .storeReturnValue64) bytes :=
  domain_nonvacuous .storeReturnValue64 bytes (by decide) (by decide)

/-- Closed fresh client claim over all raw/current admissions and AF streams. -/
theorem claim : EDSL.Grading.Claim .storeReturnValue64 bytes :=
  ⟨⟨fun _ _ pre => raw_semantics pre, fun _ _ pre => resource_semantics pre⟩, useful_domain⟩

end EDSL.StoreReturnValue64Upper
