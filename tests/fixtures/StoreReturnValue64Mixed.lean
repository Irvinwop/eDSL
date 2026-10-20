/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.Grading.StoreReturnValue64.Resources

set_option warningAsError true

namespace EDSL.StoreReturnValue64Mixed
open EDSL X86 X86.Sequential OS
open EDSL.Grading EDSL.Grading.Trace EDSL.Grading.StoreReturnValue64

/-- XOR EAX,EAX; MOV RAX,RSI; MOV QWORD[RDI],RAX;
MOV DWORD[RDI],EAX; RET. Both ordinary stores execute. -/
def bytes : List Byte := [0x31, 0xc0, 0x48, 0x89, 0xf0, 0x48, 0x89, 0x07, 0x89, 0x07, 0xc3]

def afterXor (initial : State) (af : Bool) : State :=
  { initial.writeRegister .rax 0 with
    rip := initial.rip + 2
    flags := logicalFlags32 initial.flags 0 af }

def afterCopy (initial : State) (af : Bool) : State :=
  { (afterXor initial af).writeRegister .rax (initial.registers .rsi) with rip := initial.rip + 5 }

def afterWide (initial : State) (af : Bool) : State :=
  { afterCopy initial af with
    memory := writeQWordUnchecked initial.memory (initial.registers .rdi) (initial.registers .rsi)
    rip := initial.rip + 8 }

def afterNarrow (initial : State) (af : Bool) : State :=
  { afterWide initial af with
    memory := writeDWordUnchecked (afterWide initial af).memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 10 }

def finalState (initial : State) (af : Bool) (target : Word) : State :=
  { (afterNarrow initial af).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

/-- This equality concerns byte contents only: the second instruction still
has a genuine four-byte store intent and a separate checked OS mutation. -/
theorem same_low_store (memory : Memory) (address value : Word) :
    writeDWordUnchecked (writeQWordUnchecked memory address value) address (value.setWidth 32) =
      writeQWordUnchecked memory address value := by
  have reads : storedDWordByte (writeQWordUnchecked memory address value) address (value.setWidth 32) =
      storedQWordByte memory address value := by
    funext query
    simp only [storedDWordByte, storedQWordByte]
    split <;> simp_all [writeQWordUnchecked, storedQWordByte]
    all_goals exact BitVec.extractLsb'_setWidth_of_le (by decide)
  cases memory
  simp only [writeDWordUnchecked, writeQWordUnchecked] at reads ⊢
  rw [reads]

private theorem low_writable {memory : Memory} {address : Word}
    (allowed : canStoreQWord memory address = true) : canStoreDWord memory address = true := by
  simp only [canStoreQWord, qwordAddressable, qwordWritable, Bool.and_eq_true,
    decide_eq_true_eq] at allowed
  simp only [canStoreDWord, dwordAddressable, dwordWritable, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨⟨by omega, allowed.1.2.1.1.1.1⟩,
    allowed.2.1.1.1.1.1, allowed.2.2.1.1.1.1⟩

private theorem decode_from_code {memory base} (code : CodeAt memory base bytes)
    (offset : Nat) (inside : offset < bytes.length) {state instruction}
    (mem : state.memory = memory) (pc : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction :=
  decodeAt_transport (code_fetch_transport code (by decide) offset inside state mem pc) decoded

private theorem wide_code {input initial} (pre : Pre bytes input initial) (af : Bool) :
    CodeAt (afterWide initial af).memory initial.rip bytes := by
  apply writeQWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

private theorem narrow_memory (initial : State) (af : Bool) :
    (afterNarrow initial af).memory = (afterWide initial af).memory :=
  same_low_store _ _ _

private theorem xor_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.xorSelf32 .rax) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

private theorem copy_decoded {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.decodeAt (afterXor initial af) = .ok (.movReg64 .rax .rsi) :=
  decode_from_code pre.code 2 (by decide) rfl rfl rfl

private theorem wide_decoded {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.decodeAt (afterCopy initial af) = .ok (.storeMem64 (.base .rdi) .rax) :=
  decode_from_code pre.code 5 (by decide) rfl rfl rfl

private theorem narrow_decoded {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.decodeAt (afterWide initial af) = .ok (.storeMem32 (.base .rdi) .rax) :=
  decode_from_code (wide_code pre af) 8 (by decide) rfl rfl rfl

private theorem ret_decoded {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.decodeAt (afterNarrow initial af) = .ok (.legacy .ret) :=
  decode_from_code (wide_code pre af) 10 (by decide) (narrow_memory initial af) rfl rfl

private theorem xor_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterXor initial af), []⟩ := by
  rw [step_eq_execute af (xor_decoded pre)]
  rfl

private theorem copy_step {input initial} (pre : Pre bytes input initial) (first af : Bool) :
    Sequential.step af (afterXor initial first) = .ok ⟨.next (afterCopy initial first), []⟩ := by
  rw [step_eq_execute af (copy_decoded pre first)]
  simp [execute_movReg64, afterCopy, afterXor, State.writeRegister, BitVec.add_assoc]

private theorem wide_step {input initial} (pre : Pre bytes input initial) (first af : Bool) :
    Sequential.step af (afterCopy initial first) = .ok ⟨.next (afterWide initial first), []⟩ := by
  rw [step_eq_execute af (wide_decoded pre first)]
  have writable : canStoreQWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [execute_storeMem64, afterWide, afterCopy, afterXor, State.writeRegister,
    Address.eval, storeQWord, writable, Sequential.Instruction.length, BitVec.add_assoc]

private theorem narrow_writable {input initial} (pre : Pre bytes input initial) (first : Bool) :
    canStoreDWord (afterWide initial first).memory (initial.registers .rdi) = true := by
  apply low_writable
  have old := pre.writable
  simp only [canStoreQWord, qwordWritable, Bool.and_eq_true] at old
  simpa [afterWide, canStoreQWord, qwordWritable, writeQWordUnchecked,
    storedQWordByte, pre.pointer] using And.intro old.1 old.2.1

private theorem narrow_step {input initial} (pre : Pre bytes input initial) (first af : Bool) :
    Sequential.step af (afterWide initial first) = .ok ⟨.next (afterNarrow initial first), []⟩ := by
  rw [step_eq_execute af (narrow_decoded pre first), execute_storeMem32]
  change (do
    let memory ← storeDWord (afterWide initial first).memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    pure (⟨.next { afterWide initial first with
      memory := memory
      rip := (initial.rip + 8) + 2 }, []⟩ : Observation)) = _
  simp only [storeDWord, narrow_writable pre first, ↓reduceIte, BitVec.add_assoc]
  rfl

private theorem stored_stack {input initial} (pre : Pre bytes input initial) (af : Bool) :
    readWord (afterNarrow initial af).memory (initial.registers .rsp) = .ok input.returnAddress := by
  rw [narrow_memory]
  apply (readWord_congr _ _ _ (writeQWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

private theorem ret_step {input initial} (pre : Pre bytes input initial) (first af : Bool) :
    Sequential.step af (afterNarrow initial first) =
      .ok ⟨.returned (finalState initial first input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre first)]
  have stack : readWord (afterNarrow initial first).memory ((afterNarrow initial first).registers .rsp) =
      .ok input.returnAddress := by
    simpa [afterNarrow, afterWide, afterCopy, afterXor, State.writeRegister] using stored_stack pre first
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [afterNarrow, afterWide, afterCopy, afterXor, State.writeRegister]

/-- All AF streams execute all five instructions; only RET records an operand read. -/
theorem executions {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial (choices 0) input.returnAddress, 5,
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (xor_step pre (choices 0))
    (Sequential.Executes.next (copy_step pre (choices 0) (choices.drop 1 0))
      (Sequential.Executes.next (wide_step pre (choices 0) ((choices.drop 1).drop 1 0))
        (Sequential.Executes.next (narrow_step pre (choices 0) (((choices.drop 1).drop 1).drop 1 0))
          (Sequential.Executes.ret (ret_step pre (choices 0) ((((choices.drop 1).drop 1).drop 1).drop 1 0))))))
  simpa only [Result.prepend, List.nil_append] using execution

private theorem final_value {input initial} (pre : Pre bytes input initial) (af : Bool) :
    loadQWord (finalState initial af input.returnAddress).memory input.address = .ok input.argument := by
  change loadQWord (afterNarrow initial af).memory input.address = .ok input.argument
  rw [narrow_memory]
  simpa only [afterWide, pre.pointer, pre.source] using
    qword_load_after_write initial.memory input.address input.argument pre.target_addressable

private theorem final_outside {input initial} (pre : Pre bytes input initial) (af : Bool) :
    ∀ query, 8 ≤ (query - input.address).toNat →
      (finalState initial af input.returnAddress).memory.read query = initial.memory.read query := by
  intro query outside
  change (afterNarrow initial af).memory.read query = initial.memory.read query
  rw [narrow_memory]
  exact writeQWord_frame initial.memory _ query _ (by simpa only [pre.pointer] using outside)

private theorem final_preserved (initial : State) (af : Bool) (target : Word) :
    ∀ register ∈ calleeSaved, (finalState initial af target).registers register = initial.registers register := by
  intro register member
  have notStack : register ≠ .rsp := fun same =>
    (by decide : Register.rsp ∉ calleeSaved) (same ▸ member)
  have notRax : register ≠ .rax := fun same =>
    (by decide : Register.rax ∉ calleeSaved) (same ▸ member)
  change (if register = .rsp then initial.registers .rsp + 8 else
    if register = .rax then initial.registers .rsi else
    if register = .rax then 0 else initial.registers register) = initial.registers register
  simp only [notStack, notRax, ↓reduceIte]

/-- Full64 value and ordinary SysV/RET frame, independent of instruction
counts and operand traces. The arbitrary XOR AF choice is retained. -/
theorem final_post {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Post input initial (finalState initial af input.returnAddress) := by
  exact ⟨pre.source, final_value pre af, final_outside pre af, rfl, rfl, rfl, rfl,
    final_preserved initial af input.returnAddress, logicalFlags32_preserves ..⟩

private theorem fetch_at {input : Input} {initial before : State} {instruction : Sequential.Instruction}
    (pre : Pre bytes input initial) (offset : Nat)
    (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    FetchAllowed initial.rip bytes.length before instruction := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 11 ≤ 2^64 at limit
  change offset + instruction.length ≤ 11 at span
  have offsetLt : offset < 11 :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right positive) span
  have total : initial.rip.toNat + offset < 2^64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left offsetLt _) limit
  have small : offset < 2^64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) total
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 11
  rw [pc, natural]
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left span _

/-- Every actual prefix, including both store intents, is permitted. This
invariant ranges over both actual XOR flag outcomes. -/
private def rawInvariant (initial : State) (_ : Unit) (before : State) : Prop :=
  before = initial ∨
    (∃ af, before = afterXor initial af) ∨ (∃ af, before = afterCopy initial af) ∨
    (∃ af, before = afterWide initial af) ∨ (∃ af, before = afterNarrow initial af)

private def rawAt (input : Input) (initial before : State) : Prop :=
  (rawRules bytes input initial).Current () before ∧
    ∃ instruction, Sequential.decodeAt before = .ok instruction ∧
      ∀ af, ∃ observation evolved,
        step af before = .ok observation ∧
        (∀ read ∈ observation.reads,
          (rawRules bytes input initial).ReadAllowed () before read ∧ OperandReadSucceeds before read) ∧
        (rawRules bytes input initial).Effect () before instruction observation evolved ∧
        match observation.result with
        | .next after => rawInvariant initial evolved after
        | .returned after => (rawRules bytes input initial).Current evolved after
        | .atomic _ _ | .syscall _ => False

theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  refine ⟨rawInvariant initial, Or.inl rfl, ?_⟩
  intro ghost before inside
  change rawAt input initial before
  rcases inside with same | ⟨first, same⟩ | ⟨first, same⟩ | ⟨first, same⟩ | ⟨first, same⟩
  · subst before
    refine ⟨True.intro, .xorSelf32 .rax, xor_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterXor initial af), []⟩, (), xor_step pre af, ?_,
      ⟨fetch_at pre 0 (by simp) (by decide), .readOnly rfl⟩, Or.inr (Or.inl ⟨af, rfl⟩)⟩
    simp
  · subst before
    refine ⟨True.intro, .movReg64 .rax .rsi, copy_decoded pre first, ?_⟩
    intro af
    refine ⟨⟨.next (afterCopy initial first), []⟩, (), copy_step pre first af, ?_,
      ⟨fetch_at pre 2 rfl (by decide), .readOnly rfl⟩, Or.inr (Or.inr (Or.inl ⟨first, rfl⟩))⟩
    simp
  · subst before
    refine ⟨True.intro, .storeMem64 (.base .rdi) .rax, wide_decoded pre first, ?_⟩
    intro af
    refine ⟨⟨.next (afterWide initial first), []⟩, (), wide_step pre first af, ?_,
      ⟨fetch_at pre 5 rfl (by decide), .store64 (value := initial.registers .rsi) ?_⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨first, rfl⟩)))⟩
    · simp
    · change some (initial.registers .rdi, initial.registers .rsi) =
        some (input.address, initial.registers .rsi)
      rw [pre.pointer]
  · subst before
    refine ⟨True.intro, .storeMem32 (.base .rdi) .rax, narrow_decoded pre first, ?_⟩
    intro af
    refine ⟨⟨.next (afterNarrow initial first), []⟩, (), narrow_step pre first af, ?_,
      ⟨fetch_at pre 8 rfl (by decide), .store32 (address := input.address)
        (value := (initial.registers .rsi).setWidth 32) ?_ ?_⟩,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨first, rfl⟩)))⟩
    · simp
    · change some (initial.registers .rdi, (initial.registers .rsi).setWidth 32) =
        some (input.address, (initial.registers .rsi).setWidth 32)
      rw [pre.pointer]
    · change input.address.toNat ≤ input.address.toNat ∧ input.address.toNat + 4 ≤ input.address.toNat + 8
      exact ⟨Nat.le_refl _, Nat.add_le_add_left (by decide : 4 ≤ 8) _⟩
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre first, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial first input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre first af, ?_,
      ⟨fetch_at pre 10 rfl (by decide), .readOnly rfl⟩, True.intro⟩
    refine List.forall_mem_singleton.mpr ?_
    exact ⟨⟨rfl, rfl⟩, rfl, _, stored_stack pre first⟩

theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state) ∧ RawPolicy bytes input initial :=
  ⟨fun choices => ⟨_, executions pre choices, final_post pre (choices 0)⟩, raw_policy pre⟩

/-- Accounting is derived from the same actual execution and is not an
admission, Post, or grader shape constraint. -/
theorem modeled_accounting {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 5 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 8 := by
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre choices)
  subst result
  exact ⟨rfl, rfl, rfl⟩

theorem actual_flags {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.flags = logicalFlags32 initial.flags 0 (choices 0) := by
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre choices)
  subst result
  rfl

private theorem wide_intent {resource initial} (pre : ResourcePre bytes resource initial)
    (first : Bool) :
    Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rax) (afterCopy initial first) =
      some (resource.call.targetPointer, resource.argument) := by
  change some (initial.registers .rdi, initial.registers .rsi) =
    some (resource.call.targetPointer, resource.argument)
  rw [pre.pointer, pre.source]

private theorem narrow_intent {resource initial} (pre : ResourcePre bytes resource initial)
    (first : Bool) :
    Sequential.Instruction.storeIntent (.storeMem32 (.base .rdi) .rax) (afterWide initial first) =
      some (resource.call.targetPointer, resource.argument.setWidth 32) := by
  change some (initial.registers .rdi, (initial.registers .rsi).setWidth 32) =
    some (resource.call.targetPointer, resource.argument.setWidth 32)
  rw [pre.pointer, pre.source]

private theorem stack_binding {resource initial} (pre : ResourcePre bytes resource initial)
    (first : Bool) : (afterNarrow initial first).registers .rsp = resource.call.stack := by
  simpa [afterNarrow, afterWide, afterCopy, afterXor, State.writeRegister] using pre.stack

private theorem return_eq {resource initial} (_pre : ResourcePre bytes resource initial)
    (first : Bool) : WordResources64.returnAfter (afterNarrow initial first)
      resource.call.returnAddress = finalState initial first (resourceInput resource).returnAddress := by
  simp [WordResources64.returnAfter, finalState, afterNarrow, afterWide, afterCopy,
    afterXor, State.writeRegister, resourceInput, EDSL.StoreLoad64.resourceInput]

private theorem resource_fetch {resource initial before instruction}
    (pre : ResourcePre bytes resource initial) (offset : Nat)
    (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (inside : offset + instruction.length ≤ bytes.length) :
    FetchAllowed resource.call.code resource.call.bytes.length before instruction := by
  rw [pre.code, ← pre.entry]
  exact fetch_at pre.machine offset pc inside

/-- The actual wide and narrow stores each perform their own checked mutation.
Every prefix keeps the corresponding same evolved world and complete Current8. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  have currentCopy (first : Bool) : WordResources64.Current resource.call resource.seed (afterCopy initial first) :=
    pre.current.sameMemory rfl
  obtain ⟨wideWorld, storedWide, actualWide, wideCurrent, _, _⟩ :=
    WordResources64.current_store64_step (currentCopy false) (wide_decoded raw false) (wide_intent pre false) false
  have wideEq : WordResources64.storeAfterLength (afterCopy initial false) wideWorld 3 = afterWide initial false := by
    have same := Except.ok.inj (actualWide.symm.trans (wide_step raw false false))
    exact StepResult.next.inj (congrArg Observation.result same)
  change WordResources64.Current resource.call wideWorld
    (WordResources64.storeAfterLength (afterCopy initial false) wideWorld 3) at wideCurrent
  rw [wideEq] at wideCurrent
  have currentWide (first : Bool) : WordResources64.Current resource.call wideWorld (afterWide initial first) :=
    wideCurrent.sameMemory rfl
  have span : Borrowing.Subregion (AddressSpace.wordRegion resource.call.targetPointer)
      (AddressSpace.qwordRegion resource.call.targetPointer) := by
    constructor
    · exact Nat.le_refl _
    · change resource.call.targetPointer.toNat + 4 ≤ resource.call.targetPointer.toNat + 8
      exact Nat.add_le_add_left (by decide : 4 ≤ 8) _
  obtain ⟨narrowWorld, storedNarrow, actualNarrow, narrowCurrent, _, _, _⟩ :=
    WordResources64.current_store32_step (currentWide false) (narrow_decoded raw false)
      (narrow_intent pre false) span false
  have narrowEq : WordResources64.storeAfterLength (afterWide initial false) narrowWorld 2 =
      afterNarrow initial false := by
    have same := Except.ok.inj (actualNarrow.symm.trans (narrow_step raw false false))
    exact StepResult.next.inj (congrArg Observation.result same)
  change WordResources64.Current resource.call narrowWorld
    (WordResources64.storeAfterLength (afterWide initial false) narrowWorld 2) at narrowCurrent
  rw [narrowEq] at narrowCurrent
  have currentNarrow (first : Bool) :
      WordResources64.Current resource.call narrowWorld (afterNarrow initial first) :=
    narrowCurrent.sameMemory rfl
  have retActual (first af : Bool) :=
    WordResources64.current_ret_step (currentNarrow first) (ret_decoded raw first) (stack_binding pre first) af
  refine ⟨(fun shared before => (shared = resource.seed ∧ before = initial) ∨
    (shared = resource.seed ∧ ∃ first, before = afterXor initial first) ∨
    (shared = resource.seed ∧ ∃ first, before = afterCopy initial first) ∨
    (shared = wideWorld ∧ ∃ first, before = afterWide initial first) ∨
    (shared = narrowWorld ∧ ∃ first, before = afterNarrow initial first)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, same⟩ | ⟨sameShared, first, same⟩ |
    ⟨sameShared, first, same⟩ | ⟨sameShared, first, same⟩ | ⟨sameShared, first, same⟩
  · subst shared; subst before
    refine ⟨pre.current, .xorSelf32 .rax, xor_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterXor initial af), []⟩, resource.seed, xor_step raw af, ?_,
      ⟨resource_fetch pre 0 (by simp) (by decide), .readOnly rfl⟩, Or.inr (Or.inl ⟨rfl, af, rfl⟩)⟩
    simp
  · subst shared; subst before
    refine ⟨pre.current.sameMemory rfl, .movReg64 .rax .rsi, copy_decoded raw first, ?_⟩
    intro af
    refine ⟨⟨.next (afterCopy initial first), []⟩, resource.seed, copy_step raw first af, ?_,
      ⟨resource_fetch pre 2 rfl (by decide), .readOnly rfl⟩, Or.inr (Or.inr (Or.inl ⟨rfl, first, rfl⟩))⟩
    simp
  · subst shared; subst before
    refine ⟨currentCopy first, .storeMem64 (.base .rdi) .rax, wide_decoded raw first, ?_⟩
    intro af
    refine ⟨⟨.next (afterWide initial first), []⟩, wideWorld, wide_step raw first af, ?_,
      ⟨resource_fetch pre 5 rfl (by decide), .store64 (wide_intent pre first) storedWide⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, first, rfl⟩)))⟩
    simp
  · subst shared; subst before
    refine ⟨currentWide first, .storeMem32 (.base .rdi) .rax, narrow_decoded raw first, ?_⟩
    intro af
    refine ⟨⟨.next (afterNarrow initial first), []⟩, narrowWorld, narrow_step raw first af, ?_,
      ⟨resource_fetch pre 8 rfl (by decide), .store32 (narrow_intent pre first) span storedNarrow⟩,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, first, rfl⟩)))⟩
    simp
  · subst shared; subst before
    refine ⟨currentNarrow first, .legacy .ret, ret_decoded raw first, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial first (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, narrowWorld, ret_step raw first af, ?_,
      ⟨resource_fetch pre 10 rfl (by decide), .readOnly rfl⟩, ?_⟩
    · refine List.forall_mem_singleton.mpr ?_
      refine ⟨?_, ?_⟩
      · change ReadAllowed resource.call narrowWorld (afterNarrow initial first)
          ⟨.stack, initial.registers .rsp, 8⟩
        simpa only [pre.stack] using readAllowed_of_strict (retActual first af).2.2.1
      · simpa only [pre.stack] using (retActual first af).2.2.2
    · change WordResources64.Current resource.call narrowWorld
        (finalState initial first (resourceInput resource).returnAddress)
      rw [← return_eq pre first]
      exact (retActual first af).2.1

theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result => Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result) ∧ ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned pre⟩

/-- Candidate-independent current/raw inputs inhabit the full registered
domain, without interpreting this program or narrowing its preconditions. -/
theorem useful_domain : Nonvacuous (registered .storeReturnValue64) bytes :=
  domain_nonvacuous .storeReturnValue64 bytes (by decide) (by decide)

/-- Closed fresh client claim, kept outside the grader's trusted imports. -/
theorem claim : EDSL.Grading.Claim .storeReturnValue64 bytes :=
  ⟨⟨fun _ _ pre => raw_semantics pre, fun _ _ pre => resource_semantics pre⟩, useful_domain⟩

end EDSL.StoreReturnValue64Mixed
