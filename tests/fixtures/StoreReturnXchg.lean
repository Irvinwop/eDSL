/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.OS.WordResources.Bridge
import EDSL.StoreReturn32.LowerBound

set_option warningAsError true

namespace EDSL.StoreReturnXchg
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading EDSL.Grading.Trace
open EDSL.Grading.Write32

/-- The exact GCC13 GNU23 `-Oz` output: exchange the full pointer with RAX,
store through RAX, and return through the original caller slot. -/
def bytes : List Byte := [0x48, 0x97, 0x89, 0x30, 0xc3]

def afterExchange (initial : State) : State :=
  { (initial.writeRegister .rax (initial.registers .rdi)).writeRegister
    .rdi (initial.registers .rax) with rip := initial.rip + 2 }

def afterStore (initial : State) : State :=
  { afterExchange initial with
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 4 }

def finalState (initial : State) (target : Word) : State :=
  { (afterStore initial).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

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

private theorem exchange_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.xchgRax64 .rdi) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

private theorem store_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterExchange initial) = .ok (.storeMem32 (.base .rax) .rsi) :=
  decode_from_code pre.code 2 (by decide) rfl rfl rfl

private theorem ret_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterStore initial) = .ok (.legacy .ret) :=
  decode_from_code (stored_code pre) 4 (by decide) rfl rfl rfl

private theorem exchange_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterExchange initial), []⟩ := by
  rw [step_eq_execute af (exchange_decoded pre)]
  rfl

private theorem store_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterExchange initial) = .ok ⟨.next (afterStore initial), []⟩ := by
  rw [step_eq_execute af (store_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [execute_storeMem32, Address.eval, afterExchange, afterStore, State.writeRegister,
    storeDWord, writable, Sequential.Instruction.length, BitVec.add_assoc]

private theorem stored_stack {input initial} (pre : Pre bytes input initial) :
    readWord (afterStore initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

private theorem ret_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterStore initial) =
      .ok ⟨.returned (finalState initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (afterStore initial).memory ((afterStore initial).registers .rsp) =
      .ok input.returnAddress := by
    simpa [afterStore, afterExchange, State.writeRegister] using stored_stack pre
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [afterStore, afterExchange, State.writeRegister]

/-- Independent pointer/store/caller contract for all admitted inputs. RDI is
volatile in this ABI; the exchange retains its original RAX value separately. -/
theorem final_post {input initial} (pre : Pre bytes input initial) :
    StoreReturn32.Post input initial (finalState initial input.returnAddress) := by
  have noWrap : input.address.toNat + 3 < 2^64 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp pre.target_addressable).1
  refine ⟨⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩, ?_⟩
  · have readback := load_after_write initial.memory input.address
      (input.argument.setWidth 32) pre.target_addressable
    simpa only [finalState, State.writeRegister, afterStore, pre.pointer, pre.source] using readback
  · intro query outside
    have large : 4 ≤ (query - input.address).toNat := by
      have excluded := mt (AddressSpace.word_contains_iff input.address query noWrap).mpr outside
      omega
    exact writeDWord_frame initial.memory _ query _ (by rwa [pre.pointer])
  · simp [finalState, afterStore, afterExchange, State.writeRegister]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same; subst register; simp [calleeSaved] at member
    have notRdi : register ≠ .rdi := by
      intro same; subst register; simp [calleeSaved] at member
    have notRax : register ≠ .rax := by
      intro same; subst register; simp [calleeSaved] at member
    simp [finalState, afterStore, afterExchange, State.writeRegister, notStack, notRdi, notRax]
  · simpa [finalState, afterStore, afterExchange, State.writeRegister] using pre.pointer

/-- Every AF stream executes exactly the three actual instructions. -/
theorem executions {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial input.returnAddress, 3, [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (exchange_step pre (choices 0))
    (Sequential.Executes.next (store_step pre ((choices.drop 1) 0))
      (Sequential.Executes.ret (ret_step pre (((choices.drop 1).drop 1) 0))))
  simpa only [Result.prepend, List.nil_append] using execution

private theorem fetch_at {input initial before instruction} (pre : Pre bytes input initial)
    (offset : Nat) (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    FetchAllowed initial.rip bytes.length before instruction := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 5 ≤ 2^64 at limit
  change offset + instruction.length ≤ 5 at span
  have small : offset < 2^64 := by omega
  have total : initial.rip.toNat + offset < 2^64 := by omega
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 5
  rw [pc, natural]
  omega

/-- Actual prefixes satisfy the existing fixed-target/current-fetch policy;
no direct shape or instruction count is an admission premise. -/
theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  refine ⟨(fun (_ : Unit) state => state = initial ∨ state = afterExchange initial ∨
    state = afterStore initial), Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same | same
  · subst before
    refine ⟨True.intro, .xchgRax64 .rdi, exchange_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterExchange initial), []⟩, (), exchange_step pre af, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · simp
    · exact ⟨fetch_at pre 0 (by simp) (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .storeMem32 (.base .rax) .rsi, store_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, (), store_step pre af, ?_, ?_, Or.inr (Or.inr rfl)⟩
    · simp
    · refine ⟨fetch_at pre 2 rfl (by decide), Or.inr ⟨(initial.registers .rsi).setWidth 32, ?_⟩⟩
      simp [Sequential.Instruction.storeIntent, Address.eval, afterExchange, State.writeRegister, pre.pointer]
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre af, ?_, ?_, True.intro⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, stored_stack pre⟩
    · exact ⟨fetch_at pre 4 rfl (by decide), Or.inl rfl⟩

theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => StoreReturn32.Post input initial result.state) ∧
      RawPolicy bytes input initial :=
  ⟨fun choices => ⟨_, executions pre choices, final_post pre⟩, raw_policy pre⟩

/-- The exchange preserves the same current OS world and stack binding. The
ordinary store is the actual checked owner mutation, followed by current RET. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  obtain ⟨exchanged, actualExchange, currentExchange, assigned, _, preservedExchange, _, _, _⟩ :=
    WordResources.current_xchgRax64_step pre.current (exchange_decoded raw) false
  have exchangeEq : exchanged = afterExchange initial := by
    have same := Except.ok.inj (actualExchange.symm.trans (exchange_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [exchangeEq] at currentExchange assigned preservedExchange
  have intent : Sequential.Instruction.storeIntent (.storeMem32 (.base .rax) .rsi)
      (afterExchange initial) = some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
    simp only [Sequential.Instruction.storeIntent, Address.eval]
    rw [assigned, pre.pointer, preservedExchange .rsi (by decide) (by decide)]
  obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
    WordResources.current_store_step currentExchange (store_decoded raw) intent false
  have storeEq : WordResources.storeAfterLength (afterExchange initial) evolved
      (Sequential.Instruction.storeMem32 (.base .rax) .rsi).length = afterStore initial := by
    have same := Except.ok.inj (actualStore.symm.trans (store_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [storeEq] at currentStore
  have stackBinding : (afterStore initial).registers .rsp = resource.call.stack := by
    have frame := congrArg (fun state : State => state.registers .rsp) storeEq
    change (afterExchange initial).registers .rsp = (afterStore initial).registers .rsp at frame
    exact frame.symm.trans ((preservedExchange .rsp (by decide) (by decide)).trans pre.stack)
  have returnAfterEq : WordResources.returnAfter (afterStore initial)
      resource.call.returnAddress = finalState initial (resourceInput resource).returnAddress := by
    simp [WordResources.returnAfter, finalState, afterStore, afterExchange, State.writeRegister, resourceInput]
  have retActual (af : Bool) :=
    WordResources.current_ret_step currentStore (ret_decoded raw) stackBinding af
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
    (shared = resource.seed ∧ before = afterExchange initial) ∨
    (shared = evolved ∧ before = afterStore initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, .xchgRax64 .rdi, exchange_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterExchange initial), []⟩, resource.seed, exchange_step raw af, ?_, ?_,
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch 0 (by simp) (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentExchange, .storeMem32 (.base .rax) .rsi, store_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, evolved, store_step raw af, ?_, ?_,
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch 2 rfl (by decide), .store intent stored⟩
  · subst shared
    subst before
    refine ⟨currentStore, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, evolved, ?_, ?_,
      ⟨fetch 4 rfl (by decide), .readOnly rfl⟩, currentReturn⟩
    · simpa only [returnAfterEq, pre.stack] using (retActual af).1
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      refine ⟨?_, ?_⟩
      · exact ⟨pre.stack, rfl, pre.stack ▸ (retActual af).2.2.1⟩
      · simpa only [pre.stack] using (retActual af).2.2.2

theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result => StoreReturn32.Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result) ∧ ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned⟩

/-- Accounting and the old volatile RAX value are consequences of the same
actual execution, independently of the registered mathematical Post. -/
theorem modeled_accounting {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 3 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 8 ∧ result.state.registers .rdi = initial.registers .rax := by
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre choices)
  subst result
  simp [finalState, afterStore, afterExchange, State.writeRegister]

theorem useful_domain : Nonvacuous (registered .storeReturn32) bytes :=
  domain_nonvacuous .storeReturn32 bytes (by decide) (by decide)

/-- Closed client submission, outside the grader's trusted import snapshot. -/
theorem claim : EDSL.Grading.Claim .storeReturn32 bytes :=
  ⟨⟨fun _ _ pre => raw_semantics pre, fun _ _ pre => resource_semantics pre⟩, useful_domain⟩

/-- This new compiler client attains the existing conditional minimum; costs
remain modeled instructions, including RET, under the unchanged raw policy. -/
theorem minimum_attained {input initial choices result} (pre : Pre bytes input initial)
    (useful : Useful input) (needed : initial.registers .rax ≠ input.address)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 3 ∧ 3 ≤ result.instructions :=
  ⟨(modeled_accounting pre execution).1,
    StoreReturn32.claim_minimum claim pre useful needed execution⟩

end EDSL.StoreReturnXchg
