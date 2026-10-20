/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.OS.WordResources.Bridge

set_option warningAsError true

namespace EDSL.WriteMovesSupported
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading EDSL.Grading.Trace
open EDSL.Grading.Write32

/-- MOV ECX,ESI; MOV [RDI],ECX; MOV ECX,[RDI]; RET. -/
def bytes : List Byte := [0x89, 0xf1, 0x89, 0x0f, 0x8b, 0x0f, 0xc3]

def afterMov (initial : State) : State :=
  { initial.writeRegister .rcx (((initial.registers .rsi).setWidth 32).setWidth 64) with
    rip := initial.rip + 2 }

def afterStore (initial : State) : State :=
  { afterMov initial with
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 4 }

/-- Readback rewrites ECX with the same zero-extended word just stored. -/
def afterLoad (initial : State) : State :=
  { afterStore initial with rip := initial.rip + 6 }

def finalState (initial : State) (target : Word) : State :=
  { (afterLoad initial).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

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

private theorem mov_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.movReg32 .rcx .rsi) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

private theorem store_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterMov initial) = .ok (.storeMem32 (.base .rdi) .rcx) :=
  decode_from_code pre.code 2 (by decide) rfl rfl rfl

private theorem load_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterStore initial) = .ok (.loadMem32 .rcx (.base .rdi)) :=
  decode_from_code (stored_code pre) 4 (by decide) rfl rfl rfl

private theorem ret_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterLoad initial) = .ok (.legacy .ret) :=
  decode_from_code (stored_code pre) 6 (by decide) rfl rfl rfl

private theorem mov_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterMov initial), []⟩ := by
  rw [step_eq_execute af (mov_decoded pre)]
  rfl

private theorem store_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterMov initial) = .ok ⟨.next (afterStore initial), []⟩ := by
  rw [step_eq_execute af (store_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [execute_storeMem32, Address.eval, afterMov, afterStore, State.writeRegister,
    storeDWord, writable, Sequential.Instruction.length, BitVec.add_assoc]

private theorem stored_value {input initial} (pre : Pre bytes input initial) :
    loadDWord (afterStore initial).memory (initial.registers .rdi) =
      .ok ((initial.registers .rsi).setWidth 32) := by
  apply load_after_write
  simpa only [pre.pointer] using pre.target_addressable

private theorem load_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterStore initial) = .ok ⟨.next (afterLoad initial),
      [⟨.data, initial.registers .rdi, 4⟩]⟩ := by
  rw [step_eq_execute af (load_decoded pre)]
  have loaded : loadDWord (afterStore initial).memory
      (Address.base .rdi |>.eval (afterStore initial)) =
      .ok ((initial.registers .rsi).setWidth 32) := by
    simpa [Address.eval, afterStore, afterMov, State.writeRegister] using stored_value pre
  simp only [execute_loadMem32, loaded, ok_bind, pure_ok]
  simp [afterLoad, afterStore, afterMov, State.writeRegister, Address.eval,
    Sequential.Instruction.length, BitVec.add_assoc]
  funext register
  by_cases same : register = .rcx <;> simp [same]

private theorem stored_stack {input initial} (pre : Pre bytes input initial) :
    readWord (afterLoad initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

private theorem ret_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterLoad initial) =
      .ok ⟨.returned (finalState initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (afterLoad initial).memory ((afterLoad initial).registers .rsp) =
      .ok input.returnAddress := by
    simpa [afterLoad, afterStore, afterMov, State.writeRegister] using stored_stack pre
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [afterLoad, afterStore, afterMov, State.writeRegister]

/-- Independent mathematical store and ABI postcondition for all original
arguments, old words, full-width pointers, source high bits and initial flags. -/
theorem final_post {input initial} (pre : Pre bytes input initial) :
    Post input initial (finalState initial input.returnAddress) := by
  have noWrap : input.address.toNat + 3 < 2^64 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp pre.target_addressable).1
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · have readback := load_after_write initial.memory input.address
      (input.argument.setWidth 32) pre.target_addressable
    simpa only [finalState, State.writeRegister, afterLoad, afterStore,
      pre.pointer, pre.source] using readback
  · intro query outside
    have large : 4 ≤ (query - input.address).toNat := by
      have excluded := mt (AddressSpace.word_contains_iff input.address query noWrap).mpr outside
      omega
    exact writeDWord_frame initial.memory _ query _ (by rwa [pre.pointer])
  · simp [finalState, State.writeRegister, afterLoad, afterStore, afterMov]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same
      subst register
      simp [calleeSaved] at member
    have notRcx : register ≠ .rcx := by
      intro same
      subst register
      simp [calleeSaved] at member
    simp [finalState, State.writeRegister, afterLoad, afterStore, afterMov, notStack, notRcx]

/-- Every AF stream retires exactly four instructions and observes exactly
the current target word and the original caller's eight-byte return slot. -/
theorem executions {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial input.returnAddress, 4,
        [⟨.data, initial.registers .rdi, 4⟩, ⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution :=
    Sequential.Executes.next (mov_step pre (choices 0))
      (Sequential.Executes.next (store_step pre ((choices.drop 1) 0))
        (Sequential.Executes.next (load_step pre (((choices.drop 1).drop 1) 0))
          (Sequential.Executes.ret (ret_step pre ((((choices.drop 1).drop 1).drop 1) 0)))))
  simpa only [Result.prepend, List.nil_append, List.cons_append] using execution

private theorem fetch_at {input initial before instruction} (pre : Pre bytes input initial)
    (offset : Nat) (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    FetchAllowed initial.rip bytes.length before instruction := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 7 ≤ 2^64 at limit
  change offset + instruction.length ≤ 7 at span
  have small : offset < 2^64 := by omega
  have total : initial.rip.toNat + offset < 2^64 := by omega
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 7
  rw [pc, natural]
  omega

/-- Every actual raw prefix uses the current code and real operand success.
The constructed invariant is evidence, with no extra admission assumption. -/
theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  refine ⟨(fun (_ : Unit) state => state = initial ∨ state = afterMov initial ∨
    state = afterStore initial ∨ state = afterLoad initial), Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same | same | same
  · subst before
    refine ⟨True.intro, .movReg32 .rcx .rsi, mov_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterMov initial), []⟩, (), mov_step pre af, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · simp
    · exact ⟨fetch_at pre 0 (by simp) (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .storeMem32 (.base .rdi) .rcx, store_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, (), store_step pre af, ?_, ?_,
      Or.inr (Or.inr (Or.inl rfl))⟩
    · simp
    · refine ⟨fetch_at pre 2 rfl (by decide), Or.inr ⟨(initial.registers .rsi).setWidth 32, ?_⟩⟩
      simp [Sequential.Instruction.storeIntent, Address.eval, afterMov, State.writeRegister,
        pre.pointer]
  · subst before
    refine ⟨True.intro, .loadMem32 .rcx (.base .rdi), load_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterLoad initial), [⟨.data, initial.registers .rdi, 4⟩]⟩, (),
      load_step pre af, ?_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, stored_value pre⟩
    · exact ⟨fetch_at pre 4 rfl (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre af, ?_, ?_, True.intro⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, stored_stack pre⟩
    · exact ⟨fetch_at pre 6 rfl (by decide), Or.inl rfl⟩

/-- Universal raw correctness under the unchanged registered precondition. -/
theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state) ∧ RawPolicy bytes input initial :=
  ⟨fun choices => ⟨_, executions pre choices, final_post pre⟩, raw_policy pre⟩

/-- One real checked mutation evolves the registration seed. The ordinary
load uses current owner authorization in that same world, and its preserved
RSP supplies the original caller-slot binding for the actual returning step. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  have currentMov : EDSL.OS.WordResources.Current resource.call resource.seed (afterMov initial) :=
    ⟨pre.current.contract, pre.current.coupled⟩
  have intent : Sequential.Instruction.storeIntent (.storeMem32 (.base .rdi) .rcx)
      (afterMov initial) = some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, Address.eval, afterMov, State.writeRegister, pre.pointer]
  obtain ⟨evolved, stored, actualStore, currentStore, _, _⟩ :=
    EDSL.OS.WordResources.current_store_step currentMov (store_decoded raw) intent false
  have storeEq : EDSL.OS.WordResources.storeAfterLength (afterMov initial) evolved
      (Sequential.Instruction.storeMem32 (.base .rdi) .rcx).length = afterStore initial := by
    have same := Except.ok.inj (actualStore.symm.trans (store_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [storeEq] at currentStore
  have effective : (Address.base .rdi).eval (afterStore initial) = resource.call.targetPointer := by
    simp [Address.eval, afterStore, afterMov, State.writeRegister, pre.pointer]
  obtain ⟨value, loadedAfter, actualLoad, _, loadedWord, authorized, operand,
      currentLoad, preserved, _, _, _⟩ :=
    EDSL.OS.WordResources.current_load_step currentStore (load_decoded raw) effective false
  have loadEq : loadedAfter = afterLoad initial := by
    have actual : Sequential.step false (afterStore initial) =
        .ok ⟨.next (afterLoad initial), [⟨.data, resource.call.targetPointer, 4⟩]⟩ := by
      simpa only [pre.pointer] using load_step raw false
    have same := Except.ok.inj (actualLoad.symm.trans actual)
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [loadEq] at currentLoad preserved
  obtain ⟨allocation, authorized, contains⟩ := authorized
  have targetRead : ReadAllowed resource.call evolved (afterStore initial)
      ⟨.data, initial.registers .rdi, 4⟩ :=
    ⟨pre.pointer, rfl, allocation, value, authorized, contains, loadedWord⟩
  have targetSucceeds : OperandReadSucceeds (afterStore initial)
      ⟨.data, initial.registers .rdi, 4⟩ := by
    simpa only [pre.pointer] using operand
  have stackBinding : (afterLoad initial).registers .rsp = resource.call.stack := by
    exact (preserved .rsp (by decide)).trans (by
      simpa [afterStore, afterMov, State.writeRegister] using pre.stack)
  have returnAfterEq : EDSL.OS.WordResources.returnAfter (afterLoad initial)
      resource.call.returnAddress = finalState initial (resourceInput resource).returnAddress := by
    simp [EDSL.OS.WordResources.returnAfter, finalState, afterLoad, afterStore,
      afterMov, State.writeRegister, resourceInput]
  have retActual (af : Bool) :=
    EDSL.OS.WordResources.current_ret_step currentLoad (ret_decoded raw) stackBinding af
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
    (shared = resource.seed ∧ before = afterMov initial) ∨
    (shared = evolved ∧ before = afterStore initial) ∨
    (shared = evolved ∧ before = afterLoad initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ |
    ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, .movReg32 .rcx .rsi, mov_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterMov initial), []⟩, resource.seed, mov_step raw af, ?_, ?_,
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch 0 (by simp) (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentMov, .storeMem32 (.base .rdi) .rcx, store_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, evolved, store_step raw af, ?_, ?_,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · simp
    · exact ⟨fetch 2 rfl (by decide), .store intent stored⟩
  · subst shared
    subst before
    refine ⟨currentStore, .loadMem32 .rcx (.base .rdi), load_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterLoad initial), [⟨.data, initial.registers .rdi, 4⟩]⟩, evolved,
      load_step raw af, ?_, ?_, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨targetRead, targetSucceeds⟩
    · exact ⟨fetch 4 rfl (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentLoad, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, evolved, ?_, ?_,
      ⟨fetch 6 rfl (by decide), .readOnly rfl⟩, currentReturn⟩
    · simpa only [returnAfterEq, pre.stack] using (retActual af).1
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      refine ⟨?_, ?_⟩
      · exact ⟨pre.stack, rfl, pre.stack ▸ (retActual af).2.2.1⟩
      · simpa only [pre.stack] using (retActual af).2.2.2

/-- Universal managed correctness, including lifted actual prefix/return
histories, current full RAM coupling, metadata, loans and outside frames. -/
theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result =>
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result) ∧
      ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned⟩

/-- Exact modeled count and reads for every possible actual returned result;
this follows from real execution determinism rather than a cost assumption. -/
theorem modeled_accounting {input initial choices result} (pre : Pre bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 4 ∧
      result.reads = [⟨.data, input.address, 4⟩, ⟨.stack, initial.registers .rsp, 8⟩] ∧
      (result.reads.map Read.bytes).sum = 12 := by
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre choices)
  subst result
  simp [pre.pointer]

/-- Useful changing-value witnesses use the current decoder-independent
registered domain construction for these exact seven bytes. -/
theorem useful_domain : Nonvacuous (registered .write32) bytes :=
  domain_nonvacuous .write32 bytes (by decide) (by decide)

/-- Closed universal client proof for the unchanged registered write32 task. -/
theorem claim : EDSL.Grading.Claim .write32 bytes :=
  ⟨⟨fun _ _ pre => raw_semantics pre, fun _ _ pre => resource_semantics pre⟩, useful_domain⟩


end EDSL.WriteMovesSupported
