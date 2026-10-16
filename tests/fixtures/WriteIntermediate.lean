/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.OS.WordResources.Bridge

set_option warningAsError true

namespace EDSL.WriteIntermediateSupported
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS EDSL.Grading EDSL.Grading.Trace
open EDSL.Grading.Write32

/-- INC RSI; store ESI; DEC RSI; store ESI; RET. -/
def bytes : List Byte := [0x48, 0xff, 0xc6, 0x89, 0x37, 0x48, 0xff, 0xce, 0x89, 0x37, 0xc3]

def afterInc (initial : State) : State :=
  { initial.writeRegister .rsi (initial.registers .rsi + 1) with
    rip := initial.rip + 3
    flags := incFlags64 initial.flags (initial.registers .rsi) }

def afterFirst (initial : State) : State :=
  { afterInc initial with
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi + 1).setWidth 32)
    rip := initial.rip + 5 }

def afterDec (initial : State) : State :=
  { afterFirst initial with
    registers := initial.registers
    rip := initial.rip + 8
    flags := decFlags64 (afterInc initial).flags (initial.registers .rsi + 1) }

def afterSecond (initial : State) : State :=
  { afterDec initial with
    memory := writeDWordUnchecked (afterFirst initial).memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 10 }

def finalState (initial : State) (target : Word) : State :=
  { (afterSecond initial).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

private theorem decode_from_code {memory base} (code : CodeAt memory base bytes)
    (offset : Nat) (inside : offset < bytes.length) {state instruction}
    (mem : state.memory = memory) (pc : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction :=
  decodeAt_transport (code_fetch_transport code (by decide) offset inside state mem pc) decoded

private theorem first_code {input initial} (pre : Pre bytes input initial) :
    CodeAt (afterFirst initial).memory initial.rip bytes := by
  apply writeDWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

private theorem second_code {input initial} (pre : Pre bytes input initial) :
    CodeAt (afterSecond initial).memory initial.rip bytes := by
  apply writeDWord_preserves_code
  · exact first_code pre
  · simpa only [pre.pointer] using pre.codeDisjoint

private theorem inc_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.inc64 .rsi) :=
  decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

private theorem first_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterInc initial) = .ok (.legacy .storeEsiRdi) :=
  decode_from_code pre.code 3 (by decide) rfl rfl rfl

private theorem dec_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterFirst initial) = .ok (.dec64 .rsi) :=
  decode_from_code (first_code pre) 5 (by decide) rfl rfl rfl

private theorem second_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterDec initial) = .ok (.legacy .storeEsiRdi) :=
  decode_from_code (first_code pre) 8 (by decide) rfl rfl rfl

private theorem ret_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterSecond initial) = .ok (.legacy .ret) :=
  decode_from_code (second_code pre) 10 (by decide) rfl rfl rfl

private theorem inc_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterInc initial), []⟩ := by
  rw [step_eq_execute af (inc_decoded pre)]
  rfl

private theorem first_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterInc initial) = .ok ⟨.next (afterFirst initial), []⟩ := by
  rw [step_eq_execute af (first_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [Sequential.execute, Instruction.operandReads, X86.executeInstruction,
    executeStore, storeDWord, afterInc, afterFirst, State.writeRegister, writable,
    BitVec.add_assoc]

private theorem dec_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterFirst initial) = .ok ⟨.next (afterDec initial), []⟩ := by
  rw [step_eq_execute af (dec_decoded pre)]
  have registers : ((afterFirst initial).writeRegister .rsi
      ((afterFirst initial).registers .rsi - 1)).registers = initial.registers := by
    funext register
    by_cases same : register = .rsi
    · subst register
      simp [State.writeRegister, afterFirst, afterInc, BitVec.add_sub_cancel]
    · simp [State.writeRegister, afterFirst, afterInc, same]
  simp only [Sequential.execute, Instruction.operandReads, pure_ok]
  congr 3
  rw [registers]
  simp [afterDec, afterFirst, afterInc, State.writeRegister, BitVec.add_assoc]

private theorem second_writable {input initial} (pre : Pre bytes input initial) :
    canStoreDWord (afterDec initial).memory (initial.registers .rdi) = true := by
  have allowed : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp only [canStoreDWord, dwordWritable, Bool.and_eq_true] at allowed
  simp [canStoreDWord, dwordWritable, afterDec, afterFirst, writeDWordUnchecked, storedDWordByte]
  exact ⟨allowed.1, allowed.2.1⟩

private theorem second_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterDec initial) = .ok ⟨.next (afterSecond initial), []⟩ := by
  rw [step_eq_execute af (second_decoded pre)]
  have writable : canStoreDWord (afterFirst initial).memory (initial.registers .rdi) = true :=
    second_writable pre
  simp [Sequential.execute, Instruction.operandReads, X86.executeInstruction,
    executeStore, storeDWord, writable, afterSecond, afterDec, BitVec.add_assoc]

private theorem second_stack {input initial} (pre : Pre bytes input initial) :
    readWord (afterSecond initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  have separate : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8 := by
    simpa only [pre.pointer] using pre.stackDisjoint
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 separate)).trans
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 separate)).trans pre.stack

private theorem ret_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterSecond initial) =
      .ok ⟨.returned (finalState initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (afterSecond initial).memory ((afterSecond initial).registers .rsp) =
      .ok input.returnAddress := second_stack pre
  simp [Sequential.execute, Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [afterSecond, afterDec]

/-- Both stores preserve the whole outside RAM frame; final RSI is the original
64-bit word, including the carry/wraparound case of INC followed by DEC. -/
theorem final_post {input initial} (pre : Pre bytes input initial) :
    Post input initial (finalState initial input.returnAddress) := by
  have noWrap : input.address.toNat + 3 < 2^64 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp pre.target_addressable).1
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have readback := load_after_write (afterFirst initial).memory input.address
      (input.argument.setWidth 32) pre.target_addressable
    simpa only [finalState, State.writeRegister, afterSecond, afterDec,
      pre.pointer, pre.source] using readback
  · intro query outside
    have large : 4 ≤ (query - input.address).toNat := by
      have excluded := mt (AddressSpace.word_contains_iff input.address query noWrap).mpr outside
      omega
    have separate : 4 ≤ (query - initial.registers .rdi).toNat := by rwa [pre.pointer]
    exact (writeDWord_frame _ _ _ _ separate).trans (writeDWord_frame _ _ _ _ separate)
  · simp [finalState, State.writeRegister, afterSecond, afterDec]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same
      subst register
      simp [calleeSaved] at member
    simp [finalState, State.writeRegister, afterSecond, afterDec, notStack]
  · exact (decFlags64_preserves _ _).trans (incFlags64_preserves _ _)

/-- All AF streams execute exactly five supported instructions and return. -/
theorem executions {input initial} (pre : Pre bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial input.returnAddress, 5, [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution :=
    Sequential.Executes.next (inc_step pre (choices 0))
      (Sequential.Executes.next (first_step pre ((choices.drop 1) 0))
        (Sequential.Executes.next (dec_step pre (((choices.drop 1).drop 1) 0))
          (Sequential.Executes.next (second_step pre ((((choices.drop 1).drop 1).drop 1) 0))
            (Sequential.Executes.ret (ret_step pre (((((choices.drop 1).drop 1).drop 1).drop 1) 0))))))
  simpa only [Result.prepend, List.nil_append] using execution


private theorem fetch_at {input initial before instruction} (pre : Pre bytes input initial)
    (offset : Nat) (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    FetchAllowed initial.rip bytes.length before instruction := by
  have limit := pre.code.1
  have positive := instruction.length_pos
  change initial.rip.toNat + 11 ≤ 2^64 at limit
  change offset + instruction.length ≤ 11 at span
  have small : offset < 2^64 := by omega
  have total : initial.rip.toNat + offset < 2^64 := by omega
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 11
  rw [pc, natural]
  omega

/-- Real current-memory prefixes, including every intermediate ordinary store,
meet the registered raw fixed-target policy for all AF choices. -/
theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  refine ⟨(fun (_ : Unit) state => state = initial ∨ state = afterInc initial ∨
    state = afterFirst initial ∨ state = afterDec initial ∨ state = afterSecond initial),
    Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same | same | same | same
  · subst before
    refine ⟨True.intro, .inc64 .rsi, inc_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterInc initial), []⟩, (), inc_step pre af, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · simp
    · exact ⟨fetch_at pre 0 (by simp) (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .legacy .storeEsiRdi, first_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterFirst initial), []⟩, (), first_step pre af, ?_, ?_,
      Or.inr (Or.inr (Or.inl rfl))⟩
    · simp
    · refine ⟨fetch_at pre 3 rfl (by decide), Or.inr ⟨(initial.registers .rsi + 1).setWidth 32, ?_⟩⟩
      simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent,
        afterInc, State.writeRegister, pre.pointer]
  · subst before
    refine ⟨True.intro, .dec64 .rsi, dec_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterDec initial), []⟩, (), dec_step pre af, ?_, ?_,
      Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · simp
    · exact ⟨fetch_at pre 5 rfl (by decide), Or.inl rfl⟩
  · subst before
    refine ⟨True.intro, .legacy .storeEsiRdi, second_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterSecond initial), []⟩, (), second_step pre af, ?_, ?_,
      Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    · simp
    · refine ⟨fetch_at pre 8 rfl (by decide), Or.inr ⟨(initial.registers .rsi).setWidth 32, ?_⟩⟩
      simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent,
        afterDec, pre.pointer]
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre af, ?_, ?_, True.intro⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, second_stack pre⟩
    · exact ⟨fetch_at pre 10 rfl (by decide), Or.inl rfl⟩

/-- All original admitted raw inputs, including arbitrary old/new values, high
RSI bits, high canonical target pointers and modular RSI wraparound. -/
theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state) ∧ RawPolicy bytes input initial :=
  ⟨fun choices => ⟨_, executions pre choices, final_post pre⟩, raw_policy pre⟩

/-- Two real checked Borrowing.mutate evolutions, starting at the registration
seed. Both current code and full-stack loans survive each store. -/
theorem resource_policy {resource initial} (pre : ResourcePre bytes resource initial) :
    ResourcePolicy resource initial := by
  have raw := pre.machine
  have currentInc : EDSL.OS.WordResources.Current resource.call resource.seed (afterInc initial) :=
    ⟨pre.current.contract, pre.current.coupled⟩
  have intentFirst : Sequential.Instruction.storeIntent (.legacy .storeEsiRdi) (afterInc initial) =
      some (resource.call.targetPointer, (initial.registers .rsi + 1).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent,
      afterInc, State.writeRegister, pre.pointer]
  obtain ⟨world1, stored1, actual1, currentFirst, _, _⟩ :=
    EDSL.OS.WordResources.current_store_step currentInc (first_decoded raw) intentFirst false
  have firstEq : EDSL.OS.WordResources.storeAfter (afterInc initial) world1 = afterFirst initial := by
    have same := Except.ok.inj (actual1.symm.trans (first_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [firstEq] at currentFirst
  have currentDec : EDSL.OS.WordResources.Current resource.call world1 (afterDec initial) :=
    ⟨currentFirst.contract, currentFirst.coupled⟩
  have intentSecond : Sequential.Instruction.storeIntent (.legacy .storeEsiRdi) (afterDec initial) =
      some (resource.call.targetPointer, (initial.registers .rsi).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent, afterDec, pre.pointer]
  obtain ⟨world2, stored2, actual2, currentSecond, _, _⟩ :=
    EDSL.OS.WordResources.current_store_step currentDec (second_decoded raw) intentSecond false
  have secondEq : EDSL.OS.WordResources.storeAfter (afterDec initial) world2 = afterSecond initial := by
    have same := Except.ok.inj (actual2.symm.trans (second_step raw false))
    exact StepResult.next.inj (congrArg Observation.result same)
  rw [secondEq] at currentSecond
  have currentReturn : EDSL.OS.WordResources.Current resource.call world2
      (finalState initial (resourceInput resource).returnAddress) :=
    ⟨currentSecond.contract, currentSecond.coupled⟩
  have fetch {before instruction} (offset : Nat)
      (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
      (span : offset + instruction.length ≤ bytes.length) :
      FetchAllowed resource.call.code resource.call.bytes.length before instruction := by
    rw [pre.code, ← pre.entry]
    exact fetch_at raw offset pc span
  refine ⟨(fun shared before =>
    (shared = resource.seed ∧ before = initial) ∨
    (shared = resource.seed ∧ before = afterInc initial) ∨
    (shared = world1 ∧ before = afterFirst initial) ∨
    (shared = world1 ∧ before = afterDec initial) ∨
    (shared = world2 ∧ before = afterSecond initial)), Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro shared before inside
  rcases inside with ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ |
    ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩ | ⟨sameShared, sameBefore⟩
  · subst shared
    subst before
    refine ⟨pre.current, .inc64 .rsi, inc_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterInc initial), []⟩, resource.seed, inc_step raw af, ?_, ?_,
      Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · simp
    · exact ⟨fetch 0 (by simp) (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentInc, .legacy .storeEsiRdi, first_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterFirst initial), []⟩, world1, first_step raw af, ?_, ?_,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · simp
    · exact ⟨fetch 3 rfl (by decide), .store intentFirst stored1⟩
  · subst shared
    subst before
    refine ⟨currentFirst, .dec64 .rsi, dec_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterDec initial), []⟩, world1, dec_step raw af, ?_, ?_,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · simp
    · exact ⟨fetch 5 rfl (by decide), .readOnly rfl⟩
  · subst shared
    subst before
    refine ⟨currentDec, .legacy .storeEsiRdi, second_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.next (afterSecond initial), []⟩, world2, second_step raw af, ?_, ?_,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    · simp
    · exact ⟨fetch 8 rfl (by decide), .store intentSecond stored2⟩
  · subst shared
    subst before
    refine ⟨currentSecond, .legacy .ret, ret_decoded raw, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial (resourceInput resource).returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, world2, ret_step raw af, ?_,
      ⟨fetch 10 rfl (by decide), .readOnly rfl⟩, currentReturn⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    refine ⟨?_, rfl, _, second_stack raw⟩
    change initial.registers .rsp = resource.call.stack ∧ 8 = 8 ∧
      ArrayResources.ReadPermission world2 resource.call.worker ⟨.stack, initial.registers .rsp, 8⟩
    exact ⟨pre.stack, rfl, pre.stack ▸ EDSL.OS.WordResources.stackRead_permission currentSecond.contract⟩

/-- Complete managed final frame is accumulated from the actual checked path:
OS history, allocation metadata, loans, permissions and all outside cells. -/
theorem resource_semantics {resource initial} (pre : ResourcePre bytes resource initial) :
    AllExecutions initial (fun result =>
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result) ∧
      ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_, policy⟩
  intro choices
  obtain ⟨result, execution, post⟩ := (raw_semantics pre.machine).1 choices
  exact ⟨result, execution, post, policy.returned⟩

/-- Decoder-independent useful raw and current-resource witnesses, with a
changing target value, constructed for these exact eleven bytes. -/
theorem useful_domain : Nonvacuous (registered .write32) bytes :=
  domain_nonvacuous .write32 bytes (by decide) (by decide)

/-- Closed client-only proof of the unchanged public registered claim. -/
theorem claim : EDSL.Grading.Claim .write32 bytes :=
  ⟨⟨fun _ _ pre => raw_semantics pre, fun _ _ pre => resource_semantics pre⟩, useful_domain⟩

end EDSL.WriteIntermediateSupported
