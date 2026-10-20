/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.Model

set_option warningAsError true

namespace EDSL.StoreReturn32
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.Grading.Trace
open EDSL.Grading.Write32 (Input Pre RawPolicy FetchAllowed)

/-- The first actual intermediate state, including its current memory. -/
def stageOne (shape : Shape) (initial : State) : State :=
  match shape with
  | .storeCopy => { initial with
      memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
        ((initial.registers .rsi).setWidth 32)
      rip := initial.rip + 2 }
  | .copyStore | .copyStoreRax =>
      { initial.writeRegister .rax (initial.registers .rdi) with rip := initial.rip + 3 }

/-- Both instruction orderings establish the same full machine state. -/
def stageTwo (initial : State) : State :=
  { initial.writeRegister .rax (initial.registers .rdi) with
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 5 }

def finalState (initial : State) (target : Word) : State :=
  { (stageTwo initial).writeRegister .rsp (initial.registers .rsp + 8) with rip := target }

def firstInstruction : Shape → Sequential.Instruction
  | .storeCopy => .legacy .storeEsiRdi
  | .copyStore | .copyStoreRax => .movReg64 .rax .rdi

def secondInstruction : Shape → Sequential.Instruction
  | .storeCopy => .movReg64 .rax .rdi
  | .copyStore => .legacy .storeEsiRdi
  | .copyStoreRax => .storeMem32 (.base .rax) .rsi

def firstLength : Shape → Nat
  | .storeCopy => 2
  | .copyStore | .copyStoreRax => 3

private theorem decode_from_code {shape : Shape} {memory base} (code : CodeAt memory base shape.bytes)
    (offset : Nat) (inside : offset < shape.bytes.length) {state instruction}
    (mem : state.memory = memory) (pc : state.rip = base + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState shape.bytes offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction :=
  decodeAt_transport (code_fetch_transport code (by cases shape <;> decide)
    offset inside state mem pc) decoded

theorem stageOne_code {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    CodeAt (stageOne shape initial).memory initial.rip shape.bytes := by
  cases shape with
  | storeCopy =>
    apply writeDWord_preserves_code
    · exact pre.code
    · simpa only [pre.pointer] using pre.codeDisjoint
  | copyStore | copyStoreRax => exact pre.code

theorem stageTwo_code {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    CodeAt (stageTwo initial).memory initial.rip shape.bytes := by
  apply writeDWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

theorem first_decoded {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    Sequential.decodeAt initial = .ok (firstInstruction shape) := by
  cases shape <;> exact decode_from_code pre.code 0 (by decide) rfl (by simp) rfl

theorem second_decoded {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    Sequential.decodeAt (stageOne shape initial) = .ok (secondInstruction shape) := by
  cases shape with
  | storeCopy => exact decode_from_code (stageOne_code pre) 2 (by decide) rfl rfl rfl
  | copyStore => exact decode_from_code (stageOne_code pre) 3 (by decide) rfl rfl rfl
  | copyStoreRax => exact decode_from_code (stageOne_code pre) 3 (by decide) rfl rfl rfl

theorem ret_decoded {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    Sequential.decodeAt (stageTwo initial) = .ok (.legacy .ret) := by
  cases shape <;> exact decode_from_code (stageTwo_code pre) 5 (by decide) rfl rfl rfl

theorem first_step {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (stageOne shape initial), []⟩ := by
  rw [step_eq_execute af (first_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  cases shape <;> simp [firstInstruction, Sequential.execute,
    Sequential.Instruction.operandReads, X86.executeInstruction, executeStore,
    storeDWord, writable, stageOne]

theorem second_step {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) (af : Bool) :
    Sequential.step af (stageOne shape initial) = .ok ⟨.next (stageTwo initial), []⟩ := by
  rw [step_eq_execute af (second_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  cases shape <;> simp [secondInstruction, Sequential.execute,
    Sequential.Instruction.operandReads, X86.executeInstruction, executeStore,
    storeDWord, writable, stageOne, stageTwo, State.writeRegister,
    Address.eval, Sequential.Instruction.length, BitVec.add_assoc]

theorem stageTwo_stack {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    readWord (stageTwo initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

theorem ret_step {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) (af : Bool) :
    Sequential.step af (stageTwo initial) =
      .ok ⟨.returned (finalState initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (stageTwo initial).memory ((stageTwo initial).registers .rsp) =
      .ok input.returnAddress := by
    simpa [stageTwo, State.writeRegister] using stageTwo_stack pre
  simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, finalState]
  simp [stageTwo, State.writeRegister]

/-- All inputs satisfy the independently stated store, pointer, permission,
caller-return and SysV preservation contract. No target-address truncation
bound or precondition about future execution is required. -/
theorem final_post {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    Post input initial (finalState initial input.returnAddress) := by
  have noWrap : input.address.toNat + 3 < 2^64 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp pre.target_addressable).1
  refine ⟨⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩, ?_⟩
  · have readback := load_after_write initial.memory input.address
      (input.argument.setWidth 32) pre.target_addressable
    simpa only [finalState, State.writeRegister, stageTwo, pre.pointer, pre.source] using readback
  · intro query outside
    have large : 4 ≤ (query - input.address).toNat := by
      have excluded := mt (AddressSpace.word_contains_iff input.address query noWrap).mpr outside
      omega
    exact writeDWord_frame initial.memory _ query _ (by rwa [pre.pointer])
  · simp [finalState, stageTwo, State.writeRegister]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same
      subst register
      simp [Grading.Write32.calleeSaved] at member
    have notRax : register ≠ .rax := by
      intro same
      subst register
      simp [Grading.Write32.calleeSaved] at member
    simp [finalState, stageTwo, State.writeRegister, notStack, notRax]
  · simpa [finalState, stageTwo, State.writeRegister] using pre.pointer

/-- The exact decoded three-step return for every stream of modeled AF choices. -/
theorem executions {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState initial input.returnAddress, 3, [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (first_step pre (choices 0))
    (Sequential.Executes.next (second_step pre ((choices.drop 1) 0))
      (Sequential.Executes.ret (ret_step pre (((choices.drop 1).drop 1) 0))))
  simpa only [Result.prepend, List.nil_append] using execution

theorem fetch_at {shape : Shape} {input initial before instruction} (pre : Pre shape.bytes input initial)
    (offset : Nat) (pc : before.rip = initial.rip + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ shape.bytes.length) :
    FetchAllowed initial.rip shape.bytes.length before instruction := by
  have limit := pre.code.1
  have length : shape.bytes.length = 6 := by cases shape <;> rfl
  rw [length] at limit span ⊢
  have positive := instruction.length_pos
  have small : offset < 2^64 := by omega
  have total : initial.rip.toNat + offset < 2^64 := by omega
  have natural : (initial.rip + BitVec.ofNat 64 offset).toNat = initial.rip.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change initial.rip.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ initial.rip.toNat + 6
  rw [pc, natural]
  omega

/-- Every actual prefix retains the original fetch span and fixed-target
raw effect policy. Stores remain ordinary writes, not concurrent atomics. -/
theorem raw_policy {shape : Shape} {input initial} (pre : Pre shape.bytes input initial) :
    RawPolicy shape.bytes input initial := by
  refine ⟨(fun (_ : Unit) state => state = initial ∨ state = stageOne shape initial ∨
    state = stageTwo initial), Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same | same
  · subst before
    refine ⟨True.intro, firstInstruction shape, first_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (stageOne shape initial), []⟩, (), first_step pre af, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · simp
    · refine ⟨fetch_at pre 0 (by simp) (by cases shape <;> decide), ?_⟩
      cases shape
      · exact Or.inr ⟨(initial.registers .rsi).setWidth 32, by
          simp [firstInstruction, Sequential.Instruction.storeIntent,
            X86.Instruction.storeIntent, pre.pointer]⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
  · subst before
    refine ⟨True.intro, secondInstruction shape, second_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (stageTwo initial), []⟩, (), second_step pre af, ?_, ?_, Or.inr (Or.inr rfl)⟩
    · simp
    · refine ⟨fetch_at pre (firstLength shape) (by cases shape <;> rfl)
        (by cases shape <;> decide), ?_⟩
      cases shape
      · exact Or.inl rfl
      · exact Or.inr ⟨(initial.registers .rsi).setWidth 32, by
          simp [secondInstruction, Sequential.Instruction.storeIntent,
            X86.Instruction.storeIntent, stageOne, State.writeRegister, pre.pointer]⟩
      · exact Or.inr ⟨(initial.registers .rsi).setWidth 32, by
          simp [secondInstruction, Sequential.Instruction.storeIntent,
            stageOne, State.writeRegister, Address.eval, pre.pointer]⟩
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (finalState initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre af, ?_, ?_, True.intro⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, stageTwo_stack pre⟩
    · exact ⟨fetch_at pre 5 rfl (by cases shape <;> decide), Or.inl rfl⟩

/-- Universal raw correctness and exact accounting derived from the current
executable bytes and present permissions, with unchanged independent policies. -/
theorem raw_semantics {shape : Shape} {input : Input} {initial : State}
    (pre : Pre shape.bytes input initial) :
    Sequential.AllExecutions initial (ResultContract input initial) ∧ RawPolicy shape.bytes input initial :=
  ⟨fun choices => ⟨_, executions pre choices, final_post pre, rfl, rfl⟩, raw_policy pre⟩

/-- Every actual returned result has the exact three-instruction cost and
original stack-only read list, by uniqueness of actual execution. -/
theorem modeled_accounting {shape : Shape} {input initial choices result} (pre : Pre shape.bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = 3 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  have same := Sequential.Executes.fixed_choices_unique execution (executions pre choices)
  subst result
  exact ⟨rfl, rfl⟩

end EDSL.StoreReturn32
