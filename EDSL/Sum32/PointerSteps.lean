/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.PointerFrame

namespace EDSL.Sum32.PointerProof
open X86

theorem update_block {bytes : List Byte} {plan : Plan} {base : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    {memory : Memory} (code : CodeAt memory base bytes) (choices : Sequential.Choices)
    (state : State) (mem : state.memory = memory)
    (pc : state.rip = base + BitVec.ofNat 64 (plan.load + 2)) :
    ∃ final, Sequential.Block choices state final 2 [] ∧
      final.rip = base + BitVec.ofNat 64 plan.back.offset ∧
      final.registers .rax = state.registers .rax ∧
      final.registers .rdi = state.registers .rdi + 4 ∧
      final.registers .rsi = state.registers .rsi - 1 ∧ Frame state final := by
  obtain ⟨first, second, updates, firstPC, secondPC, backPC, order⟩ := update_layout valid mode
  have firstMember := plan.update_member (node := first) (by simp [updates])
  have secondMember := plan.update_member (node := second) (by simp [updates])
  have decodedFirst := valid.decoded code first firstMember state mem (by simpa only [firstPC] using pc)
  rcases order with ⟨firstInstruction, secondInstruction⟩ | ⟨firstInstruction, secondInstruction⟩
  · let middle := decrement state
    let final := advance middle
    have stepFirst : Sequential.step (choices 0) state = .ok ⟨.next middle, []⟩ := by
      rw [Sequential.step_eq_execute _ decodedFirst, firstInstruction]
      rfl
    have middlePC : middle.rip = base + BitVec.ofNat 64 second.offset := by
      simp only [middle, decrement, pc, secondPC, firstPC, firstInstruction,
        Sequential.Instruction.length, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    have decodedSecond := valid.decoded code second secondMember middle mem middlePC
    have stepSecond : Sequential.step ((choices.drop 1) 0) middle = .ok ⟨.next final, []⟩ := by
      rw [Sequential.step_eq_execute _ decodedSecond, secondInstruction]
      rfl
    refine ⟨final, ?_, ?_, ?_, ?_, ?_, (frame_decrement state).trans (frame_advance middle)⟩
    · exact Sequential.Block.next stepFirst (Sequential.Block.next stepSecond Sequential.Block.nil)
    · simp only [final, advance, middlePC, backPC, secondInstruction,
        Sequential.Instruction.length, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · simp [final, middle, advance, decrement, State.writeRegister]
    · simp [final, middle, advance, decrement, State.writeRegister]
    · simp [final, middle, advance, decrement, State.writeRegister]
  · let middle := advance state
    let final := decrement middle
    have stepFirst : Sequential.step (choices 0) state = .ok ⟨.next middle, []⟩ := by
      rw [Sequential.step_eq_execute _ decodedFirst, firstInstruction]
      rfl
    have middlePC : middle.rip = base + BitVec.ofNat 64 second.offset := by
      simp only [middle, advance, pc, secondPC, firstPC, firstInstruction,
        Sequential.Instruction.length, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    have decodedSecond := valid.decoded code second secondMember middle mem middlePC
    have stepSecond : Sequential.step ((choices.drop 1) 0) middle = .ok ⟨.next final, []⟩ := by
      rw [Sequential.step_eq_execute _ decodedSecond, secondInstruction]
      rfl
    refine ⟨final, ?_, ?_, ?_, ?_, ?_, (frame_advance state).trans (frame_decrement middle)⟩
    · exact Sequential.Block.next stepFirst (Sequential.Block.next stepSecond Sequential.Block.nil)
    · simp only [final, decrement, middlePC, backPC, secondInstruction,
        Sequential.Instruction.length, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · simp [final, middle, advance, decrement, State.writeRegister]
    · simp [final, middle, advance, decrement, State.writeRegister]
    · simp [final, middle, advance, decrement, State.writeRegister]

/-- The TEST and JE are executed using the full count and this instruction's AF choice. -/
theorem guard_block {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state values accumulator target)
    (choices : Sequential.Choices) :
    let destination := if values = [] then plan.exit else plan.load
    ∃ final, Sequential.Block choices state final 2 [] ∧
      final.rip = base + BitVec.ofNat 64 destination ∧
      final.registers = state.registers ∧ Frame state final := by
  let middle := test state (choices 0)
  have decodedHeader := valid.decoded header.code _ plan.header_member state rfl header.pc
  have stepTest : Sequential.step (choices 0) state = .ok ⟨.next middle, []⟩ := by
    rw [Sequential.step_eq_execute _ decodedHeader, mode]
    rfl
  have middlePC : middle.rip = base + BitVec.ofNat 64 plan.branch.offset := by
    simp only [middle, test, header.pc, valid.headerNext, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have decodedBranch := valid.decoded header.code _ plan.branch_member middle rfl middlePC
  have zero : middle.flags.getLsbD 6 = (values == []) := by
    simp only [middle, test, BitVec.and_self, Sequential.logicalFlags64_zero, header.count]
    cases values with
    | nil => rfl
    | cons value rest =>
      have nonzero := count_nonzero rest value header.countBound
      change (BitVec.ofNat 64 (value :: rest).length == 0) = false
      exact decide_eq_false_iff_not.mpr nonzero
  cases values with
  | nil =>
    let final := atPC middle (base + BitVec.ofNat 64 plan.exit)
    have canonicalExit := valid.canonical_node header.code _ plan.exit_member
    have stepBranch : Sequential.step ((choices.drop 1) 0) middle = .ok ⟨.next final, []⟩ := by
      rw [Sequential.step_eq_execute _ decodedBranch, Sequential.execute_je]
      change middle.flags.getLsbD 6 = true at zero
      rw [zero]
      simp only [executeShortBranch, middlePC, valid.forward_target, canonicalExit,
        ite_true, ok_bind, pure_ok]
      rfl
    refine ⟨final, Sequential.Block.next stepTest (Sequential.Block.next stepBranch Sequential.Block.nil),
      rfl, rfl, (frame_test state _).trans (frame_atPC middle _)⟩
  | cons value rest =>
    let final := atPC middle (base + BitVec.ofNat 64 plan.load)
    have stepBranch : Sequential.step ((choices.drop 1) 0) middle = .ok ⟨.next final, []⟩ := by
      rw [Sequential.step_eq_execute _ decodedBranch, Sequential.execute_je]
      change middle.flags.getLsbD 6 = false at zero
      rw [zero]
      simp only [executeShortBranch, Bool.false_eq_true, ite_false,
        middlePC, final, atPC, valid.branchNext, BitVec.ofNat_add, BitVec.add_assoc, ok_bind, pure_ok]
      rfl
    refine ⟨final, Sequential.Block.next stepTest (Sequential.Block.next stepBranch Sequential.Block.nil),
      ?_, rfl, (frame_test state _).trans (frame_atPC middle _)⟩
    simp only [List.cons_ne_nil, ite_false, final, atPC]

/-- One nonempty iteration retires six actual instructions and reads only the head. -/
theorem iteration {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state (value :: values) accumulator target)
    (choices : Sequential.Choices) :
    ∃ final, Sequential.Block choices state final 6 [⟨.data, state.registers .rdi, 4⟩] ∧
      PointerHeader bytes plan base final values (accumulator + value) target ∧
      final.registers .rdi = state.registers .rdi + 4 ∧ Frame state final := by
  obtain ⟨body, guard, bodyPC, bodyRegisters, guardFrame⟩ := guard_block valid mode header choices
  simp only [List.cons_ne_nil, ite_false] at bodyPC
  let loaded := load body value
  have operand : loadDWord body.memory (body.registers .rdi) = .ok value := by
    rw [guardFrame.memory, bodyRegisters]
    exact header.array.head
  have decodedLoad := valid.decoded header.code _ plan.load_member body guardFrame.memory bodyPC
  have stepLoad : Sequential.step ((choices.drop 2) 0) body =
      .ok ⟨.next loaded, [⟨.data, state.registers .rdi, 4⟩]⟩ := by
    rw [Sequential.step_eq_execute _ decodedLoad, mode]
    change Sequential.execute body (.addMem32 .rax (.base .rdi)) _ = _
    rw [Sequential.execute_addMem32]
    simp only [Sequential.Address.eval]
    rw [operand]
    simp only [ok_bind, pure_ok, loaded, load, bodyRegisters]
    rfl
  have loadedPC : loaded.rip = base + BitVec.ofNat 64 (plan.load + 2) := by
    simp only [loaded, load, bodyPC, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  obtain ⟨updated, updates, updatedPC, updatedRax, updatedRdi, updatedRsi, updateFrame⟩ :=
    update_block valid mode header.code (choices.drop 3) loaded guardFrame.memory loadedPC
  have prefixFrame := (guardFrame.trans (frame_load body value)).trans updateFrame
  let final := atPC updated (base + BitVec.ofNat 64 plan.header)
  have decodedBack := valid.decoded header.code _ plan.back_member updated prefixFrame.memory updatedPC
  have canonicalHeader := valid.canonical_node header.code _ plan.header_member
  have stepBack : Sequential.step ((choices.drop 5) 0) updated = .ok ⟨.next final, []⟩ := by
    rw [Sequential.step_eq_execute _ decodedBack, Sequential.execute_jmp]
    simp only [executeShortBranch, updatedPC, valid.backward_target, canonicalHeader,
      ite_true, ok_bind, pure_ok]
    rfl
  have backBlock : Sequential.Block (choices.drop 5) updated final 1 [] :=
    Sequential.Block.next stepBack Sequential.Block.nil
  have tailBlock : Sequential.Block (choices.drop 3) loaded final 3 [] := by
    exact updates.append (by simpa only [Sequential.Choices.drop_drop] using backBlock)
  have bodyBlock : Sequential.Block (choices.drop 2) body final 4
      [⟨.data, state.registers .rdi, 4⟩] := by
    exact Sequential.Block.next stepLoad
      (by simpa only [Sequential.Choices.drop_drop] using tailBlock)
  have whole : Sequential.Block choices state final 6 [⟨.data, state.registers .rdi, 4⟩] :=
    guard.append bodyBlock
  have frame : Frame state final := prefixFrame.trans (frame_atPC updated _)
  have finalRdi : final.registers .rdi = state.registers .rdi + 4 := by
    simpa [final, atPC, loaded, load, State.writeRegister, bodyRegisters] using updatedRdi
  refine ⟨final, whole, ?_, finalRdi, frame⟩
  refine {
    code := ?_
    pc := rfl
    accumulator := ?_
    stack := ?_
    canonicalTarget := header.canonicalTarget
    canonicalStackAfter := ?_
    array := ?_
    count := ?_
    countBound := ?_ }
  · rw [frame.memory]; exact header.code
  · change updated.registers .rax = (accumulator + value).setWidth 64
    rw [updatedRax]
    simp only [loaded, load, State.writeRegister, ite_true, bodyRegisters, header.accumulator]
    simp
  · rw [frame.memory, frame.stack]; exact header.stack
  · rw [frame.stack]; exact header.canonicalStackAfter
  · rw [frame.memory, finalRdi]; exact header.array.tail
  · change updated.registers .rsi = BitVec.ofNat 64 values.length
    rw [updatedRsi]
    simpa [loaded, load, State.writeRegister, bodyRegisters, header.count] using
      count_decrement values value
  · have bound := header.countBound
    simp only [List.length_cons] at bound
    omega

/-- The empty guard branches to the checked RET, which reads the current stack. -/
theorem finish {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {accumulator : BitVec 32} {target : Word}
    (valid : Valid bytes plan) (mode : plan.mode = .pointerCount)
    (header : PointerHeader bytes plan base state [] accumulator target)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices state result ∧
      LoopPost state accumulator [] target result.state ∧
      result.instructions = 3 ∧ result.reads = pointerReads state [] := by
  obtain ⟨exit, guard, exitPC, exitRegisters, frame⟩ := guard_block valid mode header choices
  simp only [ite_true] at exitPC
  have decodedExit := valid.decoded header.code _ plan.exit_member exit frame.memory exitPC
  have stack : readWord exit.memory (exit.registers .rsp) = .ok target := by
    rw [frame.memory, frame.stack]; exact header.stack
  let final := { exit.writeRegister .rsp (exit.registers .rsp + 8) with rip := target }
  have returned : executeInstruction exit .ret = .ok (.returned final) := by
    simp only [executeInstruction, executeRet, stack, ok_bind, header.canonicalTarget,
      ite_true, pure_ok]
    rfl
  have stepRet : Sequential.step ((choices.drop 2) 0) exit =
      .ok ⟨.returned final, [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
    rw [Sequential.step_eq_execute _ decodedExit, Sequential.execute_legacy]
    rw [returned]
    simp only [except_map_ok, Sequential.Instruction.operandReads, frame.stack]
  refine ⟨⟨final, 3, [⟨.stack, state.registers .rsp, 8⟩]⟩,
    guard.then_executes (Sequential.Executes.ret stepRet), ?_, rfl, rfl⟩
  refine ⟨?_, frame.memory, rfl, ?_, ?_, frame.flags⟩
  · simpa [final, State.writeRegister, exitRegisters] using header.accumulator
  · simp only [final, State.writeRegister, ite_true, frame.stack]
  · intro register allowed
    have different : register ≠ .rsp := by intro same; subst register; simp [clobbers] at allowed
    simpa only [final, State.writeRegister, different, ite_false] using frame.preserved register allowed

end EDSL.Sum32.PointerProof
