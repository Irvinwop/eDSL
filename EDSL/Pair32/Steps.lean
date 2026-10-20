/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Model

namespace EDSL.Pair32
open X86

def initialized {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (af : Bool) :
    Header initial valuesA valuesB .first (clear initial af) where
  remaining := valuesA
  count := valuesA.length
  accumulator := 0
  consumed := 0
  length := rfl
  countBound := pre.countA_lt
  counter := pre.countA
  pointer := by simp [clear, edit, State.writeRegister, Loop.pointer]
  value := by simp [clear, edit, State.writeRegister]
  array := pre.arrayA
  split := by simp
  correct := by simp [pairSum_eq]
  frame := frame_clear initial af
  pc := rfl
  future := fun _ => ⟨rfl, pre.countB⟩

def nextHeader {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    (header : Header initial valuesA valuesB loop state) (element : Element header) (af : Bool) :
    Header initial valuesA valuesB loop (cycleState loop initial.rip state af element.first) where
  remaining := element.tail
  count := element.rest
  accumulator := header.accumulator + element.first
  consumed := header.consumed + 1
  length := by
    have length := header.length
    rw [element.values, element.count] at length
    simp only [List.length_cons] at length
    omega
  countBound := by have bound := header.countBound; rw [element.count] at bound; omega
  counter := by
    simp only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      Loop.counter_ne_pointer, Loop.counter_ne_rax, ite_false, ite_true]
    rw [header.counter, element.count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  pointer := by
    simp only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      Loop.pointer_ne_counter, Loop.pointer_ne_rax, ite_false, ite_true]
    rw [header.pointer]
    simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  value := by
    simp [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      Ne.symm (Loop.pointer_ne_rax loop), Ne.symm (Loop.counter_ne_rax loop), header.value]
  array := by
    have array := header.array
    rw [element.values] at array
    simpa only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      Loop.pointer_ne_counter, Loop.pointer_ne_rax, ite_false, ite_true] using array.tail
  split := by have split := header.split; rw [element.count] at split; omega
  correct := by
    have correct := header.correct
    rw [element.values, sum32_cons] at correct
    simpa only [BitVec.add_assoc] using correct
  frame := header.frame.trans (frame_cycle loop initial.rip state af element.first)
  pc := rfl
  future := by
    intro first
    subst loop
    simpa only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      Loop.pointer, Loop.counter, reduceCtorEq, ite_false] using header.future rfl

/-- The first phase leaves both second-phase arguments intact; current unchanged
RAM supplies the second array even when the two immutable inputs overlap. -/
def switchHeader {initial state : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target)
    (header : Header initial valuesA valuesB .first state) (zero : header.count = 0) (af : Bool) :
    Header initial valuesA valuesB .second (exitState .first initial.rip state af) where
  remaining := valuesB
  count := valuesB.length
  accumulator := header.accumulator
  consumed := 0
  length := rfl
  countBound := pre.countB_lt
  counter := (header.future rfl).2
  pointer := by
    simpa [exitState, atPC, test, Loop.pointer]
      using (header.future rfl).1
  value := header.value
  array := by
    change ArrayAt state.memory (state.registers .rdx) valuesB
    rw [header.frame.memory, (header.future rfl).1]
    exact pre.arrayB
  split := by simp
  correct := by
    have empty : header.remaining = [] := List.eq_nil_of_length_eq_zero (header.length.trans zero)
    simpa [empty] using header.correct
  frame := header.frame.trans (frame_exit .first initial.rip state af)
  pc := rfl
  future := by intro impossible; cases impossible

theorem header_operand {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    (header : Header initial valuesA valuesB loop state) (element : Element header) (af : Bool) :
    loadDWord (body loop initial.rip state af).memory
      ((body loop initial.rip state af).registers loop.pointer) = .ok element.first := by
  have array := header.array
  rw [element.values] at array
  exact array.head

theorem header_read_member {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    (header : Header initial valuesA valuesB loop state) (element : Element header) :
    (⟨.data, state.registers loop.pointer, 4⟩ : Sequential.Read) ∈
      operandReads initial valuesA valuesB := by
  have inside : header.consumed < (if loop = .first then valuesA.length else valuesB.length) := by
    have split := header.split
    have count := element.count
    omega
  have member : (⟨.data, state.registers loop.pointer, 4⟩ : Sequential.Read) ∈
      inputReads (initial.registers loop.pointer)
        (if loop = .first then valuesA.length else valuesB.length) := by
    exact List.mem_map.mpr ⟨header.consumed, List.mem_range.mpr inside, by rw [header.pointer]⟩
  cases loop <;> simp only [reduceCtorEq, ite_true, ite_false, Loop.pointer] at member ⊢
  · simp only [operandReads, List.mem_append]
    exact Or.inl (Or.inl member)
  · simp only [operandReads, List.mem_append]
    exact Or.inl (Or.inr member)

theorem tested_zero {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    (header : Header initial valuesA valuesB loop state) (af : Bool) :
    (test loop state af).flags.getLsbD 6 = decide (header.count = 0) := by
  simp only [test, Sequential.logicalFlags64_zero, header.counter]
  have zero : BitVec.ofNat 64 header.count = 0 ↔ header.count = 0 := by
    constructor
    · intro zero
      have same := congrArg BitVec.toNat zero
      simpa [Nat.mod_eq_of_lt header.countBound] using same
    · intro zero; rw [zero]; rfl
  simp only [Bool.beq_eq_decide_eq, zero]

theorem guard_exit {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target)
    (header : Header initial valuesA valuesB loop state) (zero : header.count = 0) (af choice : Bool) :
    Sequential.execute (test loop state af) (.je 11) choice =
      .ok ⟨.next (exitState loop initial.rip state af), []⟩ := by
  have canonicalExit : canonical (initial.rip + BitVec.ofNat 64 loop.exitOffset) = true := by
    cases loop with
    | first => exact valid.canonical_node pre.code (⟨7, by decide⟩ : Index)
    | second => exact valid.canonical_node pre.code (⟨13, by decide⟩ : Index)
  have pc : (test loop state af).rip = initial.rip + (BitVec.ofNat 64 loop.headerOffset + 3) := by
    simp only [test, header.pc, BitVec.add_assoc]
  have displacement : BitVec.ofNat 64 loop.headerOffset + (3 + (2 + (11 : Byte).signExtend 64)) =
      BitVec.ofNat 64 loop.exitOffset := by cases loop <;> decide
  rw [Sequential.execute_je, tested_zero header af, zero]
  simp only [decide_true, executeShortBranch, ite_true, pc, BitVec.add_assoc,
    displacement, canonicalExit, ok_bind, pure_ok]
  rfl

theorem guard_body {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    (header : Header initial valuesA valuesB loop state) (element : Element header) (af choice : Bool) :
    Sequential.execute (test loop state af) (.je 11) choice =
      .ok ⟨.next (body loop initial.rip state af), []⟩ := by
  have nonzero : header.count ≠ 0 := by have count := element.count; omega
  have pc : (test loop state af).rip + 2 = initial.rip + BitVec.ofNat 64 loop.bodyOffset := by
    simp only [test, header.pc, BitVec.add_assoc]
    congr 1
    cases loop <;> decide
  rw [Sequential.execute_je, tested_zero header af]
  simp only [nonzero, decide_false, executeShortBranch, Bool.false_eq_true, ite_false,
    pc, ok_bind, pure_ok]
  rfl

theorem back_edge {initial state : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target)
    (header : Header initial valuesA valuesB loop state) (element : Element header) (af choice : Bool) :
    Sequential.execute (advance loop (decrement loop (load (body loop initial.rip state af) element.first)))
      (.jmp 240) choice = .ok ⟨.next (cycleState loop initial.rip state af element.first), []⟩ := by
  have canonicalHeader : canonical (initial.rip + BitVec.ofNat 64 loop.headerOffset) = true := by
    cases loop with
    | first => exact valid.canonical_node pre.code (⟨1, by decide⟩ : Index)
    | second => exact valid.canonical_node pre.code (⟨7, by decide⟩ : Index)
  have pc : (advance loop (decrement loop (load (body loop initial.rip state af) element.first))).rip =
      initial.rip + BitVec.ofNat 64 loop.backOffset := by
    simp only [advance, decrement, load, body, atPC, test, edit, State.writeRegister, BitVec.add_assoc]
    congr 1
    cases loop <;> decide
  have displacement : BitVec.ofNat 64 loop.backOffset + 2 + (240 : Byte).signExtend 64 =
      BitVec.ofNat 64 loop.headerOffset := by cases loop <;> decide
  rw [Sequential.execute_jmp]
  simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement,
    canonicalHeader, ok_bind, pure_ok]
  rfl

theorem zero_return {initial state : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target)
    (header : Header initial valuesA valuesB .second state) (af choice : Bool) :
    Sequential.execute (exitState .second initial.rip state af) (.legacy .ret) choice =
      .ok ⟨.returned (finish (exitState .second initial.rip state af) target),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have frame := header.frame.trans (frame_exit .second initial.rip state af)
  have stack : readWord (exitState .second initial.rip state af).memory
      ((exitState .second initial.rip state af).registers .rsp) = .ok target := by
    rw [frame.memory, frame.stack]
    exact pre.stack
  have returned : executeRet (exitState .second initial.rip state af) =
      .ok (finish (exitState .second initial.rip state af) target) := by
    unfold executeRet
    rw [stack]
    simp only [ok_bind, pre.canonicalTarget, ite_true, pure_ok]
    rfl
  simp only [Sequential.execute, X86.executeInstruction, returned, ok_bind, pure_ok,
    Sequential.Instruction.operandReads, frame.stack]

theorem zero_post {initial state : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (header : Header initial valuesA valuesB .second state) (zero : header.count = 0)
    (af : Bool) : Post initial valuesA valuesB target
      (finish (exitState .second initial.rip state af) target) := by
  have frame := header.frame.trans (frame_exit .second initial.rip state af)
  have correct : header.accumulator = pairSum valuesA valuesB := by
    have empty : header.remaining = [] := List.eq_nil_of_length_eq_zero (header.length.trans zero)
    simpa [empty] using header.correct
  refine ⟨?_, frame.memory, rfl, ?_, ?_, frame.flags⟩
  · simp only [finish, exitState, atPC, test, State.writeRegister, reduceCtorEq, ite_false,
      header.value, correct]
  · simp only [finish, State.writeRegister, ite_true, frame.stack]
  · intro register outside
    have different : register ≠ .rsp := by
      intro same
      subst register
      simp [clobbers] at outside
    simpa only [finish, State.writeRegister, ite_false, different] using frame.preserved register outside

end EDSL.Pair32
