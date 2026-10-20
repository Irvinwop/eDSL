/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Model
import EDSL.Stride32.Resources

namespace EDSL.Stride32
open X86

def cycleState (base : Word) (state : State) (af : Bool) (value : BitVec 32) : State :=
  atPC (advance (decrement (load (body base state af) value))) (base + 2)

def exitState (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 18)

def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

def initialized {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) (af : Bool) :
    Header initial values count (clear initial af) where
  remaining := values
  count := count
  accumulator := 0
  consumed := 0
  length := pre.length
  countBound := pre.count_lt
  counter := pre.count
  pointer := by simp [clear, edit, State.writeRegister]
  value := by simp [clear, edit, State.writeRegister]
  array := pre.array
  split := by omega
  correct := by simp
  frame := frame_clear initial af
  pc := rfl

theorem frame_cycle (base : Word) (state : State) (af : Bool) (value : BitVec 32) :
    Frame state (cycleState base state af value) :=
  ((((frame_body base state af).trans (frame_load _ value)).trans (frame_decrement _)).trans
    (frame_advance _)).trans (frame_atPC _ _)

def nextHeader {initial state : State} {values : List (BitVec 32)} {total : Nat}
    (header : Header initial values total state) (pair : Pair header) (af : Bool) :
    Header initial values total (cycleState initial.rip state af pair.first) where
  remaining := pair.tail
  count := pair.rest
  accumulator := header.accumulator + pair.first
  consumed := header.consumed + 1
  length := by
    have length := header.length
    rw [pair.values, pair.count] at length
    simp only [List.length_cons] at length
    omega
  countBound := by have bound := header.countBound; rw [pair.count] at bound; omega
  counter := by
    simp only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      reduceCtorEq, ite_false, ite_true]
    rw [header.counter, pair.count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  pointer := by
    simp only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      reduceCtorEq, ite_false, ite_true]
    rw [header.pointer]
    simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  value := by
    simp [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      header.value]
  array := by
    have array := header.array
    rw [pair.values] at array
    have rest := array.tail.tail
    simpa only [cycleState, atPC, advance, decrement, load, body, test, edit, State.writeRegister,
      reduceCtorEq, ite_false, ite_true, BitVec.add_assoc, show (4 + 4 : Word) = 8 by decide] using rest
  split := by have split := header.split; rw [pair.count] at split; omega
  correct := by
    have correct := header.correct
    rw [pair.values, pair.count, evenSum_cons_pair] at correct
    simpa only [BitVec.add_assoc] using correct
  frame := header.frame.trans (frame_cycle initial.rip state af pair.first)
  pc := rfl

theorem header_operand {initial state : State} {values : List (BitVec 32)} {total : Nat}
    (header : Header initial values total state) (pair : Pair header) (af : Bool) :
    loadDWord (body initial.rip state af).memory
      ((body initial.rip state af).registers .rdi) = .ok pair.first := by
  have array := header.array
  rw [pair.values] at array
  exact array.head

theorem header_read_member {initial state : State} {values : List (BitVec 32)} {total : Nat}
    (header : Header initial values total state) (pair : Pair header) :
    (⟨.data, state.registers .rdi, 4⟩ : Sequential.Read) ∈ operandReads initial total := by
  have inside : header.consumed < total := by
    have split := header.split
    have count := pair.count
    omega
  simpa only [header.pointer] using data_read_member (initial := initial) inside

theorem tested_zero {initial state : State} {values : List (BitVec 32)} {total : Nat}
    (header : Header initial values total state) (af : Bool) :
    (test state af).flags.getLsbD 6 = decide (header.count = 0) := by
  simp only [test, Sequential.logicalFlags64_zero, header.counter]
  have zero : BitVec.ofNat 64 header.count = 0 ↔ header.count = 0 := by
    constructor
    · intro zero
      have same := congrArg BitVec.toNat zero
      simpa [Nat.mod_eq_of_lt header.countBound] using same
    · intro zero; rw [zero]; rfl
  simp only [Bool.beq_eq_decide_eq, zero]

theorem guard_exit {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (pre : Pre bytes initial values total target)
    (header : Header initial values total state) (zero : header.count = 0) (af choice : Bool) :
    Sequential.execute (test state af) (.je 11) choice =
      .ok ⟨.next (exitState initial.rip state af), []⟩ := by
  have canonicalExit : canonical (initial.rip + 18) = true := by
    exact valid.canonical_node pre.code (⟨7, by decide⟩ : Index)
  have pc : (test state af).rip = initial.rip + 5 := by
    simp only [test, header.pc, BitVec.add_assoc]
    rfl
  have displacement : (5 : Word) + 2 + (11 : Byte).signExtend 64 = 18 := by decide
  rw [Sequential.execute_je, tested_zero header af, zero]
  simp only [decide_true, executeShortBranch, ite_true, pc, BitVec.add_assoc,
    displacement, canonicalExit, ok_bind, pure_ok]
  rfl

theorem guard_body {initial state : State} {values : List (BitVec 32)} {total : Nat}
    (header : Header initial values total state) (pair : Pair header) (af choice : Bool) :
    Sequential.execute (test state af) (.je 11) choice =
      .ok ⟨.next (body initial.rip state af), []⟩ := by
  have nonzero : header.count ≠ 0 := by have count := pair.count; omega
  have pc : (test state af).rip + 2 = initial.rip + 7 := by
    simp only [test, header.pc, BitVec.add_assoc]
    rfl
  rw [Sequential.execute_je, tested_zero header af]
  simp only [nonzero, decide_false, executeShortBranch, Bool.false_eq_true, ite_false,
    pc, ok_bind, pure_ok]
  rfl

theorem back_edge {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (pre : Pre bytes initial values total target)
    (header : Header initial values total state) (pair : Pair header) (af choice : Bool) :
    Sequential.execute (advance (decrement (load (body initial.rip state af) pair.first)))
      (.jmp 240) choice = .ok ⟨.next (cycleState initial.rip state af pair.first), []⟩ := by
  have canonicalHeader : canonical (initial.rip + 2) = true := by
    exact valid.canonical_node pre.code (⟨1, by decide⟩ : Index)
  have pc : (advance (decrement (load (body initial.rip state af) pair.first))).rip =
      initial.rip + 16 := by
    simp only [advance, decrement, load, body, atPC, test, edit, State.writeRegister, BitVec.add_assoc]
    rfl
  have displacement : (16 : Word) + 2 + (240 : Byte).signExtend 64 = 2 := by decide
  rw [Sequential.execute_jmp]
  simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement,
    canonicalHeader, ok_bind, pure_ok]
  rfl

theorem zero_return {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (pre : Pre bytes initial values total target)
    (header : Header initial values total state) (af choice : Bool) :
    Sequential.execute (exitState initial.rip state af) (.legacy .ret) choice =
      .ok ⟨.returned (finish (exitState initial.rip state af) target),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  have frame : Frame initial (exitState initial.rip state af) :=
    header.frame.trans ((frame_test state af).trans (frame_atPC _ (initial.rip + 18)))
  have stack : readWord (exitState initial.rip state af).memory
      ((exitState initial.rip state af).registers .rsp) = .ok target := by
    rw [frame.memory, frame.stack]
    exact pre.stack
  have returned : executeRet (exitState initial.rip state af) =
      .ok (finish (exitState initial.rip state af) target) := by
    unfold executeRet
    rw [stack]
    simp only [ok_bind, pre.canonicalTarget, ite_true, pure_ok]
    rfl
  simp only [Sequential.execute, X86.executeInstruction, returned, ok_bind, pure_ok,
    Sequential.Instruction.operandReads, frame.stack]

theorem zero_post {initial state : State} {values : List (BitVec 32)} {total : Nat}
    {target : Word} (header : Header initial values total state) (zero : header.count = 0)
    (af : Bool) : Post initial values total target
      (finish (exitState initial.rip state af) target) := by
  have frame : Frame initial (exitState initial.rip state af) :=
    header.frame.trans ((frame_test state af).trans (frame_atPC _ (initial.rip + 18)))
  have correct : header.accumulator = evenSum values total := by
    simpa [zero] using header.correct
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

end EDSL.Stride32
