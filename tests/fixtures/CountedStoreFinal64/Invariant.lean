/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreFinal64.Machine
import EDSL.CountedStore64.Frame
import EDSL.CountedStore64.Bridges

set_option warningAsError true

namespace EDSL.CountedStoreFinal64
open EDSL CountedStore64 X86 X86.Sequential

/-- The shared frame is parameterized by arbitrary admitted candidate bytes. -/
abbrev Frame := Common.Frame bytes

namespace Frame
abbrev initial := @Common.Frame.initial bytes
end Frame

/-- Completed register increments partition the original full64 count with
RDX. The target still contains its admitted old value throughout the loop. -/
structure Settled (input : Input) (initial state : State) where
  completed : Nat
  split : completed + (state.registers .rdx).toNat = input.count.toNat
  value : state.registers .rax = input.argument + BitVec.ofNat 64 completed
  stored : loadQWord state.memory input.address = .ok input.oldValue
  frame : Frame input initial state

structure Header (input : Input) (initial state : State) extends Settled input initial state where
  pc : state.rip = initial.rip + 8
  nonzero : state.registers .rdx ≠ 0

/-- The one STORE is reached after a positive-count loop has exhausted RDX.
Its input memory still holds the original target value. -/
structure Ready (input : Input) (initial state : State) extends Settled input initial state where
  pc : state.rip = initial.rip + 16
  zero : state.registers .rdx = 0
  positive : input.count ≠ 0

/-- The actual RET state has the independent complete result. It arises
either from the zero-count guard or from the one positive-count STORE. -/
structure Exit (input : Input) (initial state : State) : Prop where
  result : state.registers .rax = input.argument + input.count
  stored : loadQWord state.memory input.address = .ok (expectedValue input)
  frame : Frame input initial state
  pc : state.rip = initial.rip + 19
  zero : state.registers .rdx = 0

def initialized {input initial} (pre : Pre bytes input initial) :
    Settled input initial (move initial) where
  completed := 0
  split := by simpa [CountedStore64.GCC.move, State.writeRegister] using congrArg BitVec.toNat pre.count
  value := by simp [CountedStore64.GCC.move, State.writeRegister, pre.memory.source]
  stored := pre.memory.oldValue
  frame := (Frame.initial pre).move

def Settled.test {input initial state} (settled : Settled input initial state) (af : Bool) :
    Settled input initial (test state af) where
  completed := settled.completed
  split := settled.split
  value := settled.value
  stored := settled.stored
  frame := settled.frame.test af

def Settled.atPC {input initial state} (settled : Settled input initial state) (pc : Word) :
    Settled input initial (atPC state pc) where
  completed := settled.completed
  split := settled.split
  value := settled.value
  stored := settled.stored
  frame := settled.frame.atPC pc

def Settled.toHeader {input initial state} (settled : Settled input initial state)
    (nonzero : state.registers .rdx ≠ 0) :
    Header input initial (CountedStoreFinal64.atPC state (initial.rip + 8)) where
  toSettled := settled.atPC _
  pc := rfl
  nonzero := nonzero

theorem Settled.completed_of_zero {input initial state} (settled : Settled input initial state)
    (zero : state.registers .rdx = 0) : settled.completed = input.count.toNat := by
  have split := settled.split
  simpa [zero] using split

theorem Settled.result_of_zero {input initial state} (settled : Settled input initial state)
    (zero : state.registers .rdx = 0) : state.registers .rax = input.argument + input.count := by
  simpa only [settled.completed_of_zero zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    using settled.value

def body (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 8)

def exitState (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 19)

def initialHeader {input initial} (pre : Pre bytes input initial)
    (nonzero : initial.registers .rdx ≠ 0) (af : Bool) :
    Header input initial (body initial.rip (move initial) af) :=
  ((initialized pre).test af).toHeader
    (by simpa only [CountedStore64.GCC.test, CountedStore64.GCC.move,
      State.writeRegister, reduceCtorEq, ite_false] using nonzero)

theorem initialExit {input initial} (pre : Pre bytes input initial)
    (zero : initial.registers .rdx = 0) (af : Bool) :
    Exit input initial (exitState initial.rip (move initial) af) := by
  have settled := ((initialized pre).test af).atPC (initial.rip + 19)
  have stillZero : (exitState initial.rip (move initial) af).registers .rdx = 0 := by
    simpa only [exitState, CountedStore64.GCC.atPC, CountedStore64.GCC.test,
      CountedStore64.GCC.move, State.writeRegister, reduceCtorEq, ite_false] using zero
  have countZero : input.count = 0 := pre.count.symm.trans zero
  exact ⟨settled.result_of_zero stillZero, by
    simpa only [exitState, expectedValue, countZero, ite_true] using settled.stored,
    settled.frame, rfl, stillZero⟩

def entry_body {input initial} (pre : Pre bytes input initial) (af : Bool)
    (nonzero : initial.registers .rdx ≠ 0) :
    Header input initial (body initial.rip (move initial) af) :=
  initialHeader pre nonzero af

theorem entry_exit {input initial} (pre : Pre bytes input initial) (af : Bool)
    (zero : initial.registers .rdx = 0) :
    Exit input initial (exitState initial.rip (move initial) af) :=
  initialExit pre zero af

def incState (state : State) : State := increment state
def decState (state : State) : State := decrement (incState state)
def continued (base : Word) (state : State) : State := atPC (decState state) (base + 8)
def toStore (base : Word) (state : State) : State := atPC (decState state) (base + 16)
def storedState (base : Word) (state : State) : State := store (toStore base state)

theorem decrement_count (count : Word) (nonzero : count ≠ 0) :
    (count - 1).toNat + 1 = count.toNat := by
  have positive := BitVec.toNat_pos_of_ne_zero nonzero
  rw [BitVec.toNat_sub_of_le (by change (1 : Nat) ≤ count.toNat; omega)]
  change count.toNat - 1 + 1 = count.toNat
  omega

theorem incState_frame {input initial state} (header : Header input initial state) :
    Frame input initial (incState state) := header.frame.increment

theorem decState_frame {input initial state} (header : Header input initial state) :
    Frame input initial (decState state) := (incState_frame header).decrement

/-- INC and DEC advance only the register computation. No target write has
occurred when this new settled state is established. -/
def nextSettled {input initial state} (header : Header input initial state) :
    Settled input initial (decState state) where
  completed := header.completed + 1
  split := by
    have split := header.split
    have decreased := decrement_count (state.registers .rdx) header.nonzero
    simp only [decState, incState, CountedStore64.GCC.decrement, CountedStore64.GCC.increment,
      State.writeRegister, reduceCtorEq, ite_true, ite_false]
    omega
  value := by
    simp only [decState, incState, CountedStore64.GCC.decrement, CountedStore64.GCC.increment,
      State.writeRegister, reduceCtorEq, ite_true, ite_false, header.value]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  stored := header.stored
  frame := decState_frame header

def nextHeader {input initial state} (_pre : Pre bytes input initial)
    (header : Header input initial state) (nonzero : (decState state).registers .rdx ≠ 0) :
    Header input initial (continued initial.rip state) :=
  (nextSettled header).toHeader nonzero

def nextReady {input initial state} (_pre : Pre bytes input initial)
    (header : Header input initial state) (zero : (decState state).registers .rdx = 0) :
    Ready input initial (toStore initial.rip state) where
  toSettled := (nextSettled header).atPC _
  pc := rfl
  zero := zero
  positive := by
    intro countZero
    have split := header.split
    have positive := BitVec.toNat_pos_of_ne_zero header.nonzero
    simp [countZero] at split
    omega

/-- This is the sole transition that replaces the old target with the final
full64 result; the caller's code/stack/permissions remain framed. -/
theorem storedExit {input initial state} (pre : Pre bytes input initial)
    (ready : Ready input initial state) : Exit input initial (store state) := by
  have result := ready.toSettled.result_of_zero ready.zero
  have pointer := ready.frame.pointer pre
  refine ⟨result, ?_, ready.frame.store pre, ?_, ready.zero⟩
  · change loadQWord (writeQWordUnchecked state.memory
      (state.registers .rdi) (state.registers .rax)) input.address = .ok _
    rw [pointer, result]
    simpa only [expectedValue, ready.positive, ite_false] using
      qword_load_after_write state.memory input.address (input.argument + input.count)
        pre.memory.target_addressable
  · simp only [CountedStore64.GCC.store, ready.pc, BitVec.add_assoc]
    rfl

theorem rank_decreases {input initial state} (header : Header input initial state) :
    ((decState state).registers .rdx).toNat < (state.registers .rdx).toNat := by
  have decreased := decrement_count (state.registers .rdx) header.nonzero
  simpa only [decState, incState, CountedStore64.GCC.decrement, CountedStore64.GCC.increment,
    State.writeRegister, reduceCtorEq, ite_true, ite_false] using (by omega :
      (state.registers .rdx - 1).toNat < (state.registers .rdx).toNat)

theorem exit_post {input initial state} (_pre : Pre bytes input initial)
    (exit : Exit input initial state) : Post input initial (finish state input.returnAddress) := by
  have frame := exit.frame
  refine ⟨?_, ?_, frame.outside, frame.writableMap, frame.executableMap, rfl, ?_, ?_, frame.flags⟩
  · simpa only [CountedStore64.GCC.finish, State.writeRegister, reduceCtorEq, ite_false]
      using exit.result
  · exact exit.stored
  · simp only [CountedStore64.GCC.finish, State.writeRegister, ite_true]
    exact congrArg (· + 8) (frame.registers .rsp (by decide) (by decide))
  · intro register member
    have a : register ≠ .rax := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have d : register ≠ .rdx := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have s : register ≠ .rsp := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    simpa only [CountedStore64.GCC.finish, State.writeRegister, s, ite_false]
      using frame.registers register a d

end EDSL.CountedStoreFinal64
