/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Clang.Machine
import EDSL.CountedStore64.Bridges

set_option warningAsError true

namespace EDSL.CountedStore64.Clang
open EDSL X86 X86.Sequential

/-- The current pre-return frame permits changes only to RAX/RDX, arithmetic
flags and the owned target's eight bytes. The complete code and caller slot
remain current across every actual store. -/
structure Frame (input : Input) (initial state : State) : Prop where
  code : CodeAt state.memory initial.rip bytes
  writable : canStoreQWord state.memory input.address = true
  stackRead : readWord state.memory (initial.registers .rsp) = .ok input.returnAddress
  outside : ∀ query, 8 ≤ (query - input.address).toNat →
    state.memory.read query = initial.memory.read query
  writableMap : state.memory.writable = initial.memory.writable
  executableMap : state.memory.executable = initial.memory.executable
  registers : ∀ register, register ≠ .rax → register ≠ .rdx →
    state.registers register = initial.registers register
  flags : state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.initial {input initial} (pre : Pre bytes input initial) :
    Frame input initial initial :=
  ⟨pre.memory.code, pre.memory.writable, pre.memory.stack, fun _ _ => rfl,
    rfl, rfl, fun _ _ _ => rfl, rfl⟩

theorem Frame.sameMemory {input initial before after}
    (frame : Frame input initial before) (memory : after.memory = before.memory)
    (registers : ∀ register, register ≠ .rax → register ≠ .rdx →
      after.registers register = before.registers register)
    (flags : after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask) :
    Frame input initial after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, flags.trans frame.flags⟩
  · rw [memory]; exact frame.code
  · rw [memory]; exact frame.writable
  · rw [memory]; exact frame.stackRead
  · intro query outside; rw [memory]; exact frame.outside query outside
  · rw [memory]; exact frame.writableMap
  · rw [memory]; exact frame.executableMap
  · intro register a d
    exact (registers register a d).trans (frame.registers register a d)

theorem Frame.move {input initial state} (frame : Frame input initial state) :
    Frame input initial (move state) :=
  frame.sameMemory rfl (by intros; simp_all [GCC.move, State.writeRegister]) rfl

theorem Frame.test {input initial state} (frame : Frame input initial state) (af : Bool) :
    Frame input initial (test state af) :=
  frame.sameMemory rfl (by intros; rfl) (logicalFlags64_preserves ..)

theorem Frame.atPC {input initial state} (frame : Frame input initial state) (pc : Word) :
    Frame input initial (atPC state pc) :=
  frame.sameMemory rfl (by intros; rfl) rfl

theorem Frame.increment {input initial state} (frame : Frame input initial state) :
    Frame input initial (increment state) :=
  frame.sameMemory rfl (by intros; simp_all [GCC.increment, State.writeRegister])
    (incFlags64_preserves ..)

theorem Frame.decrement {input initial state} (frame : Frame input initial state) :
    Frame input initial (decrement state) :=
  frame.sameMemory rfl (by intros; simp_all [GCC.decrement, State.writeRegister])
    (decFlags64_preserves ..)

theorem Frame.pointer {input initial state} (frame : Frame input initial state)
    (pre : Pre bytes input initial) : state.registers .rdi = input.address :=
  (frame.registers .rdi (by decide) (by decide)).trans pre.memory.pointer

theorem Frame.store {input initial state} (frame : Frame input initial state)
    (pre : Pre bytes input initial) : Frame input initial (store state) := by
  have pointer := frame.pointer pre
  refine ⟨?_, ?_, ?_, ?_, frame.writableMap, frame.executableMap,
    frame.registers, frame.flags⟩
  · apply writeQWord_preserves_code _ _ _ _ _ frame.code
    simpa only [pointer] using pre.memory.codeDisjoint
  · simpa only [GCC.store, pointer] using
      canStoreQWord_after_write state.memory input.address (state.registers .rax) frame.writable
  · apply (readWord_congr _ _ _ (writeQWord_agrees _ _ _ _ 8 ?_)).trans frame.stackRead
    simpa only [pointer] using pre.memory.stackDisjoint
  · intro query outside
    exact (writeQWord_frame state.memory _ query _
      (by simpa only [pointer] using outside)).trans (frame.outside query outside)

/-- A completed-store count partitions the original full64 count with RDX.
PC is deliberately absent: completion after DEC may next branch either to
the body or to RET. The STORE-before-DEC intermediate is not settled. -/
structure Settled (input : Input) (initial state : State) where
  completed : Nat
  split : completed + (state.registers .rdx).toNat = input.count.toNat
  value : state.registers .rax = input.argument + BitVec.ofNat 64 completed
  stored : loadQWord state.memory input.address =
    .ok (if completed = 0 then input.oldValue else input.argument + BitVec.ofNat 64 completed)
  frame : Frame input initial state

/-- The loop cutpoint is the actual INC location with a nonzero full64 RDX. -/
structure Header (input : Input) (initial state : State) extends Settled input initial state where
  pc : state.rip = initial.rip + 8
  nonzero : state.registers .rdx ≠ 0

/-- The actual RET location is reached only with the full remaining count zero. -/
structure Exit (input : Input) (initial state : State) extends Settled input initial state where
  pc : state.rip = initial.rip + 19
  zero : state.registers .rdx = 0

def initialized {input initial} (pre : Pre bytes input initial) :
    Settled input initial (move initial) where
  completed := 0
  split := by simpa [GCC.move, State.writeRegister] using congrArg BitVec.toNat pre.count
  value := by simp [GCC.move, State.writeRegister, pre.memory.source]
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
    Header input initial (Clang.atPC state (initial.rip + 8)) where
  toSettled := settled.atPC _
  pc := rfl
  nonzero := nonzero

def Settled.toExit {input initial state} (settled : Settled input initial state)
    (zero : state.registers .rdx = 0) :
    Exit input initial (Clang.atPC state (initial.rip + 19)) where
  toSettled := settled.atPC _
  pc := rfl
  zero := zero

def body (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 8)

def exitState (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 19)

def initialHeader {input initial} (pre : Pre bytes input initial)
    (nonzero : initial.registers .rdx ≠ 0) (af : Bool) :
    Header input initial (body initial.rip (move initial) af) :=
  ((initialized pre).test af).toHeader
    (by simpa only [GCC.test, GCC.move, State.writeRegister, reduceCtorEq, ite_false] using nonzero)

def initialExit {input initial} (pre : Pre bytes input initial)
    (zero : initial.registers .rdx = 0) (af : Bool) :
    Exit input initial (exitState initial.rip (move initial) af) :=
  ((initialized pre).test af).toExit
    (by simpa only [GCC.test, GCC.move, State.writeRegister, reduceCtorEq, ite_false] using zero)

def entry_body {input initial} (pre : Pre bytes input initial) (af : Bool)
    (nonzero : initial.registers .rdx ≠ 0) :
    Header input initial (body initial.rip (move initial) af) :=
  initialHeader pre nonzero af

def entry_exit {input initial} (pre : Pre bytes input initial) (af : Bool)
    (zero : initial.registers .rdx = 0) :
    Exit input initial (exitState initial.rip (move initial) af) :=
  initialExit pre zero af

def incState (state : State) : State := increment state
def storedState (state : State) : State := store (incState state)
def decState (state : State) : State := decrement (storedState state)
def continued (base : Word) (state : State) : State := atPC (decState state) (base + 8)
def exited (base : Word) (state : State) : State := atPC (decState state) (base + 19)

theorem decrement_count (count : Word) (nonzero : count ≠ 0) :
    (count - 1).toNat + 1 = count.toNat := by
  have positive := BitVec.toNat_pos_of_ne_zero nonzero
  rw [BitVec.toNat_sub_of_le (by change (1 : Nat) ≤ count.toNat; omega)]
  change count.toNat - 1 + 1 = count.toNat
  omega

theorem incState_frame {input initial state} (header : Header input initial state) :
    Frame input initial (incState state) := header.frame.increment

theorem storedState_frame {input initial state} (pre : Pre bytes input initial)
    (header : Header input initial state) : Frame input initial (storedState state) :=
  (incState_frame header).store pre

theorem decState_frame {input initial state} (pre : Pre bytes input initial)
    (header : Header input initial state) : Frame input initial (decState state) :=
  (storedState_frame pre header).decrement

/-- Only after DEC do the advanced value and completed store agree with the
decreased full64 count. No settled assertion is made immediately after STORE. -/
def nextSettled {input initial state} (pre : Pre bytes input initial)
    (header : Header input initial state) : Settled input initial (decState state) where
  completed := header.completed + 1
  split := by
    have split := header.split
    have decreased := decrement_count (state.registers .rdx) header.nonzero
    simp only [decState, storedState, incState, GCC.decrement, GCC.store, GCC.increment,
      State.writeRegister, reduceCtorEq, ite_true, ite_false]
    omega
  value := by
    simp only [decState, storedState, incState, GCC.decrement, GCC.store, GCC.increment,
      State.writeRegister, reduceCtorEq, ite_true, ite_false, header.value]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  stored := by
    have pointer := (incState_frame header).pointer pre
    have value : (incState state).registers .rax =
        input.argument + BitVec.ofNat 64 (header.completed + 1) := by
      simp [incState, GCC.increment, State.writeRegister,
        header.value, BitVec.ofNat_add, BitVec.add_assoc]
    change loadQWord (writeQWordUnchecked (incState state).memory
      ((incState state).registers .rdi) ((incState state).registers .rax))
      input.address = .ok _
    rw [pointer, value]
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using
      qword_load_after_write (incState state).memory input.address
        (input.argument + BitVec.ofNat 64 (header.completed + 1)) pre.memory.target_addressable
  frame := decState_frame pre header

def nextHeader {input initial state} (pre : Pre bytes input initial)
    (header : Header input initial state) (nonzero : (decState state).registers .rdx ≠ 0) :
    Header input initial (continued initial.rip state) :=
  (nextSettled pre header).toHeader nonzero

def nextExit {input initial state} (pre : Pre bytes input initial)
    (header : Header input initial state) (zero : (decState state).registers .rdx = 0) :
    Exit input initial (exited initial.rip state) :=
  (nextSettled pre header).toExit zero

theorem rank_decreases {input initial state} (header : Header input initial state) :
    ((decState state).registers .rdx).toNat < (state.registers .rdx).toNat := by
  have decreased := decrement_count (state.registers .rdx) header.nonzero
  simpa only [decState, storedState, incState, GCC.decrement, GCC.store, GCC.increment,
    State.writeRegister, reduceCtorEq, ite_true, ite_false] using (by omega :
      (state.registers .rdx - 1).toNat < (state.registers .rdx).toNat)

/-- The RET state's settled value and zero remaining count entail the
independent callable result, memory/permission/ABI frames and real return. -/
theorem exit_post {input initial state} (_pre : Pre bytes input initial)
    (exit : Exit input initial state) : Post input initial (finish state input.returnAddress) := by
  have completed : exit.completed = input.count.toNat := by
    have split := exit.split
    simpa [exit.zero] using split
  have value : state.registers .rax = input.argument + input.count := by
    simpa only [completed, BitVec.ofNat_toNat, BitVec.setWidth_eq] using exit.value
  have zero_iff : exit.completed = 0 ↔ input.count = 0 := by
    rw [completed, ← BitVec.toNat_inj]
    rfl
  have countZero : input.count.toNat = 0 ↔ input.count = 0 := by
    simpa only [completed] using zero_iff
  have frame := exit.frame
  refine ⟨?_, ?_, frame.outside, frame.writableMap, frame.executableMap, rfl, ?_, ?_, frame.flags⟩
  · simpa only [GCC.finish, State.writeRegister, reduceCtorEq, ite_false] using value
  · have stored := exit.stored
    simp only [completed, countZero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at stored
    simpa only [GCC.finish, State.writeRegister, expectedValue] using stored
  · simp only [GCC.finish, State.writeRegister, ite_true]
    exact congrArg (· + 8) (frame.registers .rsp (by decide) (by decide))
  · intro register member
    have a : register ≠ .rax := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have d : register ≠ .rdx := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have s : register ≠ .rsp := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    simpa only [GCC.finish, State.writeRegister, s, ite_false] using frame.registers register a d

end EDSL.CountedStore64.Clang
