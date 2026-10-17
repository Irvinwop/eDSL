/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.GCC
import EDSL.CountedStore64.Frame
import EDSL.CountedStore64.Bridges

set_option warningAsError true

namespace EDSL.CountedStore64.GCC
open EDSL X86 X86.Sequential

/-- A pre-return frame allows only RAX/RDX and the owned eight target bytes
to change. Code, the original caller slot and all permissions stay current. -/
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

/-- Completed stores and full-width remaining count partition the original
natural count. The pending increment before STORE is kept out of this header. -/
structure Header (input : Input) (initial state : State) where
  completed : Nat
  split : completed + (state.registers .rdx).toNat = input.count.toNat
  value : state.registers .rax = input.argument + BitVec.ofNat 64 completed
  stored : loadQWord state.memory input.address =
    .ok (if completed = 0 then input.oldValue else input.argument + BitVec.ofNat 64 completed)
  frame : Frame input initial state
  pc : state.rip = initial.rip + 3

def initialized {input initial} (pre : Pre bytes input initial) :
    Header input initial (move initial) where
  completed := 0
  split := by simpa [move, State.writeRegister] using congrArg BitVec.toNat pre.count
  value := by simp [move, State.writeRegister, pre.memory.source]
  stored := pre.memory.oldValue
  frame := (Frame.initial pre).move
  pc := rfl

def body (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 8)

def pending (base : Word) (state : State) (af : Bool) : State :=
  decrement (increment (body base state af))

def cycle (base : Word) (state : State) (af : Bool) : State :=
  atPC (store (pending base state af)) (base + 3)

def exitState (base : Word) (state : State) (af : Bool) : State :=
  atPC (test state af) (base + 19)

theorem decrement_count (count : Word) (nonzero : count ≠ 0) :
    (count - 1).toNat + 1 = count.toNat := by
  have positive := BitVec.toNat_pos_of_ne_zero nonzero
  rw [BitVec.toNat_sub_of_le (by change (1 : Nat) ≤ count.toNat; omega)]
  change count.toNat - 1 + 1 = count.toNat
  omega

theorem pending_frame {input initial state} (header : Header input initial state) (af : Bool) :
    Frame input initial (pending initial.rip state af) :=
  (((header.frame.test af).atPC _).increment).decrement

def nextHeader {input initial state} (pre : Pre bytes input initial)
    (header : Header input initial state) (nonzero : state.registers .rdx ≠ 0) (af : Bool) :
    Header input initial (cycle initial.rip state af) where
  completed := header.completed + 1
  split := by
    have split := header.split
    have decreased := decrement_count (state.registers .rdx) nonzero
    simp only [cycle, store, pending, decrement, increment, body, atPC, test,
      State.writeRegister, reduceCtorEq, ite_true, ite_false]
    omega
  value := by
    simp only [cycle, store, pending, decrement, increment, body, atPC, test,
      State.writeRegister, reduceCtorEq, ite_true, ite_false, header.value]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  stored := by
    have pointer := (pending_frame header af).pointer pre
    have value : (pending initial.rip state af).registers .rax =
        input.argument + BitVec.ofNat 64 (header.completed + 1) := by
      simp [pending, decrement, increment, body, atPC, test, State.writeRegister,
        header.value, BitVec.ofNat_add, BitVec.add_assoc]
    change loadQWord (writeQWordUnchecked (pending initial.rip state af).memory
      ((pending initial.rip state af).registers .rdi) ((pending initial.rip state af).registers .rax))
      input.address = .ok _
    rw [pointer, value]
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using
      qword_load_after_write (pending initial.rip state af).memory input.address
        (input.argument + BitVec.ofNat 64 (header.completed + 1)) pre.memory.target_addressable
  frame := ((pending_frame header af).store pre).atPC _
  pc := rfl

theorem rank_decreases {input initial state} (_header : Header input initial state)
    (nonzero : state.registers .rdx ≠ 0) (af : Bool) :
    ((cycle initial.rip state af).registers .rdx).toNat < (state.registers .rdx).toNat := by
  have decreased := decrement_count (state.registers .rdx) nonzero
  simpa only [cycle, atPC, store, pending, decrement, increment, body, test,
    State.writeRegister, reduceCtorEq, ite_true, ite_false] using (by omega :
      (state.registers .rdx - 1).toNat < (state.registers .rdx).toNat)

theorem exit_post {input initial state} (_pre : Pre bytes input initial)
    (header : Header input initial state) (zero : state.registers .rdx = 0) (af : Bool) :
    Post input initial (finish (exitState initial.rip state af) input.returnAddress) := by
  have completed : header.completed = input.count.toNat := by
    have split := header.split
    simpa [zero] using split
  have value : state.registers .rax = input.argument + input.count := by
    simpa only [completed, BitVec.ofNat_toNat, BitVec.setWidth_eq] using header.value
  have zero_iff : header.completed = 0 ↔ input.count = 0 := by
    rw [completed, ← BitVec.toNat_inj]
    rfl
  have countZero : input.count.toNat = 0 ↔ input.count = 0 := by
    simpa only [completed] using zero_iff
  have frame := (header.frame.test af).atPC (initial.rip + 19)
  refine ⟨?_, ?_, frame.outside, frame.writableMap, frame.executableMap, rfl, ?_, ?_, frame.flags⟩
  · simpa [finish, exitState, atPC, test, State.writeRegister] using value
  · have stored := header.stored
    simp only [completed, countZero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at stored
    simpa only [finish, State.writeRegister, exitState, atPC, test, expectedValue,
      BitVec.ofNat_toNat, BitVec.setWidth_eq] using stored
  · simp only [finish, State.writeRegister, ite_true]
    exact congrArg (· + 8) (frame.registers .rsp (by decide) (by decide))
  · intro register member
    have a : register ≠ .rax := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have d : register ≠ .rdx := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    have s : register ≠ .rsp := by intro same; subst register; simp [StoreLoad64.calleeSaved] at member
    simpa only [finish, State.writeRegister, s, ite_false, exitState] using frame.registers register a d

end EDSL.CountedStore64.GCC
