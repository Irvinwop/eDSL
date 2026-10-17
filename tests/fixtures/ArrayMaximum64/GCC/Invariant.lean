/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArrayMaximum64.GCC.Machine

set_option warningAsError true

namespace EDSL.ArrayMaximum64.GCC
open X86 X86.Sequential

/-- Only present-state memory, registers, provenance and independent suffix
mathematics occur here. No future execution is assumed. -/
structure Header (initial : State) (values remaining : List Word) (consumed : Nat)
    (state : State) : Prop where
  split : remaining.length + consumed = values.length
  counter : state.registers .rdx = BitVec.ofNat 64 consumed
  array : ArrayAt64 state.memory
    (initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)) remaining
  correct : maximumFrom (state.registers .rax).toNat remaining = maximumNat values
  frame : Frame initial state
  pc : state.rip = initial.rip + 4

def initialized (initial : State) (first second : Bool) : State :=
  clear (clear initial .rdx first) .rax second

theorem initialized_header {initial values target} (pre : Pre bytes initial values target)
    (first second : Bool) : Header initial values values 0 (initialized initial first second) where
  split := by omega
  counter := by simp [initialized,clear,edit,State.writeRegister]
  array := by simpa [initialized,clear,edit,State.writeRegister] using pre.array
  correct := by simp [initialized,clear,edit,State.writeRegister,maximumNat]
  frame := (frame_clear initial .rdx first (by decide) (by decide)).trans
    (frame_clear _ .rax second (by decide) (by decide))
  pc := by simp only [initialized,clear,edit,BitVec.add_assoc]; rfl

theorem Header.pointer {initial values remaining consumed state}
    (header : Header initial values remaining consumed state) :
    state.registers .rdi = initial.registers .rdi :=
  header.frame.preserved .rdi (by decide)

theorem Header.count {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target) :
    state.registers .rsi = BitVec.ofNat 64 values.length :=
  (header.frame.preserved .rsi (by decide)).trans pre.count

theorem Header.consumed_lt {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target) :
    consumed < 2^64 := by
  have length := pre.bound.length_lt
  have split := header.split
  omega

theorem Header.tested_zero {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target) :
    (test state).flags.getLsbD 6 = decide (remaining = []) := by
  have length := pre.bound.length_lt
  have consumedBound := header.consumed_lt pre
  have equal : BitVec.ofNat 64 consumed = BitVec.ofNat 64 values.length ↔ remaining = [] := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt consumedBound,Nat.mod_eq_of_lt length]
    have split := header.split
    constructor
    · intro same
      apply List.eq_nil_of_length_eq_zero
      omega
    · intro empty
      subst remaining
      simp only [List.length_nil,Nat.zero_add] at split
      exact split
  simp only [test,cmpFlags64_zero,header.counter,header.count pre,Bool.beq_eq_decide_eq,equal]

theorem indexed_address {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target) :
    (Address.indexed .rdi .rdx 3).eval state =
      initial.registers .rdi + BitVec.ofNat 64 (8 * consumed) := by
  have small := header.consumed_lt pre
  simp only [Address.eval,header.pointer,header.counter]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.shiftLeft_eq]
  congr 1
  exact Nat.mul_comm consumed 8

theorem body_operand {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target) :
    loadQWord (body initial.rip state).memory
      ((Address.indexed .rdi .rdx 3).eval (body initial.rip state)) = .ok value := by
  change loadQWord state.memory ((Address.indexed .rdi .rdx 3).eval state) = .ok value
  rw [indexed_address header pre]
  exact header.array.head

theorem next_header {initial values value rest consumed state}
    (header : Header initial values (value :: rest) consumed state) :
    Header initial values rest (consumed + 1) (cycle initial.rip state value) where
  split := by have split := header.split; simp only [List.length_cons] at split; omega
  counter := by
    change state.registers .rdx + 1 = BitVec.ofNat 64 (consumed + 1)
    rw [header.counter,BitVec.ofNat_add]
    rfl
  array := by
    have tail := header.array.tail
    have address : initial.registers .rdi + BitVec.ofNat 64 (8 * (consumed + 1)) =
        (initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)) + 8 := by
      simp only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    rw [address]
    exact tail
  correct := by rw [cycle_value,maximumFrom_step]; exact header.correct
  frame := header.frame.trans (frame_cycle initial.rip state value)
  pc := rfl

theorem empty_post {initial values consumed state target}
    (header : Header initial values [] consumed state) :
    Post initial values target (finish (exiting initial.rip state) target) := by
  have frame := header.frame.trans (frame_exiting initial.rip state)
  refine ⟨?_,frame.memory,rfl,?_,?_,frame.flags⟩
  · simpa only [finish,exiting,atPC,test,State.writeRegister,reduceCtorEq,ite_false,
      maximumFrom_nil] using header.correct
  · simp only [finish,State.writeRegister,ite_true,frame.stack]
  · intro register outside
    have different : register ≠ .rsp := by
      intro same
      subst register
      simp [clobbers] at outside
    simpa only [finish,State.writeRegister,different,ite_false] using frame.preserved register outside

end EDSL.ArrayMaximum64.GCC
