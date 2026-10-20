/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Prologue

namespace EDSL.Sum32
open X86

structure Initialized (bytes : List Byte) (plan : Plan) (initial : State)
    (values : List (BitVec 32)) (target : Word) (state : State) : Prop
    extends Header bytes plan initial.rip state 0 target where
  effect : PrologueEffect plan.prologue initial state
  array : ArrayAt state.memory (state.registers .rdi) values
  count : state.registers .rsi = BitVec.ofNat 64 values.length
  countBound : values.length < 2^64
  index : plan.mode = .index → state.registers .rcx = 0
  base : state.registers .rdi = initial.registers .rdi
  stackPointer : state.registers .rsp = initial.registers .rsp

theorem initialization_enabled {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {initial : State} {values : List (BitVec 32)} {target : Word}
    (admitted : Pre bytes initial values target) (choices : Sequential.Choices) :
    ∃ middle, Sequential.Block choices initial middle plan.prologue.length [] ∧
      Initialized bytes plan initial values target middle := by
  have prologue := (Bool.and_eq_true_iff.mp valid.shape).1
  have pair := Bool.and_eq_true_iff.mp prologue
  have allowed := (Bool.and_eq_true_iff.mp pair.1).1
  have cleared := (Bool.and_eq_true_iff.mp pair.1).2
  obtain ⟨middle, execution, pc, effect⟩ := prologue_block valid plan.prologue
    (fun node member => plan.prologue_member member) allowed 0 plan.header valid.prologue
    initial admitted.code (by simp) choices
  have base : middle.registers .rdi = initial.registers .rdi := by
    have absent := plan.prologue_not_clears prologue .rdi (by decide) (by decide)
    simpa only [absent, Bool.false_eq_true, ite_false] using effect.registers .rdi
  have stackPointer : middle.registers .rsp = initial.registers .rsp := by
    have absent := plan.prologue_not_clears prologue .rsp (by decide) (by decide)
    simpa only [absent, Bool.false_eq_true, ite_false] using effect.registers .rsp
  have count : middle.registers .rsi = BitVec.ofNat 64 values.length := by
    have absent := plan.prologue_not_clears prologue .rsi (by decide) (by decide)
    have same : middle.registers .rsi = initial.registers .rsi := by
      simpa only [absent, Bool.false_eq_true, ite_false] using effect.registers .rsi
    exact same.trans admitted.count
  refine ⟨middle, execution, ?_⟩
  refine { code := ?_
           pc := pc
           accumulator := ?_
           stack := ?_
           canonicalTarget := admitted.canonicalTarget
           canonicalStackAfter := ?_
           effect := effect
           array := ?_
           count := count
           countBound := admitted.count_lt
           index := ?_
           base := base
           stackPointer := stackPointer }
  · rw [effect.memory]
    exact admitted.code
  · simpa [cleared] using effect.registers .rax
  · rw [effect.memory, stackPointer]
    exact admitted.stack
  · rw [stackPointer]
    exact admitted.canonicalStackAfter
  · rw [effect.memory, base]
    exact admitted.array
  · intro mode
    have zeroIndex : clears plan.prologue .rcx = true := by simpa only [mode] using pair.2
    simpa only [zeroIndex, ite_true] using effect.registers .rcx

theorem Initialized.preserved {bytes : List Byte} {plan : Plan} {initial state : State}
    {values : List (BitVec 32)} {target : Word}
    (ready : Initialized bytes plan initial values target state)
    (valid : Valid bytes plan) (register : Register) (outside : register ∉ clobbers) :
    state.registers register = initial.registers register := by
  have restrictions : register ≠ .rax ∧ register ≠ .rcx := by
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    exact ⟨outside.1, outside.2.1⟩
  have absent := plan.prologue_not_clears (Bool.and_eq_true_iff.mp valid.shape).1
    register restrictions.1 restrictions.2
  simpa only [absent, Bool.false_eq_true, ite_false] using ready.effect.registers register

theorem Initialized.pointer {bytes : List Byte} {plan : Plan} {initial state : State}
    {values : List (BitVec 32)} {target : Word}
    (ready : Initialized bytes plan initial values target state) :
    PointerHeader bytes plan initial.rip state values 0 target :=
  { toHeader := ready.toHeader, array := ready.array, count := ready.count, countBound := ready.countBound }

theorem Initialized.indexed {bytes : List Byte} {plan : Plan} {initial state : State}
    {values : List (BitVec 32)} {target : Word}
    (ready : Initialized bytes plan initial values target state) (mode : plan.mode = .index) :
    IndexHeader bytes plan initial.rip state values 0 target 0 values.length := by
  refine { toHeader := ready.toHeader
           array := ?_
           count := ready.count
           index := ?_
           remaining := by simp
           countBound := ready.countBound }
  · simpa using ready.array
  · simpa using ready.index mode

end EDSL.Sum32
