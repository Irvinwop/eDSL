/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Contract
import EDSL.Sum32.Code
import EDSL.X86.Sequential.Execution

namespace EDSL.Sum32
open X86

/-- A return from a loop header may start with an already accumulated prefix.
Its result is still the same independent mathematical sum. -/
structure LoopPost (initial : State) (accumulator : BitVec 32) (remaining : List (BitVec 32))
    (target : Word) (final : State) : Prop where
  value : final.registers .rax = (accumulator + sum32 remaining).setWidth 64
  memory : final.memory = initial.memory
  returnAddress : final.rip = target
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

structure Header (bytes : List Byte) (plan : Plan) (base : Word) (state : State)
    (accumulator : BitVec 32) (target : Word) : Prop where
  code : CodeAt state.memory base bytes
  pc : state.rip = base + BitVec.ofNat 64 plan.header
  accumulator : state.registers .rax = accumulator.setWidth 64
  stack : readWord state.memory (state.registers .rsp) = .ok target
  canonicalTarget : canonical target = true
  canonicalStackAfter : canonical (state.registers .rsp + 8) = true

structure PointerHeader (bytes : List Byte) (plan : Plan) (base : Word) (state : State)
    (values : List (BitVec 32)) (accumulator : BitVec 32) (target : Word) : Prop
    extends Header bytes plan base state accumulator target where
  array : ArrayAt state.memory (state.registers .rdi) values
  count : state.registers .rsi = BitVec.ofNat 64 values.length
  countBound : values.length < 2^64

structure IndexHeader (bytes : List Byte) (plan : Plan) (base : Word) (state : State)
    (values : List (BitVec 32)) (accumulator : BitVec 32) (target : Word)
    (consumed total : Nat) : Prop
    extends Header bytes plan base state accumulator target where
  array : ArrayAt state.memory (state.registers .rdi + BitVec.ofNat 64 (4 * consumed)) values
  count : state.registers .rsi = BitVec.ofNat 64 total
  index : state.registers .rcx = BitVec.ofNat 64 consumed
  remaining : consumed + values.length = total
  countBound : total < 2^64

def pointerReads (state : State) (values : List (BitVec 32)) : List Sequential.Read :=
  inputReads (state.registers .rdi) values ++ [⟨.stack, state.registers .rsp, 8⟩]

def indexReads (state : State) (consumed : Nat) (values : List (BitVec 32)) : List Sequential.Read :=
  inputReads (state.registers .rdi + BitVec.ofNat 64 (4 * consumed)) values ++
    [⟨.stack, state.registers .rsp, 8⟩]

theorem LoopPost.zero {initial final : State} {values : List (BitVec 32)} {target : Word}
    (result : LoopPost initial 0 values target final) : Post initial values target final := by
  refine ⟨?_, result.memory, result.returnAddress, result.stackPointer, result.preserved, result.flags⟩
  simpa using result.value

end EDSL.Sum32
