/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory
import EDSL.X86.Sequential.Model
import EDSL.X86.Flags

namespace EDSL.Pair32
open X86

/-- The sum of two mathematical lists, independently of control flow, argument
registers, and instruction selection. Both additions are modulo 2^32. -/
def pairSum (valuesA valuesB : List (BitVec 32)) : BitVec 32 := sum32 (valuesA ++ valuesB)

theorem pairSum_eq (valuesA valuesB : List (BitVec 32)) :
    pairSum valuesA valuesB = sum32 valuesA + sum32 valuesB := sum32_append valuesA valuesB

/-- Two current contiguous arrays may alias when their contents agree. Neither
empty input imposes a readability or canonicality condition on its pointer. -/
structure Pre (bytes : List Byte) (initial : State) (valuesA valuesB : List (BitVec 32))
    (target : Word) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  arrayA : ArrayAt initial.memory (initial.registers .rdi) valuesA
  arrayB : ArrayAt initial.memory (initial.registers .rdx) valuesB
  boundA : ArrayBound (initial.registers .rdi) valuesA
  boundB : ArrayBound (initial.registers .rdx) valuesB
  countA : initial.registers .rsi = BitVec.ofNat 64 valuesA.length
  countB : initial.registers .rcx = BitVec.ofNat 64 valuesB.length
  stack : readWord initial.memory (initial.registers .rsp) = .ok target
  canonicalTarget : canonical target = true
  canonicalStackAfter : canonical (initial.registers .rsp + 8) = true

def clobbers : List Register := [.rax, .rsi, .rdi, .rcx, .rdx, .rsp]

structure Post (initial : State) (valuesA valuesB : List (BitVec 32))
    (target : Word) (final : State) : Prop where
  value : final.registers .rax = (pairSum valuesA valuesB).setWidth 64
  memory : final.memory = initial.memory
  returnAddress : final.rip = target
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- An independently enumerated footprint: all four-byte A operands, then all B
operands, followed by the complete eight-byte return slot. -/
def inputReads (base : Word) (count : Nat) : List Sequential.Read :=
  (List.range count).map fun index => ⟨.data, base + BitVec.ofNat 64 (4 * index), 4⟩

def operandReads (initial : State) (valuesA valuesB : List (BitVec 32)) : List Sequential.Read :=
  inputReads (initial.registers .rdi) valuesA.length ++
    inputReads (initial.registers .rdx) valuesB.length ++ [⟨.stack, initial.registers .rsp, 8⟩]

theorem Pre.countA_lt {bytes : List Byte} {initial : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target) : valuesA.length < 2^64 :=
  pre.boundA.length_lt

theorem Pre.countB_lt {bytes : List Byte} {initial : State} {valuesA valuesB : List (BitVec 32)}
    {target : Word} (pre : Pre bytes initial valuesA valuesB target) : valuesB.length < 2^64 :=
  pre.boundB.length_lt

end EDSL.Pair32
