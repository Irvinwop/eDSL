/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory
import EDSL.X86.Sequential.Model
import EDSL.X86.Flags

namespace EDSL.Stride32
open X86

/-- Select the even-index values of a logical contiguous input. The admitted
domain below supplies exactly twice `count` elements, so every lookup is in
range. This mathematical selection is independent of machine control flow. -/
def evenValues (values : List (BitVec 32)) (count : Nat) : List (BitVec 32) :=
  (List.range count).map fun index => values[2 * index]?.getD 0

def evenSum (values : List (BitVec 32)) (count : Nat) : BitVec 32 :=
  sum32 (evenValues values count)

@[simp] theorem evenValues_zero (values : List (BitVec 32)) : evenValues values 0 = [] := rfl
@[simp] theorem evenSum_zero (values : List (BitVec 32)) : evenSum values 0 = 0 := rfl

theorem evenValues_cons_pair (first second : BitVec 32) (values : List (BitVec 32))
    (count : Nat) : evenValues (first :: second :: values) (count + 1) =
      first :: evenValues values count := by
  simp only [evenValues, List.range_succ_eq_map, List.map_cons, Nat.mul_zero,
    List.getElem?_cons_zero, Option.getD_some, List.map_map]
  congr 1

theorem evenSum_cons_pair (first second : BitVec 32) (values : List (BitVec 32))
    (count : Nat) : evenSum (first :: second :: values) (count + 1) =
      first + evenSum values count := by
  rw [evenSum, evenValues_cons_pair, sum32_cons]
  rfl

/-- All current input cells belong to one contiguous logical array, including
the odd-index elements which the independent result contract ignores. -/
structure Pre (bytes : List Byte) (initial : State) (values : List (BitVec 32))
    (count : Nat) (target : Word) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  array : ArrayAt initial.memory (initial.registers .rdi) values
  bound : ArrayBound (initial.registers .rdi) values
  length : values.length = 2 * count
  count : initial.registers .rsi = BitVec.ofNat 64 count
  stack : readWord initial.memory (initial.registers .rsp) = .ok target
  canonicalTarget : canonical target = true
  canonicalStackAfter : canonical (initial.registers .rsp + 8) = true

def clobbers : List Register := [.rax, .rsi, .rdi, .rsp]

structure Post (initial : State) (values : List (BitVec 32)) (count : Nat)
    (target : Word) (final : State) : Prop where
  value : final.registers .rax = (evenSum values count).setWidth 64
  memory : final.memory = initial.memory
  returnAddress : final.rip = target
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- A mathematical footprint at even input indices, followed separately by RET.
There is no operand access to the odd trailing word or the one-past pointer. -/
def inputReads (base : Word) (count : Nat) : List Sequential.Read :=
  (List.range count).map fun index => ⟨.data, base + BitVec.ofNat 64 (8 * index), 4⟩

def operandReads (initial : State) (count : Nat) : List Sequential.Read :=
  inputReads (initial.registers .rdi) count ++ [⟨.stack, initial.registers .rsp, 8⟩]

theorem Pre.count_lt {bytes : List Byte} {initial : State} {values : List (BitVec 32)}
    {count : Nat} {target : Word} (admitted : Pre bytes initial values count target) : count < 2^64 := by
  have bound := admitted.bound.length_lt
  rw [admitted.length] at bound
  omega

end EDSL.Stride32
