/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory64
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Grading.Policy

set_option warningAsError true

namespace EDSL.ArraySum64
open X86 X86.Sequential

/-- Mathematical unsigned sum in the naturals, independent of machine
registers, instruction evaluation and control flow. No intermediate truncation. -/
def sumNat (values : List Word) : Nat := (values.map fun value => value.toNat).sum

/-- The independent result is reduced only after the mathematical sum. -/
def sumMod (values : List Word) : Nat := sumNat values % 2^64

/-- A word representation of the independent mathematical result. -/
def sumWord (values : List Word) : Word := BitVec.ofNat 64 (sumNat values)

@[simp] theorem sumNat_nil : sumNat [] = 0 := rfl

@[simp] theorem sumNat_cons (value : Word) (rest : List Word) :
    sumNat (value :: rest) = value.toNat + sumNat rest := by
  simp [sumNat]

theorem sumNat_append (left right : List Word) :
    sumNat (left ++ right) = sumNat left + sumNat right := by
  simp [sumNat, List.sum_append]

/-- Prefix/suffix reasoning uses the ordinary list decomposition. -/
theorem sumNat_take_drop (values : List Word) (count : Nat) :
    sumNat (values.take count) + sumNat (values.drop count) = sumNat values := by
  rw [← sumNat_append, List.take_append_drop]

@[simp] theorem sumMod_nil : sumMod [] = 0 := rfl

theorem sumMod_cons (value : Word) (rest : List Word) :
    sumMod (value :: rest) = (value.toNat + sumMod rest) % 2^64 := by
  simp only [sumMod, sumNat_cons, Nat.add_mod_mod]

theorem sumMod_append (left right : List Word) :
    sumMod (left ++ right) = (sumMod left + sumMod right) % 2^64 := by
  simp only [sumMod, sumNat_append, Nat.mod_add_mod, Nat.add_mod_mod]

theorem sumMod_lt (values : List Word) : sumMod values < 2^64 :=
  Nat.mod_lt _ (by decide)

theorem sumMod_of_lt {values : List Word} (bound : sumNat values < 2^64) :
    sumMod values = sumNat values := Nat.mod_eq_of_lt bound

@[simp] theorem sumWord_toNat (values : List Word) :
    (sumWord values).toNat = sumMod values := rfl

@[simp] theorem sumWord_nil : sumWord [] = 0 := rfl

theorem sumWord_cons (value : Word) (rest : List Word) :
    sumWord (value :: rest) = value + sumWord rest := by
  apply BitVec.eq_of_toNat_eq
  simpa only [sumWord_toNat, BitVec.toNat_add] using sumMod_cons value rest

theorem sumWord_append (left right : List Word) :
    sumWord (left ++ right) = sumWord left + sumWord right := by
  apply BitVec.eq_of_toNat_eq
  simpa only [sumWord_toNat, BitVec.toNat_add] using sumMod_append left right

/-- A full-width addition can wrap without changing the final mathematical
sum modulo 2^64. This is a bitvector arithmetic lemma, not an execution premise. -/
theorem accumulator_suffix (acc value : Word) (rest : List Word) :
    ((acc + value).toNat + sumNat rest) % 2^64 =
      (acc.toNat + sumNat (value :: rest)) % 2^64 := by
  rw [BitVec.toNat_add, Nat.mod_add_mod, sumNat_cons, Nat.add_assoc]

/-- A word accumulator representing a prefix suffices for the independent
result after adding the remaining natural suffix, including wrapping sums. -/
theorem accumulator_append {acc : Word} (prior rest : List Word)
    (represents : acc.toNat = sumMod prior) :
    (acc.toNat + sumNat rest) % 2^64 = sumMod (prior ++ rest) := by
  rw [represents]
  simp only [sumMod, sumNat_append, Nat.mod_add_mod]

structure Input where
  values : List Word
  target : Word

/-- Current machine observations and ABI inputs only. Empty arrays impose no
data-read, allocation, alignment or canonicality condition on the unused base. -/
structure Pre (bytes : List Byte) (initial : State) (values : List Word) (target : Word) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  array : ArrayAt64 initial.memory (initial.registers .rdi) values
  bound : ArrayBound64 (initial.registers .rdi) values
  count : initial.registers .rsi = BitVec.ofNat 64 values.length
  stack : readWord initial.memory (initial.registers .rsp) = .ok target
  canonicalTarget : canonical target = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  canonicalStackAfter : canonical (initial.registers .rsp + 8) = true

def clobbers : List Register := [.rax,.rcx,.rdx,.rsp]

structure Post (initial : State) (values : List Word) (target : Word) (final : State) : Prop where
  value : (final.registers .rax).toNat = sumMod values
  memory : final.memory = initial.memory
  returnAddress : final.rip = target
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

def inputReads (base : Word) (values : List Word) : List Read :=
  (List.range values.length).map fun index => ⟨.data,base + BitVec.ofNat 64 (8 * index),8⟩

def operandReads (initial : State) (values : List Word) : List Read :=
  inputReads (initial.registers .rdi) values ++ [⟨.stack,initial.registers .rsp,8⟩]

def ReadAllowed (initial : State) (values : List Word) (read : Read) : Prop :=
  (read.kind = .data ∧ read.bytes = 8 ∧ ∃ index, index < values.length ∧
    read.address = initial.registers .rdi + BitVec.ofNat 64 (8 * index)) ∨
  (read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8)

def RawPolicy (initial : State) (values : List Word) : Prop :=
  Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
    (fun _ => ReadAllowed initial values)

end EDSL.ArraySum64
