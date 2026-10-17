/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ArrayMemory64
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Grading.Policy

set_option warningAsError true

namespace EDSL.ArrayMaximum64
open X86 X86.Sequential

/-- Mathematical maximum of natural interpretations, seeded independently of
machine registers or control flow. The empty input has result zero. -/
def maximumFrom (accumulator : Nat) : List Word → Nat
  | [] => accumulator
  | value :: rest => maximumFrom (max accumulator value.toNat) rest

def maximumNat (values : List Word) : Nat := maximumFrom 0 values

@[simp] theorem maximumFrom_nil (accumulator : Nat) : maximumFrom accumulator [] = accumulator := rfl
@[simp] theorem maximumNat_nil : maximumNat [] = 0 := rfl

/-- An order characterization independent of any compiler or instruction
selection. Every input must be below any upper bound on the result. -/
theorem maximumFrom_le_iff (accumulator bound : Nat) (values : List Word) :
    maximumFrom accumulator values ≤ bound ↔
      accumulator ≤ bound ∧ ∀ value ∈ values, value.toNat ≤ bound := by
  induction values generalizing accumulator with
  | nil => simp [maximumFrom]
  | cons value rest induction =>
    simp [maximumFrom,induction,Nat.max_le,and_assoc]

theorem maximumNat_le_iff (values : List Word) (bound : Nat) :
    maximumNat values ≤ bound ↔ ∀ value ∈ values, value.toNat ≤ bound := by
  simp [maximumNat,maximumFrom_le_iff]

theorem element_le_maximumNat {values : List Word} {value : Word}
    (member : value ∈ values) : value.toNat ≤ maximumNat values :=
  (maximumNat_le_iff values (maximumNat values)).mp (Nat.le_refl _) value member

theorem maximumNat_lt (values : List Word) : maximumNat values < 2^64 := by
  have upper : maximumNat values ≤ 2^64 - 1 :=
    (maximumNat_le_iff values _).mpr (by
      intro value _
      have bound := value.isLt
      omega)
  omega

/-- A reusable mathematical selection lemma for both comparison directions.
The independent result contract below is the natural maximum, not this helper. -/
def selectMaximum (left right : Word) : Word :=
  if left.toNat < right.toNat then right else left

theorem selectMaximum_toNat (left right : Word) :
    (selectMaximum left right).toNat = max left.toNat right.toNat := by
  unfold selectMaximum
  split
  · rename_i less
    simp only [Nat.max_eq_right (Nat.le_of_lt less)]
  · rename_i notLess
    simp only [Nat.max_eq_left (by omega : right.toNat ≤ left.toNat)]

theorem maximumFrom_step (accumulator value : Word) (rest : List Word) :
    maximumFrom (selectMaximum accumulator value).toNat rest =
      maximumFrom accumulator.toNat (value :: rest) := by
  rw [selectMaximum_toNat]
  rfl

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
  value : (final.registers .rax).toNat = maximumNat values
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

end EDSL.ArrayMaximum64
