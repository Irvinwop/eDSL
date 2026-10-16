/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.X86

/-- An independent mathematical modular sum of the input values. -/
def sum32 (values : List (BitVec 32)) : BitVec 32 :=
  BitVec.ofNat 32 (values.map BitVec.toNat).sum

/-- Each actual input element is read from its four little-endian bytes.
An empty array imposes no input-memory or pointer-readability condition. -/
def ArrayAt (memory : Memory) (base : Word) (values : List (BitVec 32)) : Prop :=
  ∀ index value, values[index]? = some value →
    loadDWord memory (base + BitVec.ofNat 64 (4 * index)) = .ok value

/-- The entire input footprint does not wrap. This remains vacuous for an
empty input, including a noncanonical unused base pointer. -/
def ArrayBound (base : Word) (values : List (BitVec 32)) : Prop :=
  base.toNat + 4 * values.length ≤ 2^64

@[simp] theorem sum32_nil : sum32 [] = 0 := rfl

theorem sum32_cons (value : BitVec 32) (values : List (BitVec 32)) :
    sum32 (value :: values) = value + sum32 values := by
  simp [sum32, BitVec.ofNat_add]

theorem sum32_append (left right : List (BitVec 32)) :
    sum32 (left ++ right) = sum32 left + sum32 right := by
  simp [sum32, List.sum_append, BitVec.ofNat_add]

theorem ArrayAt.nil (memory : Memory) (base : Word) : ArrayAt memory base [] := by
  intro index value present
  simp at present

theorem ArrayAt.head {memory : Memory} {base : Word} {value : BitVec 32}
    {values : List (BitVec 32)} (array : ArrayAt memory base (value :: values)) :
    loadDWord memory base = .ok value := by
  simpa using array 0 value rfl

theorem ArrayAt.tail {memory : Memory} {base : Word} {value : BitVec 32}
    {values : List (BitVec 32)} (array : ArrayAt memory base (value :: values)) :
    ArrayAt memory (base + 4) values := by
  intro index element present
  have atNext := array (index + 1) element (by simpa using present)
  simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add] at atNext
  change loadDWord memory (base + (BitVec.ofNat 64 (4 * index) + 4)) = .ok element at atNext
  rw [BitVec.add_comm (BitVec.ofNat 64 (4 * index)) 4, ← BitVec.add_assoc] at atNext
  exact atNext

theorem ArrayAt.drop {memory : Memory} {base : Word} {values : List (BitVec 32)}
    (array : ArrayAt memory base values) (count : Nat) :
    ArrayAt memory (base + BitVec.ofNat 64 (4 * count)) (values.drop count) := by
  intro index value present
  have atNext := array (count + index) value (by simpa using present)
  simpa only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc] using atNext

theorem ArrayBound.length_lt {base : Word} {values : List (BitVec 32)}
    (bound : ArrayBound base values) : values.length < 2^64 := by
  unfold ArrayBound at bound
  omega

end EDSL.X86
