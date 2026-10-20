/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory64

set_option warningAsError true

namespace EDSL.X86

/-- Every actual element is a complete little-endian eight-byte DATA load.
The empty array imposes no memory or pointer-readability condition. -/
def ArrayAt64 (memory : Memory) (base : Word) (values : List Word) : Prop :=
  ∀ index value, values[index]? = some value →
    loadQWord memory (base + BitVec.ofNat 64 (8 * index)) = .ok value

/-- The whole byte span does not wrap. An endpoint at 2^64 is permitted;
an empty array needs neither allocation, alignment, nor a canonical base. -/
def ArrayBound64 (base : Word) (values : List Word) : Prop :=
  base.toNat + 8 * values.length ≤ 2^64

@[simp] theorem ArrayAt64.nil (memory : Memory) (base : Word) :
    ArrayAt64 memory base [] := by
  intro index value present
  simp at present

theorem ArrayAt64.head {memory : Memory} {base value : Word} {values : List Word}
    (array : ArrayAt64 memory base (value :: values)) :
    loadQWord memory base = .ok value := by
  simpa using array 0 value rfl

theorem ArrayAt64.tail {memory : Memory} {base value : Word} {values : List Word}
    (array : ArrayAt64 memory base (value :: values)) :
    ArrayAt64 memory (base + 8) values := by
  intro index element present
  have atNext := array (index + 1) element (by simpa using present)
  simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add] at atNext
  change loadQWord memory (base + (BitVec.ofNat 64 (8 * index) + 8)) = .ok element at atNext
  rw [BitVec.add_comm (BitVec.ofNat 64 (8 * index)) 8, ← BitVec.add_assoc] at atNext
  exact atNext

theorem ArrayAt64.drop {memory : Memory} {base : Word} {values : List Word}
    (array : ArrayAt64 memory base values) (count : Nat) :
    ArrayAt64 memory (base + BitVec.ofNat 64 (8 * count)) (values.drop count) := by
  intro index value present
  have atNext := array (count + index) value (by simpa using present)
  simpa only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc] using atNext

@[simp] theorem ArrayBound64.nil (base : Word) : ArrayBound64 base [] := by
  have := base.isLt
  simp only [ArrayBound64, List.length_nil, Nat.mul_zero, Nat.add_zero]
  omega

theorem ArrayBound64.length_le {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) : values.length ≤ 2^61 := by
  unfold ArrayBound64 at bound
  omega

theorem ArrayBound64.length_lt {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) : values.length < 2^64 := by
  have := bound.length_le
  omega

/-- Every accessed element starts strictly below the address-space endpoint. -/
theorem ArrayBound64.element_address {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) {index : Nat} (inside : index < values.length) :
    (base + BitVec.ofNat 64 (8 * index)).toNat = base.toNat + 8 * index := by
  have limit : base.toNat + 8 * values.length ≤ 2^64 := bound
  have offset : 8 * index < 2^64 := by omega
  have sum : base.toNat + 8 * index < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt offset, Nat.mod_eq_of_lt sum]

/-- Nonwrapping includes the last byte of the last element. -/
theorem ArrayBound64.byte_address {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) {index offset : Nat}
    (inside : index < values.length) (byte : offset < 8) :
    ((base + BitVec.ofNat 64 (8 * index)) + BitVec.ofNat 64 offset).toNat =
      base.toNat + 8 * index + offset := by
  have limit : base.toNat + 8 * values.length ≤ 2^64 := bound
  have small : offset < 2^64 := by omega
  have sum : base.toNat + 8 * index + offset < 2^64 := by omega
  simp only [BitVec.toNat_add, bound.element_address inside, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]

theorem ArrayBound64.drop {base : Word} {values : List Word}
    (bound : ArrayBound64 base values) (count : Nat) :
    ArrayBound64 (base + BitVec.ofNat 64 (8 * count)) (values.drop count) := by
  by_cases inside : count < values.length
  · have address := bound.element_address inside
    have limit : base.toNat + 8 * values.length ≤ 2^64 := bound
    simp only [ArrayBound64, List.length_drop, address]
    omega
  · have empty : values.drop count = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [empty]
    exact ArrayBound64.nil _

theorem ArrayBound64.tail {base value : Word} {values : List Word}
    (bound : ArrayBound64 base (value :: values)) : ArrayBound64 (base + 8) values := by
  simpa using bound.drop 1

end EDSL.X86
