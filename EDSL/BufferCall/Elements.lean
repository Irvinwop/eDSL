/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.BufferCall.Resources
import EDSL.X86.ArrayMemory

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.BufferCall.Elements
open X86 X86.Sequential

/-- The four actual little-endian bytes of one unsigned 32-bit element. -/
def dwordBytes (value : BitVec 32) : List Byte :=
  [value.extractLsb' 0 8, value.extractLsb' 8 8,
    value.extractLsb' 16 8, value.extractLsb' 24 8]

/-- One complete byte snapshot, with no per-element loans or alignment test. -/
def u32Bytes (values : List (BitVec 32)) : List Byte := values.flatMap dwordBytes

@[simp] theorem u32Bytes_nil : u32Bytes [] = [] := rfl

@[simp] theorem u32Bytes_cons (value : BitVec 32) (values : List (BitVec 32)) :
    u32Bytes (value :: values) =
      value.extractLsb' 0 8 :: value.extractLsb' 8 8 ::
        value.extractLsb' 16 8 :: value.extractLsb' 24 8 :: u32Bytes values := rfl

@[simp] theorem u32Bytes_length (values : List (BitVec 32)) :
    (u32Bytes values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [u32Bytes_cons, List.length_cons, ih]; omega

theorem u32Bytes_nonempty {values : List (BitVec 32)} :
    u32Bytes values ≠ [] ↔ values ≠ [] := by
  cases values <;> simp

/-- Every component byte comes from the corresponding typed element. -/
theorem u32Bytes_element {values : List (BitVec 32)} {index : Nat} {value : BitVec 32}
    (present : values[index]? = some value) (offset : Fin 4) :
    (u32Bytes values)[4 * index + offset.val]? =
      some (value.extractLsb' (8 * offset.val) 8) := by
  induction values generalizing index with
  | nil => simp at present
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at present
      subst head
      match offset with
      | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
    | succ index =>
      have next := ih (by simpa using present)
      rw [u32Bytes_cons,
        show 4 * (index + 1) + offset.val = 4 * index + offset.val + 1 + 1 + 1 + 1 by omega]
      exact next

/-- Any positive, fully contained span has its exact natural address, even
at the end of the full 64-bit extent. No neighboring readable RAM is used. -/
theorem span_of_bufferAt {memory : Memory} {base : Word} {bytes : List Byte}
    (snapshot : BufferAt memory base bytes) {offset width : Nat}
    (positive : 0 < width) (inside : offset + width ≤ bytes.length) :
    (Buffer.mk base bytes).Contains (base + BitVec.ofNat 64 offset) width := by
  have inRange : offset < bytes.length := by omega
  have address : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset :=
    Buffer.offset_address (buffer := ⟨base, bytes⟩) snapshot inRange
  change 0 < width ∧ base.toNat ≤ (base + BitVec.ofNat 64 offset).toNat ∧
    (base + BitVec.ofNat 64 offset).toNat + width ≤ base.toNat + bytes.length
  rw [address]
  exact ⟨positive, by omega, by omega⟩

/-- Four observed bytes in an arbitrary byte list imply a successful actual
unaligned dword load. There is no future-read or decoder premise. -/
theorem loadDWord_of_bufferAt {memory : Memory} {base : Word} {bytes : List Byte}
    (snapshot : BufferAt memory base bytes) {offset : Nat} {b0 b1 b2 b3 : Byte}
    (at0 : bytes[offset]? = some b0) (at1 : bytes[offset + 1]? = some b1)
    (at2 : bytes[offset + 2]? = some b2) (at3 : bytes[offset + 3]? = some b3) :
    loadDWord memory (base + BitVec.ofNat 64 offset) = .ok (joinDWord b0 b1 b2 b3) := by
  have inside := (List.getElem_of_getElem? at3).1
  have span := span_of_bufferAt snapshot (offset := offset) (width := 4) (by decide) (by omega)
  have nowrap : ¬(base + BitVec.ofNat 64 offset).toNat + 3 ≥ 2^64 := by
    have bound := snapshot.1
    have upper := span.2.2
    change (base + BitVec.ofNat 64 offset).toNat + 4 ≤ base.toNat + bytes.length at upper
    omega
  have read0 := snapshot.2 offset b0 at0
  have read1 := snapshot.2 (offset + 1) b1 at1
  have read2 := snapshot.2 (offset + 2) b2 at2
  have read3 := snapshot.2 (offset + 3) b3 at3
  simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at read1 read2 read3
  simp only [loadDWord, ite_eq_right nowrap, BitVec.ofNat_eq_ofNat,
    read0, read1, read2, read3, ok_bind, pure_ok]

/-- The entire four-byte operand is authorized by the single full snapshot. -/
theorem u32_element_span {memory : Memory} {base : Word} {values : List (BitVec 32)}
    (snapshot : BufferAt memory base (u32Bytes values)) {index : Nat}
    (inside : index < values.length) :
    (Buffer.mk base (u32Bytes values)).Contains (base + BitVec.ofNat 64 (4 * index)) 4 := by
  apply span_of_bufferAt snapshot (by decide)
  rw [u32Bytes_length]
  omega

theorem byte_element_span {memory : Memory} {base : Word} {values : List Byte}
    (snapshot : BufferAt memory base values) {index : Nat} (inside : index < values.length) :
    (Buffer.mk base values).Contains (base + BitVec.ofNat 64 index) 1 :=
  span_of_bufferAt snapshot (by decide) (by omega)

/-- The byte snapshot determines the actual raw-memory value of every word. -/
theorem u32_loadDWord {memory : Memory} {base : Word} {values : List (BitVec 32)}
    (snapshot : BufferAt memory base (u32Bytes values)) {index : Nat} {value : BitVec 32}
    (present : values[index]? = some value) :
    loadDWord memory (base + BitVec.ofNat 64 (4 * index)) = .ok value := by
  have loaded := loadDWord_of_bufferAt snapshot
    (u32Bytes_element present ⟨0, by decide⟩) (u32Bytes_element present ⟨1, by decide⟩)
    (u32Bytes_element present ⟨2, by decide⟩) (u32Bytes_element present ⟨3, by decide⟩)
  change loadDWord memory (base + BitVec.ofNat 64 (4 * index)) =
    .ok (joinDWord (value.extractLsb' 0 8) (value.extractLsb' 8 8)
      (value.extractLsb' 16 8) (value.extractLsb' 24 8)) at loaded
  rw [join_extracts] at loaded
  exact loaded

theorem u32_arrayAt {memory : Memory} {base : Word} {values : List (BitVec 32)}
    (snapshot : BufferAt memory base (u32Bytes values)) : ArrayAt memory base values := by
  intro index value present
  exact u32_loadDWord snapshot present

theorem u32_arrayBound {memory : Memory} {base : Word} {values : List (BitVec 32)}
    (snapshot : BufferAt memory base (u32Bytes values)) : ArrayBound base values := by
  change base.toNat + 4 * values.length ≤ 2^64
  simpa only [u32Bytes_length] using snapshot.1

end EDSL.BufferCall.Elements
