/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State

namespace EDSL.X86

def dwordAddressable (address : Word) : Bool :=
  decide (address.toNat + 3 < 2^64) &&
    (canonical address && canonical (address + 1) &&
      canonical (address + 2) && canonical (address + 3))

def readDataByte (memory : Memory) (address : Word) : Except Error Byte :=
  if canonical address then
    match memory.read address with
    | some byte => .ok byte
    | none => .error (.inaccessibleData address)
  else .error (.inaccessibleData address)

def joinDWord (b0 b1 b2 b3 : Byte) : BitVec 32 :=
  b0.setWidth 32 ||| (b1.setWidth 32 <<< 8) |||
    (b2.setWidth 32 <<< 16) ||| (b3.setWidth 32 <<< 24)

def loadDWord (memory : Memory) (address : Word) : Except Error (BitVec 32) := do
  if address.toNat + 3 ≥ 2^64 then throw (.inaccessibleData address)
  let b0 ← readDataByte memory address
  let b1 ← readDataByte memory (address + 1)
  let b2 ← readDataByte memory (address + 2)
  let b3 ← readDataByte memory (address + 3)
  return joinDWord b0 b1 b2 b3

def dwordWritable (memory : Memory) (address : Word) : Bool :=
  (memory.writable address && memory.writable (address + 1) &&
    memory.writable (address + 2) && memory.writable (address + 3)) &&
  ((memory.read address).isSome && (memory.read (address + 1)).isSome &&
    (memory.read (address + 2)).isSome && (memory.read (address + 3)).isSome)

def canStoreDWord (memory : Memory) (address : Word) : Bool :=
  dwordAddressable address && dwordWritable memory address

def storedDWordByte (memory : Memory) (address : Word) (value : BitVec 32)
    (query : Word) : Option Byte :=
  match (query - address).toNat with
  | 0 => some (value.extractLsb' 0 8)
  | 1 => some (value.extractLsb' 8 8)
  | 2 => some (value.extractLsb' 16 8)
  | 3 => some (value.extractLsb' 24 8)
  | _ => memory.read query

/-- Functional byte update only; this does not assert concurrent visibility or atomicity. -/
def writeDWordUnchecked (memory : Memory) (address : Word) (value : BitVec 32) : Memory :=
  { memory with read := storedDWordByte memory address value }

/-- Validate all four bytes before creating an updated memory state. -/
def storeDWord (memory : Memory) (address : Word) (value : BitVec 32) : Except Error Memory :=
  if canStoreDWord memory address then .ok (writeDWordUnchecked memory address value)
  else .error (.writeDenied address)

@[simp] theorem offset_cancel (address offset : Word) : address + offset - address = offset := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem join_extracts (value : BitVec 32) :
    joinDWord (value.extractLsb' 0 8) (value.extractLsb' 8 8)
      (value.extractLsb' 16 8) (value.extractLsb' 24 8) = value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i bound
  by_cases h0 : i < 8
  · simp [joinDWord, h0, show i < 16 by omega, show i < 24 by omega, bound]
  · by_cases h1 : i < 16
    · simp [joinDWord, h0, h1, show i < 24 by omega, bound,
        show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
    · by_cases h2 : i < 24
      · simp [joinDWord, h0, h1, h2, bound,
          show ¬ i - 8 < 8 by omega, show i - 16 < 8 by omega,
          show 16 + (i - 16) = i by omega]
      · simp [joinDWord, h0, h1, h2, bound,
          show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
          show i - 24 < 8 by omega, show 24 + (i - 24) = i by omega]

/-- Outside the four-byte footprint, a write leaves bytes unchanged. -/
theorem writeDWord_frame (memory : Memory) (address query : Word) (value : BitVec 32)
    (outside : 4 ≤ (query - address).toNat) :
    (writeDWordUnchecked memory address value).read query = memory.read query := by
  simp only [writeDWordUnchecked, storedDWordByte]
  split <;> first | omega | rfl

theorem writeDWord_preserves_permissions (memory : Memory) (address : Word) (value : BitVec 32) :
    (writeDWordUnchecked memory address value).executable = memory.executable ∧
    (writeDWordUnchecked memory address value).writable = memory.writable := by
  exact ⟨rfl, rfl⟩

theorem load_after_write (memory : Memory) (address : Word) (value : BitVec 32)
    (valid : dwordAddressable address = true) :
    loadDWord (writeDWordUnchecked memory address value) address = .ok value := by
  simp only [dwordAddressable, Bool.and_eq_true, decide_eq_true_eq] at valid
  rcases valid with ⟨bound, ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩⟩
  simp only [BitVec.ofNat_eq_ofNat] at c0 c1 c2 c3
  have noWrap : ¬ address.toNat + 3 ≥ 2^64 := by omega
  simp [loadDWord, noWrap, readDataByte, c0, c1, c2, c3,
    writeDWordUnchecked, storedDWordByte]
  exact join_extracts value

theorem store_sound (memory : Memory) (address : Word) (value : BitVec 32)
    (allowed : canStoreDWord memory address = true) :
    storeDWord memory address value = .ok (writeDWordUnchecked memory address value) ∧
    loadDWord (writeDWordUnchecked memory address value) address = .ok value := by
  have valid := (Bool.and_eq_true_iff.mp allowed).1
  exact ⟨by simp [storeDWord, allowed], load_after_write memory address value valid⟩

def DWordDisjoint (address base : Word) (length : Nat) : Prop :=
  ∀ offset, offset < length → 4 ≤ ((base + BitVec.ofNat 64 offset) - address).toNat

def MemoryAgreesOn (left right : Memory) (base : Word) (length : Nat) : Prop :=
  ∀ offset, offset < length →
    left.read (base + BitVec.ofNat 64 offset) = right.read (base + BitVec.ofNat 64 offset)

theorem writeDWord_agrees (memory : Memory) (address base : Word) (value : BitVec 32)
    (length : Nat) (disjoint : DWordDisjoint address base length) :
    MemoryAgreesOn (writeDWordUnchecked memory address value) memory base length := by
  intro offset bound
  exact writeDWord_frame memory address (base + BitVec.ofNat 64 offset) value (disjoint offset bound)

theorem loadDWord_congr (left right : Memory) (address : Word)
    (same : MemoryAgreesOn left right address 4) :
    loadDWord left address = loadDWord right address := by
  have b0 := same 0 (by decide)
  have b1 := same 1 (by decide)
  have b2 := same 2 (by decide)
  have b3 := same 3 (by decide)
  simp only [BitVec.add_zero] at b0
  unfold loadDWord readDataByte
  simp only [BitVec.ofNat_eq_ofNat]
  rw [b0, b1, b2, b3]

theorem readWord_congr (left right : Memory) (address : Word)
    (same : MemoryAgreesOn left right address 8) :
    readWord left address = readWord right address := by
  have b0 := same 0 (by decide)
  have b1 := same 1 (by decide)
  have b2 := same 2 (by decide)
  have b3 := same 3 (by decide)
  have b4 := same 4 (by decide)
  have b5 := same 5 (by decide)
  have b6 := same 6 (by decide)
  have b7 := same 7 (by decide)
  simp only [BitVec.add_zero] at b0
  unfold readWord readStackByte
  simp only [BitVec.ofNat_eq_ofNat]
  rw [b0, b1, b2, b3, b4, b5, b6, b7]

theorem writeDWord_preserves_code (memory : Memory) (address base : Word)
    (value : BitVec 32) (bytes : List Byte)
    (code : CodeAt memory base bytes) (disjoint : DWordDisjoint address base bytes.length) :
    CodeAt (writeDWordUnchecked memory address value) base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have unchanged := writeDWord_frame memory address (base + BitVec.ofNat 64 offset) value
    (disjoint offset bound)
  have sameFetch : fetchByte (writeDWordUnchecked memory address value)
      (base + BitVec.ofNat 64 offset) = fetchByte memory (base + BitVec.ofNat 64 offset) := by
    unfold fetchByte
    rw [unchanged]
    rfl
  exact sameFetch.trans (code.2 offset byte atOffset)

end EDSL.X86
