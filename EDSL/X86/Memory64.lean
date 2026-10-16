/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.X86

/-- Ordinary eight-byte operands may be unaligned, but may neither wrap nor
cross the four-level canonical-address hole. -/
def qwordAddressable (address : Word) : Bool :=
  decide (address.toNat + 7 < 2^64) &&
    (canonical address && canonical (address + 1) &&
      canonical (address + 2) && canonical (address + 3) &&
      canonical (address + 4) && canonical (address + 5) &&
      canonical (address + 6) && canonical (address + 7))

def joinQWord (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) : Word :=
  b0.setWidth 64 ||| (b1.setWidth 64 <<< 8) |||
    (b2.setWidth 64 <<< 16) ||| (b3.setWidth 64 <<< 24) |||
    (b4.setWidth 64 <<< 32) ||| (b5.setWidth 64 <<< 40) |||
    (b6.setWidth 64 <<< 48) ||| (b7.setWidth 64 <<< 56)

/-- Little-endian DATA read; RET's distinct stack-fault primitive is unchanged. -/
def loadQWord (memory : Memory) (address : Word) : Except Error Word := do
  if address.toNat + 7 ≥ 2^64 then throw (.inaccessibleData address)
  let b0 ← readDataByte memory address
  let b1 ← readDataByte memory (address + 1)
  let b2 ← readDataByte memory (address + 2)
  let b3 ← readDataByte memory (address + 3)
  let b4 ← readDataByte memory (address + 4)
  let b5 ← readDataByte memory (address + 5)
  let b6 ← readDataByte memory (address + 6)
  let b7 ← readDataByte memory (address + 7)
  return joinQWord b0 b1 b2 b3 b4 b5 b6 b7

/-- Every byte must already be mapped/readable and writable. -/
def qwordWritable (memory : Memory) (address : Word) : Bool :=
  (memory.writable address && memory.writable (address + 1) &&
    memory.writable (address + 2) && memory.writable (address + 3) &&
    memory.writable (address + 4) && memory.writable (address + 5) &&
    memory.writable (address + 6) && memory.writable (address + 7)) &&
  ((memory.read address).isSome && (memory.read (address + 1)).isSome &&
    (memory.read (address + 2)).isSome && (memory.read (address + 3)).isSome &&
    (memory.read (address + 4)).isSome && (memory.read (address + 5)).isSome &&
    (memory.read (address + 6)).isSome && (memory.read (address + 7)).isSome)

def canStoreQWord (memory : Memory) (address : Word) : Bool :=
  qwordAddressable address && qwordWritable memory address

def storedQWordByte (memory : Memory) (address value : Word) (query : Word) : Option Byte :=
  match (query - address).toNat with
  | 0 => some (value.extractLsb' 0 8)
  | 1 => some (value.extractLsb' 8 8)
  | 2 => some (value.extractLsb' 16 8)
  | 3 => some (value.extractLsb' 24 8)
  | 4 => some (value.extractLsb' 32 8)
  | 5 => some (value.extractLsb' 40 8)
  | 6 => some (value.extractLsb' 48 8)
  | 7 => some (value.extractLsb' 56 8)
  | _ => memory.read query

/-- Functional byte update only; no concurrent visibility or atomicity claim. -/
def writeQWordUnchecked (memory : Memory) (address value : Word) : Memory :=
  { memory with read := storedQWordByte memory address value }

/-- Preflight the complete eight-byte operand before returning updated memory. -/
def storeQWord (memory : Memory) (address value : Word) : Except Error Memory :=
  if canStoreQWord memory address then .ok (writeQWordUnchecked memory address value)
  else .error (.writeDenied address)

theorem qword_join_extracts (value : Word) :
    joinQWord (value.extractLsb' 0 8) (value.extractLsb' 8 8)
      (value.extractLsb' 16 8) (value.extractLsb' 24 8)
      (value.extractLsb' 32 8) (value.extractLsb' 40 8)
      (value.extractLsb' 48 8) (value.extractLsb' 56 8) = value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i bound
  by_cases h0 : i < 8
  · simp (disch := omega) [joinQWord, show i < 8 by omega, show i < 16 by omega, show i < 24 by omega, show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  · by_cases h1 : i < 16
    · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show i < 16 by omega, show i < 24 by omega, show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
    · by_cases h2 : i < 24
      · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show i < 24 by omega, show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
      · by_cases h3 : i < 32
        · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
        · by_cases h4 : i < 40
          · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
          · by_cases h5 : i < 48
            · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega, show ¬ i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
            · by_cases h6 : i < 56
              · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega, show ¬ i < 40 by omega, show ¬ i < 48 by omega, show i < 56 by omega]
              · simp (disch := omega) [joinQWord, show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega, show ¬ i < 40 by omega, show ¬ i < 48 by omega, show ¬ i < 56 by omega]

/-- Outside the modular eight-byte footprint, all bytes are unchanged. -/
theorem writeQWord_frame (memory : Memory) (address query value : Word)
    (outside : 8 ≤ (query - address).toNat) :
    (writeQWordUnchecked memory address value).read query = memory.read query := by
  simp only [writeQWordUnchecked, storedQWordByte]
  split <;> first | omega | rfl

theorem writeQWord_preserves_permissions (memory : Memory) (address value : Word) :
    (writeQWordUnchecked memory address value).executable = memory.executable ∧
    (writeQWordUnchecked memory address value).writable = memory.writable := by
  exact ⟨rfl, rfl⟩

theorem qword_load_after_write (memory : Memory) (address value : Word)
    (valid : qwordAddressable address = true) :
    loadQWord (writeQWordUnchecked memory address value) address = .ok value := by
  simp only [qwordAddressable, Bool.and_eq_true, decide_eq_true_eq] at valid
  rcases valid with ⟨bound, ⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩⟩
  simp only [BitVec.ofNat_eq_ofNat] at c0 c1 c2 c3 c4 c5 c6 c7
  have noWrap : ¬ address.toNat + 7 ≥ 2^64 := by omega
  simp [loadQWord, noWrap, readDataByte, c0, c1, c2, c3, c4, c5, c6, c7,
    writeQWordUnchecked, storedQWordByte, qword_join_extracts]

theorem qword_store_sound (memory : Memory) (address value : Word)
    (allowed : canStoreQWord memory address = true) :
    storeQWord memory address value = .ok (writeQWordUnchecked memory address value) ∧
    loadQWord (writeQWordUnchecked memory address value) address = .ok value := by
  exact ⟨by simp [storeQWord, allowed],
    qword_load_after_write memory address value (Bool.and_eq_true_iff.mp allowed).1⟩

/-- Successful validation entails an actual complete DATA read, independently
of the replacement value used by a later store. -/
theorem loadQWord_of_canStoreQWord (memory : Memory) (address : Word)
    (allowed : canStoreQWord memory address = true) :
    ∃ value, loadQWord memory address = .ok value := by
  simp only [canStoreQWord, qwordAddressable, qwordWritable, Bool.and_eq_true,
    decide_eq_true_eq] at allowed
  rcases allowed with ⟨⟨bound, canon⟩, writable, readable⟩
  rcases canon with ⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩
  rcases readable with ⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩
  obtain ⟨b0, h0⟩ := Option.isSome_iff_exists.mp r0
  obtain ⟨b1, h1⟩ := Option.isSome_iff_exists.mp r1
  obtain ⟨b2, h2⟩ := Option.isSome_iff_exists.mp r2
  obtain ⟨b3, h3⟩ := Option.isSome_iff_exists.mp r3
  obtain ⟨b4, h4⟩ := Option.isSome_iff_exists.mp r4
  obtain ⟨b5, h5⟩ := Option.isSome_iff_exists.mp r5
  obtain ⟨b6, h6⟩ := Option.isSome_iff_exists.mp r6
  obtain ⟨b7, h7⟩ := Option.isSome_iff_exists.mp r7
  simp only [BitVec.ofNat_eq_ofNat] at c0 c1 c2 c3 c4 c5 c6 c7 h0 h1 h2 h3 h4 h5 h6 h7
  refine ⟨joinQWord b0 b1 b2 b3 b4 b5 b6 b7, ?_⟩
  have noWrap : ¬ address.toNat + 7 ≥ 2^64 := by omega
  simp [loadQWord, noWrap, readDataByte, c0, c1, c2, c3, c4, c5, c6, c7,
    h0, h1, h2, h3, h4, h5, h6, h7]

def QWordDisjoint (address base : Word) (length : Nat) : Prop :=
  ∀ offset, offset < length → 8 ≤ ((base + BitVec.ofNat 64 offset) - address).toNat

theorem writeQWord_agrees (memory : Memory) (address base value : Word)
    (length : Nat) (disjoint : QWordDisjoint address base length) :
    MemoryAgreesOn (writeQWordUnchecked memory address value) memory base length := by
  intro offset bound
  exact writeQWord_frame memory address (base + BitVec.ofNat 64 offset) value (disjoint offset bound)

theorem loadQWord_congr (left right : Memory) (address : Word)
    (same : MemoryAgreesOn left right address 8) :
    loadQWord left address = loadQWord right address := by
  have b0 := same 0 (by decide)
  have b1 := same 1 (by decide)
  have b2 := same 2 (by decide)
  have b3 := same 3 (by decide)
  have b4 := same 4 (by decide)
  have b5 := same 5 (by decide)
  have b6 := same 6 (by decide)
  have b7 := same 7 (by decide)
  simp only [BitVec.add_zero] at b0
  unfold loadQWord readDataByte
  simp only [BitVec.ofNat_eq_ofNat]
  rw [b0, b1, b2, b3, b4, b5, b6, b7]

theorem writeQWord_preserves_code (memory : Memory) (address base value : Word) (bytes : List Byte)
    (code : CodeAt memory base bytes) (disjoint : QWordDisjoint address base bytes.length) :
    CodeAt (writeQWordUnchecked memory address value) base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have unchanged := writeQWord_frame memory address (base + BitVec.ofNat 64 offset) value
    (disjoint offset bound)
  have sameFetch : fetchByte (writeQWordUnchecked memory address value)
      (base + BitVec.ofNat 64 offset) = fetchByte memory (base + BitVec.ofNat 64 offset) := by
    unfold fetchByte
    rw [unchanged]
    rfl
  exact sameFetch.trans (code.2 offset byte atOffset)

end EDSL.X86
