/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.BufferTask
import EDSL.Grading.FirstMatchConsumers

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.IndexSearch
open X86 X86.Sequential BufferCall Grading.IndexSearch

/-- A consumer law: inserting the key after a rejected prefix fixes the return
regardless of the suffix, including arbitrarily many later copies of the key. -/
theorem prefix_then_key {α : Type} [DecidableEq α] (front suffix : List α) (key : α)
    (absent : ∀ value ∈ front, value ≠ key) (actual : Word) :
    Result (front ++ key :: suffix) key actual ↔ actual = BitVec.ofNat 64 front.length := by
  have first : Grading.FirstMatch.Result (front ++ key :: suffix) (equals key) front.length :=
    Grading.FirstMatch.Consumers.prefix_then_match
      (by simpa only [equals, decide_eq_false_iff_not] using absent) (by simp [equals])
  have reference : Result (front ++ key :: suffix) key (BitVec.ofNat 64 front.length) := by
    refine ⟨front.length, first, ?_⟩
    simp [encode]
  constructor
  · intro result
    exact result.unique reference
  · rintro rfl
    exact reference

/-- Exercise fixed dispatch with unsigned high bytes and duplicate matches. -/
theorem byte_first_duplicate (actual : Word) :
    (Grading.BufferTask.registeredSpec .memchrIndex).result
      ⟨0x100000001, [0x80, 0xff, 0xef, 0xef, 0x41], 0xef⟩ actual ↔ actual = 2 := by
  exact prefix_then_key [0x80, 0xff] [0xef, 0x41] (0xef : Byte) (by simp) actual

/-- Equal low bytes do not make distinct 32-bit elements equal. -/
theorem word_first_duplicate (actual : Word) :
    (Grading.BufferTask.registeredSpec .linearSearchU32).result
      ⟨0x100000001, [0xef, 0x80000000, 0x800000ef, 0x800000ef], 0x800000ef⟩ actual ↔
      actual = 2 := by
  exact prefix_then_key [0xef, 0x80000000] [0x800000ef] (0x800000ef : BitVec 32)
    (by simp) actual

/-- Exhaustion returns all 64 one bits, rather than n or a zero-extended -1. -/
theorem absence_full64 (values : List Byte) (key : Byte)
    (absent : ∀ value ∈ values, value ≠ key) (actual : Word) :
    byteSpec.result ⟨0x8000000000000001, values, key⟩ actual ↔
      actual = 0xffffffffffffffff := by
  have reference : Result values key sizeMax := Result.of_absent absent
  constructor
  · intro result
    exact result.unique reference
  · rintro rfl
    exact reference

theorem sentinel_is_not_low32_minus_one : sizeMax ≠ (0x00000000ffffffff : Word) := by decide

/-- Raw wire bytes are defined by addresses, independently of u32Bytes and
storedDWordByte. The base is both unaligned and above the 32-bit address range. -/
def wireMemory : Memory where
  read address :=
    match address.toNat with
    | 0x100000001 => some 0xef
    | 0x100000002 => some 0xcd
    | 0x100000003 => some 0xab
    | 0x100000004 => some 0x89
    | 0x100000005 => some 0x78
    | 0x100000006 => some 0x56
    | 0x100000007 => some 0x34
    | 0x100000008 => some 0x12
    | 0x100000009 => some 0xaa
    | _ => none
  executable _ := false
  writable _ := false

theorem wire_snapshot :
    BufferAt wireMemory 0x100000001 (Elements.u32Bytes [0x89abcdef, 0x12345678]) := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  match offset with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp [Elements.u32Bytes, Elements.dwordBytes] at present
    subst byte
    rfl
  | offset + 8 => simp [Elements.u32Bytes, Elements.dwordBytes] at present

/-- Both words must decode from the independent wire bytes, with the high bit
retained. The same raw memory is used by the production load operation. -/
theorem unaligned_wire_loads :
    loadDWord wireMemory 0x100000001 = .ok 0x89abcdef ∧
      loadDWord wireMemory 0x100000005 = .ok 0x12345678 := by
  exact ⟨Elements.u32_loadDWord wire_snapshot (index := 0) rfl,
    Elements.u32_loadDWord wire_snapshot (index := 1) rfl⟩

/-- A readable byte after the buffer cannot authorize a partially contained
last operand. This quantifies over arbitrary extents and pointer values. -/
theorem last_word_fullspan {memory : Memory} {base : Word} {values : List (BitVec 32)}
    (snapshot : BufferAt memory base (Elements.u32Bytes values)) (nonempty : values ≠ []) :
    (Buffer.mk base (Elements.u32Bytes values)).Contains
        (base + BitVec.ofNat 64 (4 * (values.length - 1))) 4 ∧
      ¬(Buffer.mk base (Elements.u32Bytes values)).Contains
        (base + BitVec.ofNat 64 (4 * (values.length - 1))) 5 := by
  have positive : 0 < values.length := by
    cases values with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail => simp
  have inside : values.length - 1 < values.length := by omega
  refine ⟨Elements.u32_element_span snapshot inside, ?_⟩
  have offsetInside : 4 * (values.length - 1) < (Elements.u32Bytes values).length := by
    rw [Elements.u32Bytes_length]
    omega
  have address : (base + BitVec.ofNat 64 (4 * (values.length - 1))).toNat =
      base.toNat + 4 * (values.length - 1) :=
    Buffer.offset_address (buffer := ⟨base, Elements.u32Bytes values⟩) snapshot offsetInside
  rintro ⟨_, _, upper⟩
  change (base + BitVec.ofNat 64 (4 * (values.length - 1))).toNat + 5 ≤
    base.toNat + (Elements.u32Bytes values).length at upper
  rw [address, Elements.u32Bytes_length] at upper
  omega

theorem readable_neighbor_is_not_buffer :
    readDataByte wireMemory 0x100000009 = .ok 0xaa ∧
      ¬(Buffer.mk 0x100000001 (Elements.u32Bytes [0x89abcdef, 0x12345678])).Contains
        0x100000006 4 := by
  exact ⟨rfl, by unfold Buffer.Contains; decide⟩

/-- The last component byte participates in the typed snapshot. Changing it
invalidates that snapshot even if all other bytes remain accessible. -/
theorem changed_last_byte_invalidates {memory : Memory} {base : Word}
    {values : List (BitVec 32)} {index : Nat} {value : BitVec 32}
    (present : values[index]? = some value)
    (changed : readDataByte memory (base + BitVec.ofNat 64 (4 * index + 3)) ≠
      .ok (value.extractLsb' 24 8)) : ¬BufferAt memory base (Elements.u32Bytes values) := by
  intro snapshot
  exact changed (snapshot.2 (4 * index + 3) (value.extractLsb' 24 8)
    (Elements.u32Bytes_element present ⟨3, by decide⟩))

/-- Neither empty bytes nor empty words confer any data span, for every pointer
and width. This includes noncanonical/unaligned/unmapped pointers and width 0. -/
theorem empty_never_authorizes_data (base : Word) (byteKey : Byte) (wordKey : BitVec 32)
    (read : Read) :
    ¬DataRead (byteSpec.buffers ⟨base, [], byteKey⟩) read ∧
      ¬DataRead (u32Spec.buffers ⟨base, [], wordKey⟩) read := by
  constructor
  · apply DataRead.no_empty
    intro buffer member
    have same : buffer = byteBuffer ⟨base, [], byteKey⟩ := by simpa [byteSpec] using member
    subst buffer
    rfl
  · apply DataRead.no_empty
    intro buffer member
    have same : buffer = u32Buffer ⟨base, [], wordKey⟩ := by simpa [u32Spec] using member
    subst buffer
    rfl

def argumentState (base count key : Word) : State where
  registers register :=
    match register with
    | .rdi => base
    | .rsi => count
    | .rdx => key
    | _ => 0
  rip := 0
  flags := 0
  memory := wireMemory

/-- The registered argument contracts accept dirty upper RDX bits for both
element widths while retaining the full high address bits in RDI. -/
theorem key_upper_bits_unrestricted :
    Bound (Grading.BufferTask.registeredSpec .memchrIndex)
        ⟨0x100000001, [0xef], 0xef⟩ (argumentState 0x100000001 1 0xa55a1234567800ef) ∧
      Bound (Grading.BufferTask.registeredSpec .linearSearchU32)
        ⟨0x100000001, [0x89abcdef], 0x89abcdef⟩
        (argumentState 0x100000001 1 0xa55a123489abcdef) := by
  constructor
  · intro index argument registered
    match index with
    | ⟨0, _⟩ | ⟨1, _⟩ =>
      simp [Grading.BufferTask.registeredSpec, byteSpec] at registered
      subst argument
      rfl
    | ⟨2, _⟩ =>
      simp [Grading.BufferTask.registeredSpec, byteSpec] at registered
      subst argument
      change (0xa55a1234567800ef : Word).setWidth 8 = (0xef : Byte)
      decide
    | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
      simp [Grading.BufferTask.registeredSpec, byteSpec] at registered
  · intro index argument registered
    match index with
    | ⟨0, _⟩ | ⟨1, _⟩ =>
      simp [Grading.BufferTask.registeredSpec, u32Spec] at registered
      subst argument
      rfl
    | ⟨2, _⟩ =>
      simp [Grading.BufferTask.registeredSpec, u32Spec] at registered
      subst argument
      change (0xa55a123489abcdef : Word).setWidth 32 = (0x89abcdef : BitVec 32)
      decide
    | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
      simp [Grading.BufferTask.registeredSpec, u32Spec] at registered

/-- Truncating either pointer or length would incorrectly admit these calls. -/
theorem full64_base_and_count :
    ¬Bound byteSpec ⟨0x100000001, [0xef], 0xef⟩ (argumentState 1 1 0xef) ∧
      ¬Bound u32Spec ⟨0x100000001, [0x89abcdef], 0x89abcdef⟩
        (argumentState 0x100000001 0x100000001 0x89abcdef) := by
  constructor
  · intro bound
    have wrong := bound ⟨0, by decide⟩ (.word64 0x100000001) rfl
    have different : ¬Argument.Holds (.word64 0x100000001) 1 := by
      change (1 : Word) ≠ 0x100000001
      decide
    exact different wrong
  · intro bound
    have wrong := bound ⟨1, by decide⟩ (.word64 1) rfl
    have different : ¬Argument.Holds (.word64 1) 0x100000001 := by
      change (0x100000001 : Word) ≠ 1
      decide
    exact different wrong

end EDSL.Tests.IndexSearch
