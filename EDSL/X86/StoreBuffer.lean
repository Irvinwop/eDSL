/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.X86.StoreBuffer

/-- A pending ordinary four-byte write. Buffers are ordered oldest first. -/
structure Store where
  address : Word
  value : BitVec 32
  deriving DecidableEq, Repr

abbrev Buffer := List Store

/-- The issuing thread observes global RAM overlaid by its pending writes.
Newer overlapping bytes win; this definition does not publish any write. -/
def view (memory : Memory) (buffer : Buffer) : Memory :=
  buffer.foldl (fun current store => writeDWordUnchecked current store.address store.value) memory

def enqueue (buffer : Buffer) (store : Store) : Buffer := buffer ++ [store]

/-- The byte supplied by one pending write, absent outside its four-byte footprint. -/
def Store.byte (store : Store) (query : Word) : Option Byte :=
  match (query - store.address).toNat with
  | 0 => some (store.value.extractLsb' 0 8)
  | 1 => some (store.value.extractLsb' 8 8)
  | 2 => some (store.value.extractLsb' 16 8)
  | 3 => some (store.value.extractLsb' 24 8)
  | _ => none

/-- Search from newest to oldest, independently for each addressed byte. -/
def forward : Buffer → Word → Option Byte
  | [], _ => none
  | head :: tail, query => (forward tail query).or (head.byte query)

theorem write_byte (memory : Memory) (store : Store) (query : Word) :
    (writeDWordUnchecked memory store.address store.value).read query =
      (store.byte query).or (memory.read query) := by
  simp only [writeDWordUnchecked, storedDWordByte, Store.byte]
  split <;> simp_all

/-- Each byte comes from the newest matching own store, or from global memory. -/
theorem view_read (memory : Memory) (buffer : Buffer) (query : Word) :
    (view memory buffer).read query = (forward buffer query).or (memory.read query) := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    change (view (writeDWordUnchecked memory head.address head.value) tail).read query = _
    rw [ih, write_byte]
    exact (Option.or_assoc).symm

theorem view_read_congr (left right : Memory) (buffer : Buffer) (query : Word)
    (same : left.read query = right.read query) :
    (view left buffer).read query = (view right buffer).read query := by
  rw [view_read, view_read, same]

@[simp] theorem view_nil (memory : Memory) : view memory [] = memory := rfl

@[simp] theorem view_cons (memory : Memory) (head : Store) (tail : Buffer) :
    view memory (head :: tail) =
      view (writeDWordUnchecked memory head.address head.value) tail := rfl

theorem view_append (memory : Memory) (first second : Buffer) :
    view memory (first ++ second) = view (view memory first) second := by
  exact List.foldl_append

@[simp] theorem view_enqueue (memory : Memory) (buffer : Buffer) (store : Store) :
    view memory (enqueue buffer store) =
      writeDWordUnchecked (view memory buffer) store.address store.value := by
  simp [enqueue, view]

/-- Publishing the oldest pending write leaves this thread's own view unchanged. -/
theorem drain_view (memory : Memory) (head : Store) (tail : Buffer) :
    view (writeDWordUnchecked memory head.address head.value) tail =
      view memory (head :: tail) := rfl

@[simp] theorem view_executable (memory : Memory) (buffer : Buffer) :
    (view memory buffer).executable = memory.executable := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih => exact ih _

@[simp] theorem view_writable (memory : Memory) (buffer : Buffer) :
    (view memory buffer).writable = memory.writable := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem view_frame (memory : Memory) (buffer : Buffer) (query : Word)
    (outside : ∀ store ∈ buffer, 4 ≤ (query - store.address).toNat) :
    (view memory buffer).read query = memory.read query := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    rw [view_cons, ih _ (by
      intro store member
      exact outside store (List.mem_cons_of_mem head member))]
    exact writeDWord_frame _ _ _ _ (outside head (List.mem_cons_self))

theorem view_agrees (memory : Memory) (buffer : Buffer) (base : Word) (length : Nat)
    (disjoint : ∀ store ∈ buffer, DWordDisjoint store.address base length) :
    MemoryAgreesOn (view memory buffer) memory base length := by
  intro offset bound
  exact view_frame memory buffer _ (fun store member => disjoint store member offset bound)

theorem view_load_frame (memory : Memory) (buffer : Buffer) (address : Word)
    (disjoint : ∀ store ∈ buffer, DWordDisjoint store.address address 4) :
    loadDWord (view memory buffer) address = loadDWord memory address :=
  loadDWord_congr _ _ _ (view_agrees memory buffer address 4 disjoint)

theorem view_readWord_frame (memory : Memory) (buffer : Buffer) (address : Word)
    (disjoint : ∀ store ∈ buffer, DWordDisjoint store.address address 8) :
    readWord (view memory buffer) address = readWord memory address :=
  readWord_congr _ _ _ (view_agrees memory buffer address 8 disjoint)

theorem view_code (memory : Memory) (buffer : Buffer) (base : Word) (bytes : List Byte)
    (code : CodeAt memory base bytes)
    (disjoint : ∀ store ∈ buffer, DWordDisjoint store.address base bytes.length) :
    CodeAt (view memory buffer) base bytes := by
  induction buffer generalizing memory with
  | nil => exact code
  | cons head tail ih =>
    apply ih _ (writeDWord_preserves_code memory head.address base head.value bytes code
      (disjoint head List.mem_cons_self))
    intro store member
    exact disjoint store (List.mem_cons_of_mem head member)

/-- The newest enqueued same-address write supplies the complete load. -/
theorem load_enqueue (memory : Memory) (buffer : Buffer) (store : Store)
    (valid : dwordAddressable store.address = true) :
    loadDWord (view memory (enqueue buffer store)) store.address = .ok store.value := by
  rw [view_enqueue]
  exact load_after_write _ _ _ valid

/-- Later independent stores do not invalidate forwarding of the last matching write. -/
theorem load_enqueue_frame (memory : Memory) (buffer later : Buffer) (store : Store)
    (valid : dwordAddressable store.address = true)
    (disjoint : ∀ pending ∈ later, DWordDisjoint pending.address store.address 4) :
    loadDWord (view memory (enqueue buffer store ++ later)) store.address = .ok store.value := by
  rw [view_append, view_load_frame _ _ _ disjoint]
  exact load_enqueue memory buffer store valid

/-- Two four-byte footprints do not intersect, including modular addresses. -/
def Separate (a b : Word) : Prop :=
  ∀ query, 4 ≤ (query - a).toNat ∨ 4 ≤ (query - b).toNat

theorem separate_symm {a b : Word} (separate : Separate a b) : Separate b a := by
  intro query
  exact (separate query).symm

theorem write_read_congr (left right : Memory) (address query : Word) (value : BitVec 32)
    (same : left.read query = right.read query) :
    (writeDWordUnchecked left address value).read query =
      (writeDWordUnchecked right address value).read query := by
  simp only [writeDWordUnchecked, storedDWordByte]
  split <;> first | rfl | exact same

theorem write_commute (memory : Memory) (a b : Word) (va vb : BitVec 32)
    (separate : Separate a b) :
    writeDWordUnchecked (writeDWordUnchecked memory a va) b vb =
      writeDWordUnchecked (writeDWordUnchecked memory b vb) a va := by
  apply congrArg (fun read : Word → Option Byte => ({ memory with read := read } : Memory))
  funext query
  rcases separate query with outside | outside
  · exact (write_read_congr _ _ b query vb (writeDWord_frame memory a query va outside)).trans
      (writeDWord_frame (writeDWordUnchecked memory b vb) a query va outside).symm
  · exact (writeDWord_frame (writeDWordUnchecked memory a va) b query vb outside).trans
      (write_read_congr _ _ a query va (writeDWord_frame memory b query vb outside)).symm

/-- A globally visible independent write can pass all of this thread's buffered writes. -/
theorem view_write_commute (memory : Memory) (buffer : Buffer) (address : Word)
    (value : BitVec 32)
    (separate : ∀ store ∈ buffer, Separate store.address address) :
    view (writeDWordUnchecked memory address value) buffer =
      writeDWordUnchecked (view memory buffer) address value := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    simp only [view_cons]
    rw [write_commute memory address head.address value head.value
      (separate_symm (separate head List.mem_cons_self))]
    exact ih _ (fun store member => separate store (List.mem_cons_of_mem head member))

/-- Functional writes never remove the accessibility of an existing byte. -/
theorem write_readable (memory : Memory) (address query : Word) (value : BitVec 32)
    (readable : (memory.read query).isSome = true) :
    ((writeDWordUnchecked memory address value).read query).isSome = true := by
  simp only [writeDWordUnchecked, storedDWordByte]
  split <;> first | rfl | exact readable

theorem view_readable (memory : Memory) (buffer : Buffer) (query : Word)
    (readable : (memory.read query).isSome = true) :
    ((view memory buffer).read query).isSome = true := by
  induction buffer generalizing memory with
  | nil => exact readable
  | cons head tail ih => exact ih _ (write_readable _ _ _ _ readable)

theorem write_canStore (memory : Memory) (address query : Word) (value : BitVec 32)
    (allowed : canStoreDWord memory query = true) :
    canStoreDWord (writeDWordUnchecked memory address value) query = true := by
  simp only [canStoreDWord, dwordWritable, Bool.and_eq_true] at allowed ⊢
  rcases allowed with ⟨valid, permissions, ⟨⟨⟨r0, r1⟩, r2⟩, r3⟩⟩
  exact ⟨valid, permissions, ⟨⟨⟨write_readable _ _ _ _ r0,
    write_readable _ _ _ _ r1⟩, write_readable _ _ _ _ r2⟩,
    write_readable _ _ _ _ r3⟩⟩

theorem view_canStore (memory : Memory) (buffer : Buffer) (address : Word)
    (allowed : canStoreDWord memory address = true) :
    canStoreDWord (view memory buffer) address = true := by
  induction buffer generalizing memory with
  | nil => exact allowed
  | cons head tail ih => exact ih _ (write_canStore _ _ _ _ allowed)

theorem query_of_offset (address query : Word) (offset : Nat) (bound : offset < 4)
    (same : (query - address).toNat = offset) :
    query = address + BitVec.ofNat 64 offset := by
  have delta : query - address = BitVec.ofNat 64 offset := by
    apply BitVec.toNat_inj.mp
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset < 2^64 by omega)] using same
  exact (BitVec.sub_eq_iff_eq_add.mp delta).trans (BitVec.add_comm _ _)

theorem canStore_readable (memory : Memory) (address query : Word)
    (allowed : canStoreDWord memory address = true)
    (inside : (query - address).toNat < 4) :
    (memory.read query).isSome = true := by
  simp only [canStoreDWord, dwordWritable, Bool.and_eq_true] at allowed
  rcases allowed with ⟨_, _, ⟨⟨⟨r0, r1⟩, r2⟩, r3⟩⟩
  have offsets : (query - address).toNat = 0 ∨ (query - address).toNat = 1 ∨
      (query - address).toNat = 2 ∨ (query - address).toNat = 3 := by omega
  rcases offsets with h | h | h | h
  · simpa only [query_of_offset address query 0 (by decide) h, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using r0
  · simpa only [query_of_offset address query 1 (by decide) h, BitVec.ofNat_eq_ofNat] using r1
  · simpa only [query_of_offset address query 2 (by decide) h, BitVec.ofNat_eq_ofNat] using r2
  · simpa only [query_of_offset address query 3 (by decide) h, BitVec.ofNat_eq_ofNat] using r3

/-- A checked write changes values, never the accessible-byte domain. -/
theorem write_read_isSome (memory : Memory) (address query : Word) (value : BitVec 32)
    (allowed : canStoreDWord memory address = true) :
    ((writeDWordUnchecked memory address value).read query).isSome =
      (memory.read query).isSome := by
  by_cases outside : 4 ≤ (query - address).toNat
  · rw [writeDWord_frame _ _ _ _ outside]
  · have readable := canStore_readable memory address query allowed (by omega)
    rw [write_readable _ _ _ _ readable, readable]

theorem write_canStore_eq (memory : Memory) (address query : Word) (value : BitVec 32)
    (allowed : canStoreDWord memory address = true) :
    canStoreDWord (writeDWordUnchecked memory address value) query = canStoreDWord memory query := by
  simp only [canStoreDWord, dwordWritable,
    write_read_isSome memory address _ value allowed]
  rfl

/-- Independently checked pending stores cannot create new writable addresses. -/
theorem view_canStore_eq (memory : Memory) (buffer : Buffer) (address : Word)
    (pending : ∀ store ∈ buffer, canStoreDWord memory store.address = true) :
    canStoreDWord (view memory buffer) address = canStoreDWord memory address := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    rw [view_cons, ih _ (by
      intro store member
      exact write_canStore _ _ _ _ (pending store (List.mem_cons_of_mem head member)))]
    exact write_canStore_eq _ _ _ _ (pending head List.mem_cons_self)

theorem view_read_isSome (memory : Memory) (buffer : Buffer) (query : Word)
    (pending : ∀ store ∈ buffer, canStoreDWord memory store.address = true) :
    ((view memory buffer).read query).isSome = (memory.read query).isSome := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    rw [view_cons, ih _ (by
      intro store member
      exact write_canStore _ _ _ _ (pending store (List.mem_cons_of_mem head member)))]
    exact write_read_isSome _ _ _ _ (pending head List.mem_cons_self)

end EDSL.X86.StoreBuffer
