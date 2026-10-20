/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.StoreBuffer
import EDSL.X86.Memory64

namespace EDSL.X86.StoreBuffer.Mixed

/-- Ordinary write payloads; this tag imposes no architectural admission. -/
inductive Value where
  | dword (value : BitVec 32)
  | qword (value : Word)
  deriving DecidableEq, Repr

/-- An unchecked pending write. Buffers are ordered oldest first. -/
structure Store where
  address : Word
  value : Value
  deriving DecidableEq, Repr

def Store.width (store : Store) : Nat :=
  match store.value with
  | .dword _ => 4
  | .qword _ => 8

/-- Use the production byte updates, without performing scheduler/OS preflights. -/
def Store.publish (store : Store) (memory : Memory) : Memory :=
  match store.value with
  | .dword value => writeDWordUnchecked memory store.address value
  | .qword value => writeQWordUnchecked memory store.address value

/-- The production update supplies a byte exactly within this store's footprint. -/
def Store.byte (store : Store) (query : Word) : Option Byte :=
  (store.publish { read := fun _ => none, executable := fun _ => false }).read query

abbrev Buffer := List Store

def view (memory : Memory) (buffer : Buffer) : Memory :=
  buffer.foldl (fun current store => store.publish current) memory

def enqueue (buffer : Buffer) (store : Store) : Buffer := buffer ++ [store]

/-- Search newest first, independently for every addressed byte. -/
def forward : Buffer → Word → Option Byte
  | [], _ => none
  | head :: tail, query => (forward tail query).or (head.byte query)

/-- Publish only the FIFO head; an empty queue has no publication. -/
def publishOldest (memory : Memory) : Buffer → Option (Memory × Buffer)
  | [] => none
  | head :: tail => some (head.publish memory, tail)

theorem Store.publish_read (memory : Memory) (store : Store) (query : Word) :
    (store.publish memory).read query = (store.byte query).or (memory.read query) := by
  cases store with
  | mk address value =>
    cases value <;>
      simp only [Store.publish, Store.byte, writeDWordUnchecked, storedDWordByte,
        writeQWordUnchecked, storedQWordByte] <;>
      split <;> simp_all

/-- Each byte comes from the newest matching own store, or from global memory. -/
theorem view_read (memory : Memory) (buffer : Buffer) (query : Word) :
    (view memory buffer).read query = (forward buffer query).or (memory.read query) := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    change (view (head.publish memory) tail).read query = _
    rw [ih, Store.publish_read]
    exact Option.or_assoc.symm

theorem view_read_congr (left right : Memory) (buffer : Buffer) (query : Word)
    (same : left.read query = right.read query) :
    (view left buffer).read query = (view right buffer).read query := by
  rw [view_read, view_read, same]

@[simp] theorem view_nil (memory : Memory) : view memory [] = memory := rfl

@[simp] theorem view_cons (memory : Memory) (head : Store) (tail : Buffer) :
    view memory (head :: tail) = view (head.publish memory) tail := rfl

theorem view_append (memory : Memory) (first second : Buffer) :
    view memory (first ++ second) = view (view memory first) second :=
  List.foldl_append

@[simp] theorem view_enqueue (memory : Memory) (buffer : Buffer) (store : Store) :
    view memory (enqueue buffer store) = store.publish (view memory buffer) := by
  simp [enqueue, view]

theorem forward_append (first second : Buffer) (query : Word) :
    forward (first ++ second) query = (forward second query).or (forward first query) := by
  induction first with
  | nil => simp [forward]
  | cons head tail ih =>
    simp only [List.cons_append, forward, ih, Option.or_assoc]

@[simp] theorem forward_enqueue (buffer : Buffer) (store : Store) (query : Word) :
    forward (enqueue buffer store) query = (store.byte query).or (forward buffer query) := by
  simp [enqueue, forward_append, forward]

/-- Newer overlapping bytes override older writes without discarding their other bytes. -/
theorem view_enqueue_read (memory : Memory) (buffer : Buffer) (store : Store) (query : Word) :
    (view memory (enqueue buffer store)).read query =
      (store.byte query).or ((view memory buffer).read query) := by
  rw [view_enqueue, Store.publish_read]

/-- FIFO publication leaves the issuing worker's complete own view unchanged. -/
theorem drain_view (memory : Memory) (head : Store) (tail : Buffer) :
    view (head.publish memory) tail = view memory (head :: tail) := rfl

theorem publishOldest_view (memory published : Memory) (buffer remaining : Buffer)
    (publishedHead : publishOldest memory buffer = some (published, remaining)) :
    view published remaining = view memory buffer := by
  cases buffer with
  | nil => simp [publishOldest] at publishedHead
  | cons head tail =>
    simp only [publishOldest, Option.some.injEq, Prod.mk.injEq] at publishedHead
    rcases publishedHead with ⟨rfl, rfl⟩
    exact drain_view memory head tail

@[simp] theorem Store.publish_executable (memory : Memory) (store : Store) :
    (store.publish memory).executable = memory.executable := by
  cases store with
  | mk address value => cases value <;> rfl

@[simp] theorem Store.publish_writable (memory : Memory) (store : Store) :
    (store.publish memory).writable = memory.writable := by
  cases store with
  | mk address value => cases value <;> rfl

@[simp] theorem view_executable (memory : Memory) (buffer : Buffer) :
    (view memory buffer).executable = memory.executable := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih => rw [view_cons, ih, Store.publish_executable]

@[simp] theorem view_writable (memory : Memory) (buffer : Buffer) :
    (view memory buffer).writable = memory.writable := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih => rw [view_cons, ih, Store.publish_writable]

theorem Store.publish_frame (memory : Memory) (store : Store) (query : Word)
    (outside : store.width ≤ (query - store.address).toNat) :
    (store.publish memory).read query = memory.read query := by
  cases store with
  | mk address value =>
    cases value with
    | dword value => exact writeDWord_frame memory address query value outside
    | qword value => exact writeQWord_frame memory address query value outside

theorem Store.byte_frame (store : Store) (query : Word)
    (outside : store.width ≤ (query - store.address).toNat) : store.byte query = none :=
  Store.publish_frame _ store query outside

theorem view_frame (memory : Memory) (buffer : Buffer) (query : Word)
    (outside : ∀ store ∈ buffer, store.width ≤ (query - store.address).toNat) :
    (view memory buffer).read query = memory.read query := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    rw [view_cons, ih _ (fun store member => outside store (List.mem_cons_of_mem head member))]
    exact head.publish_frame memory query (outside head List.mem_cons_self)

/-- Disjointness uses the same modular footprints as the production writes. -/
def Store.Disjoint (store : Store) (base : Word) (length : Nat) : Prop :=
  ∀ offset, offset < length →
    store.width ≤ ((base + BitVec.ofNat 64 offset) - store.address).toNat

theorem view_agrees (memory : Memory) (buffer : Buffer) (base : Word) (length : Nat)
    (disjoint : ∀ store ∈ buffer, store.Disjoint base length) :
    MemoryAgreesOn (view memory buffer) memory base length := by
  intro offset bound
  exact view_frame memory buffer _ (fun store member => disjoint store member offset bound)

theorem view_readDataByte_frame (memory : Memory) (buffer : Buffer) (address : Word)
    (outside : ∀ store ∈ buffer, store.width ≤ (address - store.address).toNat) :
    readDataByte (view memory buffer) address = readDataByte memory address := by
  unfold readDataByte
  rw [view_frame memory buffer address outside]

theorem view_loadDWord_frame (memory : Memory) (buffer : Buffer) (address : Word)
    (disjoint : ∀ store ∈ buffer, store.Disjoint address 4) :
    loadDWord (view memory buffer) address = loadDWord memory address :=
  loadDWord_congr _ _ _ (view_agrees memory buffer address 4 disjoint)

theorem view_loadQWord_frame (memory : Memory) (buffer : Buffer) (address : Word)
    (disjoint : ∀ store ∈ buffer, store.Disjoint address 8) :
    loadQWord (view memory buffer) address = loadQWord memory address :=
  loadQWord_congr _ _ _ (view_agrees memory buffer address 8 disjoint)

theorem view_readWord_frame (memory : Memory) (buffer : Buffer) (address : Word)
    (disjoint : ∀ store ∈ buffer, store.Disjoint address 8) :
    readWord (view memory buffer) address = readWord memory address :=
  readWord_congr _ _ _ (view_agrees memory buffer address 8 disjoint)

theorem view_code (memory : Memory) (buffer : Buffer) (base : Word) (bytes : List Byte)
    (code : CodeAt memory base bytes)
    (disjoint : ∀ store ∈ buffer, store.Disjoint base bytes.length) :
    CodeAt (view memory buffer) base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have unchanged := view_agrees memory buffer base bytes.length disjoint offset bound
  have sameFetch : fetchByte (view memory buffer) (base + BitVec.ofNat 64 offset) =
      fetchByte memory (base + BitVec.ofNat 64 offset) := by
    unfold fetchByte
    rw [view_executable, unchanged]
  exact sameFetch.trans (code.2 offset byte atOffset)

theorem loadDWord_enqueue (memory : Memory) (buffer : Buffer) (address : Word)
    (value : BitVec 32) (valid : dwordAddressable address = true) :
    loadDWord (view memory (enqueue buffer ⟨address, .dword value⟩)) address = .ok value := by
  rw [view_enqueue]
  exact load_after_write _ _ _ valid

/-- The existing production qword addressability premise is required unchanged. -/
theorem loadQWord_enqueue (memory : Memory) (buffer : Buffer) (address value : Word)
    (valid : qwordAddressable address = true) :
    loadQWord (view memory (enqueue buffer ⟨address, .qword value⟩)) address = .ok value := by
  rw [view_enqueue]
  exact qword_load_after_write _ _ _ valid

theorem loadQWord_enqueue_frame (memory : Memory) (buffer later : Buffer) (address value : Word)
    (valid : qwordAddressable address = true)
    (disjoint : ∀ store ∈ later, store.Disjoint address 8) :
    loadQWord (view memory (enqueue buffer ⟨address, .qword value⟩ ++ later)) address =
      .ok value := by
  rw [view_append, view_loadQWord_frame _ _ _ disjoint]
  exact loadQWord_enqueue memory buffer address value valid

/-- Every old store embeds without changing addresses, values or byte semantics. -/
def embedStore32 (store : EDSL.X86.StoreBuffer.Store) : Store :=
  ⟨store.address, .dword store.value⟩

def embed32 (buffer : EDSL.X86.StoreBuffer.Buffer) : Buffer := buffer.map embedStore32

@[simp] theorem publish_embedStore32 (memory : Memory) (store : EDSL.X86.StoreBuffer.Store) :
    (embedStore32 store).publish memory =
      writeDWordUnchecked memory store.address store.value := rfl

@[simp] theorem byte_embedStore32 (store : EDSL.X86.StoreBuffer.Store) (query : Word) :
    (embedStore32 store).byte query = store.byte query := rfl

/-- Exact memory equality for every old buffer, including unchecked modular ones. -/
@[simp] theorem view_embed32 (memory : Memory) (buffer : EDSL.X86.StoreBuffer.Buffer) :
    view memory (embed32 buffer) = EDSL.X86.StoreBuffer.view memory buffer := by
  induction buffer generalizing memory with
  | nil => rfl
  | cons head tail ih =>
    change view (writeDWordUnchecked memory head.address head.value) (embed32 tail) = _
    exact ih _

@[simp] theorem forward_embed32 (buffer : EDSL.X86.StoreBuffer.Buffer) (query : Word) :
    forward (embed32 buffer) query = EDSL.X86.StoreBuffer.forward buffer query := by
  induction buffer with
  | nil => rfl
  | cons head tail ih =>
    change (forward (embed32 tail) query).or ((embedStore32 head).byte query) = _
    rw [ih, byte_embedStore32]
    rfl

@[simp] theorem enqueue_embed32 (buffer : EDSL.X86.StoreBuffer.Buffer)
    (store : EDSL.X86.StoreBuffer.Store) :
    embed32 (EDSL.X86.StoreBuffer.enqueue buffer store) =
      enqueue (embed32 buffer) (embedStore32 store) := by
  simp [embed32, EDSL.X86.StoreBuffer.enqueue, enqueue]

end EDSL.X86.StoreBuffer.Mixed
