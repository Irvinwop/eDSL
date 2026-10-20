/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.BufferCall.Elements
import EDSL.Grading.FirstMatch

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.IndexSearch
open X86 X86.Sequential BufferCall

universe u
variable {α : Type u} [DecidableEq α]

def equals (key value : α) : Bool := decide (value = key)

/-- The full 64-bit absent value, never a truncated 32-bit return. -/
def sizeMax : Word := BitVec.ofNat 64 (2^64 - 1)

@[simp] theorem sizeMax_toNat : sizeMax.toNat = 2^64 - 1 := rfl

/-- FirstMatch uses n for exhaustion; the callable interface uses SIZE_MAX. -/
def encode (length index : Nat) : Word :=
  if index < length then BitVec.ofNat 64 index else sizeMax

/-- Independent earliest-match mathematics, followed by the specified encoding.
The prefix and hit requirements are exactly generic FirstMatch.Result. -/
def Result (values : List α) (key : α) (actual : Word) : Prop :=
  ∃ index, FirstMatch.Result values (equals key) index ∧ actual = encode values.length index

theorem matchesAt_iff {values : List α} {key : α} {index : Nat} :
    FirstMatch.MatchesAt values (equals key) index ↔ values[index]? = some key := by
  constructor
  · rintro ⟨value, present, accepted⟩
    have same : value = key := of_decide_eq_true accepted
    simpa only [same] using present
  · intro present
    exact ⟨key, present, by simp [equals]⟩

theorem Result.exists (values : List α) (key : α) : ∃ actual, Result values key actual := by
  obtain ⟨index, first⟩ := FirstMatch.Result.exists values (equals key)
  exact ⟨encode values.length index, index, first, rfl⟩

theorem Result.unique {values : List α} {key : α} {a b : Word}
    (first : Result values key a) (second : Result values key b) : a = b := by
  obtain ⟨i, atI, encodedA⟩ := first
  obtain ⟨j, atJ, encodedB⟩ := second
  rw [encodedA, encodedB, atI.unique atJ]

/-- List.findIdx is a consequence of the relation, not its definition. -/
theorem Result.iff_findIdx {values : List α} {key : α} {actual : Word} :
    Result values key actual ↔ actual = encode values.length (values.findIdx (equals key)) := by
  simp only [Result, FirstMatch.Result.iff_findIdx, exists_eq_left]

theorem encode_eq_sizeMax_iff {length index : Nat} (small : length < 2^64)
    (bound : index ≤ length) : encode length index = sizeMax ↔ index = length := by
  by_cases inside : index < length
  · rw [encode, ite_eq_left inside]
    constructor
    · intro same
      have equal := congrArg BitVec.toNat same
      change index % 2^64 = (2^64 - 1) % 2^64 at equal
      rw [Nat.mod_eq_of_lt (show index < 2^64 by omega),
        Nat.mod_eq_of_lt (by decide)] at equal
      omega
    · intro same
      omega
  · have same : index = length := by omega
    simp [encode, same]

theorem Result.sentinel_iff {values : List α} {key : α} {actual : Word}
    (result : Result values key actual) (small : values.length < 2^64) :
    actual = sizeMax ↔ ∀ value ∈ values, value ≠ key := by
  obtain ⟨index, first, encoded⟩ := result
  rw [encoded, encode_eq_sizeMax_iff small first.bound]
  simpa only [equals, decide_eq_false_iff_not] using first.eq_length_iff

/-- A nonsentinel return identifies a present key and excludes every earlier
key. All 64 return bits participate in the index and sentinel distinction. -/
theorem Result.present {values : List α} {key : α} {actual : Word}
    (result : Result values key actual) (small : values.length < 2^64)
    (found : actual ≠ sizeMax) :
    actual.toNat < values.length ∧ values[actual.toNat]? = some key ∧
      ∀ index, index < actual.toNat → values[index]? ≠ some key := by
  obtain ⟨index, first, encoded⟩ := result
  have inside : index < values.length := by
    have different : index ≠ values.length := by
      intro same
      exact found (encoded.trans ((encode_eq_sizeMax_iff small first.bound).mpr same))
    have bound := first.bound
    omega
  have natural : actual.toNat = index := by
    rw [encoded, encode, ite_eq_left inside, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show index < 2^64 by omega)]
  rw [natural]
  refine ⟨inside, matchesAt_iff.mp (first.hit inside), ?_⟩
  intro earlier before present
  exact first.nonmatch earlier before (matchesAt_iff.mpr present)

theorem Result.of_hit {values : List α} {key : α} {index : Nat}
    (scanned : FirstMatch.Prefix values (equals key) index)
    (hit : values[index]? = some key) : Result values key (BitVec.ofNat 64 index) := by
  have matchAt := matchesAt_iff.mpr hit
  exact ⟨index, scanned.finish_hit matchAt, by simp only [encode, ite_eq_left matchAt.bound]⟩

theorem Result.of_absent {values : List α} {key : α}
    (absent : ∀ value ∈ values, value ≠ key) : Result values key sizeMax := by
  refine ⟨values.length, (FirstMatch.Result.at_bound_iff values (equals key)).mpr ?_, ?_⟩
  · simpa only [equals, decide_eq_false_iff_not] using absent
  · simp [encode]

theorem Result.nil_iff (key : α) (actual : Word) :
    Result [] key actual ↔ actual = sizeMax := by
  simp only [Result.iff_findIdx, List.findIdx_nil, List.length_nil, encode,
    Nat.lt_irrefl, ↓reduceIte]

/-- Shared input shape only; each fixed task below binds its entire Spec. -/
structure Input (Element : Type) where
  base : Word
  values : List Element
  key : Element

abbrev ByteInput := Input Byte
abbrev U32Input := Input (BitVec 32)

def byteBuffer (input : ByteInput) : Buffer := ⟨input.base, input.values⟩
def u32Buffer (input : U32Input) : Buffer := ⟨input.base, Elements.u32Bytes input.values⟩

/-- RDI and RSI are full64 base and element count. Only RDX.low8 is the byte
key; its upper bits are unrestricted. Empty inputs need no data memory. -/
def byteSpec : Spec where
  Input := ByteInput
  arguments input index :=
    match index.val with
    | 0 => some (.word64 input.base)
    | 1 => some (.word64 (BitVec.ofNat 64 input.values.length))
    | 2 => some (.low8 input.key)
    | _ => none
  buffers input := [byteBuffer input]
  domain input := input.values.length < 2^64
  result input actual := Result input.values input.key actual
  useful input := input.values ≠ []

/-- RDX.low32 is the unsigned word key, with arbitrary upper bits. A single
little-endian full-buffer snapshot supplies the actual 4*n nonwrapping extent.
No pointer alignment, small count cap, result or execution premise is imposed. -/
def u32Spec : Spec where
  Input := U32Input
  arguments input index :=
    match index.val with
    | 0 => some (.word64 input.base)
    | 1 => some (.word64 (BitVec.ofNat 64 input.values.length))
    | 2 => some (.low32 input.key)
    | _ => none
  buffers input := [u32Buffer input]
  domain input := input.values.length < 2^64
  result input actual := Result input.values input.key actual
  useful input := input.values ≠ []

theorem byte_result_empty (base : Word) (key : Byte) (actual : Word) :
    byteSpec.result ⟨base, [], key⟩ actual ↔ actual = sizeMax := Result.nil_iff key actual

theorem u32_result_empty (base : Word) (key : BitVec 32) (actual : Word) :
    u32Spec.result ⟨base, [], key⟩ actual ↔ actual = sizeMax := Result.nil_iff key actual

theorem byte_snapshot {bytes : List Byte} {input : Invocation byteSpec} {initial : State}
    (pre : Pre byteSpec bytes input initial) :
    BufferAt initial.memory input.value.base input.value.values :=
  pre.buffers (byteBuffer input.value) (by simp [byteSpec])

theorem u32_snapshot {bytes : List Byte} {input : Invocation u32Spec} {initial : State}
    (pre : Pre u32Spec bytes input initial) :
    BufferAt initial.memory input.value.base (Elements.u32Bytes input.value.values) :=
  pre.buffers (u32Buffer input.value) (by simp [u32Spec])

/-- Successful DATA1 reads and their positive raw footprints follow from the
initial snapshot; no machine execution is assumed. -/
theorem byte_read {bytes : List Byte} {input : Invocation byteSpec} {initial : State}
    (pre : Pre byteSpec bytes input initial) {index : Nat} {value : Byte}
    (present : input.value.values[index]? = some value) :
    readDataByte initial.memory (input.value.base + BitVec.ofNat 64 index) = .ok value ∧
      RawRead byteSpec input initial ⟨.data, input.value.base + BitVec.ofNat 64 index, 1⟩ := by
  have snapshot := byte_snapshot pre
  refine ⟨snapshot.2 index value present, .inr ⟨rfl, byteBuffer input.value,
    by simp [byteSpec], ?_⟩⟩
  exact Elements.byte_element_span snapshot (List.getElem_of_getElem? present).1

/-- Actual unaligned DATA4 load success and the full operand footprint are
derived from the original full-buffer bytes. -/
theorem u32_read {bytes : List Byte} {input : Invocation u32Spec} {initial : State}
    (pre : Pre u32Spec bytes input initial) {index : Nat} {value : BitVec 32}
    (present : input.value.values[index]? = some value) :
    loadDWord initial.memory (input.value.base + BitVec.ofNat 64 (4 * index)) = .ok value ∧
      RawRead u32Spec input initial ⟨.data, input.value.base + BitVec.ofNat 64 (4 * index), 4⟩ := by
  have snapshot := u32_snapshot pre
  refine ⟨Elements.u32_loadDWord snapshot present, .inr ⟨rfl, u32Buffer input.value,
    by simp [u32Spec], ?_⟩⟩
  exact Elements.u32_element_span snapshot (List.getElem_of_getElem? present).1

/-- Current DATA1 authority and value, supplied by the existing resource
adapter without adding an execution model or an alias restriction. -/
theorem byte_read_current {resource : Resources byteSpec} {machine : State}
    (current : Current resource machine) {index : Nat} {value : Byte}
    (present : resource.value.values[index]? = some value) :
    readDataByte machine.memory (resource.value.base + BitVec.ofNat 64 index) = .ok value ∧
      ReadAllowed resource ⟨.data, resource.value.base + BitVec.ofNat 64 index, 1⟩ := by
  have member : byteBuffer resource.value ∈ byteSpec.buffers resource.value := by simp [byteSpec]
  have snapshot := current.buffer member
  have footprint : DataRead (byteSpec.buffers resource.value)
      ⟨.data, resource.value.base + BitVec.ofNat 64 index, 1⟩ :=
    ⟨rfl, byteBuffer resource.value, member,
      Elements.byte_element_span snapshot (List.getElem_of_getElem? present).1⟩
  exact ⟨snapshot.2 index value present,
    .inr ⟨footprint, current.contract.dataRead_permission footprint⟩⟩

/-- Current DATA4 authority and exact little-endian value use the same generic
resource bridge, preserving its caller, all RAM/permissions and read-only policy. -/
theorem u32_read_current {resource : Resources u32Spec} {machine : State}
    (current : Current resource machine) {index : Nat} {value : BitVec 32}
    (present : resource.value.values[index]? = some value) :
    loadDWord machine.memory (resource.value.base + BitVec.ofNat 64 (4 * index)) = .ok value ∧
      ReadAllowed resource ⟨.data, resource.value.base + BitVec.ofNat 64 (4 * index), 4⟩ := by
  have member : u32Buffer resource.value ∈ u32Spec.buffers resource.value := by simp [u32Spec]
  have snapshot := current.buffer member
  have footprint : DataRead (u32Spec.buffers resource.value)
      ⟨.data, resource.value.base + BitVec.ofNat 64 (4 * index), 4⟩ :=
    ⟨rfl, u32Buffer resource.value, member,
      Elements.u32_element_span snapshot (List.getElem_of_getElem? present).1⟩
  exact ⟨Elements.u32_loadDWord snapshot present,
    .inr ⟨footprint, current.contract.dataRead_permission footprint⟩⟩

/-- Arbitrary empty pointers and unused loan IDs require just the original
caller/code contract. This does not assert an execution or a resource witness. -/
theorem byte_empty_resources {resource : Resources byteSpec} {shared : OS.Borrowing.State}
    (call : OS.CallResources.Contract resource.call shared) (empty : resource.value.values = []) :
    ResourceContract resource shared := by
  apply ResourceContract.of_empty call
  intro buffer member
  have same : buffer = byteBuffer resource.value := by simpa [byteSpec] using member
  subst buffer
  exact empty

theorem u32_empty_resources {resource : Resources u32Spec} {shared : OS.Borrowing.State}
    (call : OS.CallResources.Contract resource.call shared) (empty : resource.value.values = []) :
    ResourceContract resource shared := by
  apply ResourceContract.of_empty call
  intro buffer member
  have same : buffer = u32Buffer resource.value := by simpa [u32Spec] using member
  subst buffer
  simp [u32Buffer, empty]

end EDSL.Grading.IndexSearch
