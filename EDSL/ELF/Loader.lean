/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.Format

namespace EDSL.ELF
open X86 OS.AddressSpace

def Segment.Contains (segment : Segment) (address : Nat) : Prop :=
  segment.virtualAddress ≤ address ∧ address < segment.virtualAddress + segment.memorySize

instance (segment : Segment) (address : Nat) : Decidable (segment.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

def segmentAt (image : Image) (address : Nat) : Option Segment :=
  image.segments.find? fun segment => decide (segment.Contains address)

/-- Exact segment bytes followed by BSS zeros. Page padding is deliberately not
installed by this abstract image loader. Missing file data does not become zero. -/
def segmentCell (file : List Byte) (segment : Segment) (address : Nat) : Option Cell :=
  let offset := address - segment.virtualAddress
  if offset < segment.fileSize then
    file[segment.offset + offset]?.map fun byte => ⟨byte, segment.permissions⟩
  else some ⟨0, segment.permissions⟩

/-- Initialization can install final read-only or executable bytes without
pretending that an ordinary user store can write through those permissions. -/
def install (file : List Byte) (image : Image) (prior : Space) : Space where
  cells address :=
    match segmentAt image address.toNat with
    | some segment => segmentCell file segment address.toNat
    | none => prior.cells address

/-- Freshness covers rounded pages, even though only exact segment bytes are
installed. The caller's hidden cells also count as existing mappings. -/
def fresh (image : Image) (prior : Space) : Bool :=
  image.segments.all fun segment => allUnmapped prior segment.pageRegion

structure Loaded where
  image : Image
  space : Space

def load (file : List Byte) (prior : Space) : Except Error Loaded := do
  let image ← parse file
  if fresh image prior then return ⟨image, install file image prior⟩
  else throw .mappingCollision

def codeAddress (image : Image) : Word := BitVec.ofNat 64 image.entry

/-- Check the selected complete function window is executable and file-backed. -/
def fileBackedWindow (image : Image) (length : Nat) : Bool :=
  decide (0 < length ∧ length ≤ 64 ∧ image.entry + length ≤ 2^47) &&
  image.segments.any fun segment => segment.executable &&
    decide (segment.virtualAddress ≤ image.entry ∧ image.entry + length ≤
      segment.virtualAddress + segment.fileSize)

/-- Executable checker for the independently stated CodeAt proposition. -/
def checkCode (memory : X86.Memory) (base : Word) (bytes : List Byte) : Bool :=
  decide (base.toNat + bytes.length ≤ 2^64) &&
  (List.range bytes.length).all fun index =>
    (bytes[index]?.map fun byte =>
      match fetchByte memory (base + BitVec.ofNat 64 index) with
      | .ok observed => decide (observed = byte)
      | .error _ => false).getD false

def checkEntry (file : List Byte) (image : Image) (bytes : List Byte) : Bool :=
  fileBackedWindow image bytes.length &&
    checkCode (toMemory (install file image empty)) (codeAddress image) bytes

theorem checkCode_sound (memory : X86.Memory) (base : Word) (bytes : List Byte)
    (checked : checkCode memory base bytes = true) : CodeAt memory base bytes := by
  obtain ⟨bound, checked⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨of_decide_eq_true bound, ?_⟩
  intro index byte atIndex
  obtain ⟨indexBound, _⟩ := List.getElem_of_getElem? atIndex
  have checkAt := List.all_eq_true.mp checked index (List.mem_range.mpr indexBound)
  simp only [atIndex, Option.map_some, Option.getD_some] at checkAt
  cases fetched : fetchByte memory (base + BitVec.ofNat 64 index) with
  | error error => simp [fetched] at checkAt
  | ok observed =>
    have equal : observed = byte := of_decide_eq_true (by simpa [fetched] using checkAt)
    cases equal
    rfl

theorem install_outside (file : List Byte) (image : Image) (prior : Space) (address : Word)
    (outside : ∀ segment ∈ image.segments, ¬segment.Contains address.toNat) :
    (install file image prior).cells address = prior.cells address := by
  have absent : segmentAt image address.toNat = none := by
    apply List.find?_eq_none.mpr
    simpa only [decide_eq_true_eq] using outside
  simp [install, absent]

theorem install_file_byte (file : List Byte) (image : Image) (prior : Space)
    (segment : Segment) (address : Word) (byte : Byte)
    (selected : segmentAt image address.toNat = some segment)
    (backed : address.toNat - segment.virtualAddress < segment.fileSize)
    (fileByte : file[segment.offset + (address.toNat - segment.virtualAddress)]? = some byte) :
    (install file image prior).cells address = some ⟨byte, segment.permissions⟩ := by
  simp [install, selected, segmentCell, backed, fileByte]

theorem install_bss (file : List Byte) (image : Image) (prior : Space)
    (segment : Segment) (address : Word)
    (selected : segmentAt image address.toNat = some segment)
    (bss : segment.fileSize ≤ address.toNat - segment.virtualAddress) :
    (install file image prior).cells address = some ⟨0, segment.permissions⟩ := by
  simp [install, selected, segmentCell, show ¬ address.toNat - segment.virtualAddress < segment.fileSize by omega]

/-- Successful executable bytes generated from an empty space are independent
of any caller cells: a successful fetch cannot have come from the empty caller. -/
theorem installed_fetch_independent (file : List Byte) (image : Image)
    (prior : Space) (address : Word) (byte : Byte)
    (fetched : fetchByte (toMemory (install file image empty)) address = .ok byte) :
    fetchByte (toMemory (install file image prior)) address = .ok byte := by
  cases selected : segmentAt image address.toNat with
  | none => simp [fetchByte, toMemory, install, selected, empty] at fetched
  | some segment =>
    simpa only [fetchByte, toMemory, install, selected] using fetched

theorem checked_entry_code (file : List Byte) (image : Image) (bytes : List Byte)
    (prior : Space) (checked : checkEntry file image bytes = true) :
    CodeAt (toMemory (install file image prior)) (codeAddress image) bytes := by
  have code := checkCode_sound _ _ _ (Bool.and_eq_true_iff.mp checked).2
  refine ⟨code.1, ?_⟩
  intro index byte atIndex
  exact installed_fetch_independent file image prior _ byte (code.2 index byte atIndex)

theorem load_success (file : List Byte) (prior : Space) (image : Image)
    (parsed : parse file = .ok image) (free : fresh image prior = true) :
    load file prior = .ok ⟨image, install file image prior⟩ := by
  simp [load, parsed, free]

theorem load_ok (file : List Byte) (prior : Space) (result : Loaded)
    (success : load file prior = .ok result) :
    parse file = .ok result.image ∧ fresh result.image prior = true ∧
    result.space = install file result.image prior := by
  cases parsed : parse file with
  | error error => simp [load, parsed] at success
  | ok image =>
    by_cases free : fresh image prior = true
    · simp [load, parsed, free] at success
      cases success
      exact ⟨rfl, free, rfl⟩
    · simp [load, parsed, free] at success

/-- Selection comes from a validated program header and its exact byte interval. -/
theorem selected_valid (file : List Byte) (image : Image) (segment : Segment) (address : Nat)
    (checked : valid file image = true) (selected : segmentAt image address = some segment) :
    segment.valid file.length = true ∧ segment.Contains address := by
  simp only [valid, Bool.and_eq_true] at checked
  have member := List.mem_of_find?_eq_some selected
  have inside := List.find?_some selected
  exact ⟨List.all_eq_true.mp checked.1.1.2 segment member, of_decide_eq_true inside⟩

/-- Exact segment byte ranges lie within the pages used for freshness checking. -/
theorem segment_inside_pages (segment : Segment) (fileLength : Nat) (address : Word)
    (checked : segment.valid fileLength = true) (inside : segment.Contains address.toNat) :
    segment.pageRegion.Contains address := by
  have bounds := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
  have lower := inside.1
  have upper := inside.2
  have startBound : segment.pageStart < 2^64 := by
    simp only [Segment.pageStart, pageSize]
    omega
  simp only [Segment.pageRegion, Region.Contains, BitVec.toNat_ofNat,
    Segment.pageStart, Segment.pageEnd, pageSize]
  constructor <;> omega

/-- A fresh loaded image cannot replace any prior mapped cell, including hidden
ones. This is logical cell preservation, not physical-page ownership. -/
theorem install_preserves_existing (file : List Byte) (image : Image) (prior : Space)
    (checked : valid file image = true) (free : fresh image prior = true)
    (address : Word) (cell : Cell) (existing : prior.cells address = some cell) :
    (install file image prior).cells address = some cell := by
  cases selected : segmentAt image address.toNat with
  | none => simp [install, selected, existing]
  | some segment =>
    have validated := selected_valid file image segment address.toNat checked selected
    have pageContains := segment_inside_pages segment file.length address validated.1 validated.2
    have unmapped := List.all_eq_true.mp free segment (List.mem_of_find?_eq_some selected)
    have missing := allUnmapped_inside prior segment.pageRegion unmapped address pageContains
    rw [existing] at missing
    contradiction

end EDSL.ELF
