/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.Loader

namespace EDSL.ELF.FunctionWindow
open X86 OS.AddressSpace

/-- Untrusted metadata witnesses are checked against the complete literal file.
No symbol name, section contents, interpreter or relocation is interpreted. -/
structure Header where
  osAbi : Nat
  entry : Nat
  programOffset : Nat
  sectionOffset : Nat
  sectionCount : Nat
  sectionNames : Nat
  deriving DecidableEq, Repr

structure ProgramHeader where
  kind : Nat
  physicalAddress : Nat
  segment : Segment
  deriving DecidableEq, Repr

structure Table where
  header : Header
  programs : List ProgramHeader
  deriving DecidableEq, Repr

def Table.image (table : Table) : Image :=
  ⟨table.header.entry, (table.programs.filter (fun row => row.kind == 1)).map (·.segment)⟩

/-- This descriptor identifies an address and file interval, never a symbol. -/
structure Window where
  address : Nat
  offset : Nat
  deriving DecidableEq, Repr

def Window.base (window : Window) : Word := BitVec.ofNat 64 window.address

structure Field where
  offset : Nat
  width : Nat
  value : Nat
  deriving DecidableEq, Repr

/-- Independent bounded little-endian field relation, with natural arithmetic. -/
def Field.Holds (file : List Byte) (field : Field) : Prop :=
  field.offset + field.width ≤ file.length ∧
  ((file.drop field.offset).take field.width).foldr
    (fun byte rest => byte.toNat + rest * 256) 0 = field.value

def Header.fields (header : Header) (count : Nat) : List Field := [
  ⟨0, 4, 0x464c457f⟩, ⟨4, 1, 2⟩, ⟨5, 1, 1⟩, ⟨6, 1, 1⟩,
  ⟨7, 1, header.osAbi⟩, ⟨8, 1, 0⟩, ⟨9, 7, 0⟩,
  ⟨16, 2, 2⟩, ⟨18, 2, 62⟩, ⟨20, 4, 1⟩, ⟨24, 8, header.entry⟩,
  ⟨32, 8, header.programOffset⟩, ⟨40, 8, header.sectionOffset⟩, ⟨48, 4, 0⟩,
  ⟨52, 2, 64⟩, ⟨54, 2, 56⟩, ⟨56, 2, count⟩,
  ⟨58, 2, 64⟩, ⟨60, 2, header.sectionCount⟩, ⟨62, 2, header.sectionNames⟩]

/-- This profile requires an ordinary bounded section table but does not check
its contents. Extended numbering and sectionless images are unsupported. -/
def Header.Shape (header : Header) (fileLength count : Nat) : Prop :=
  64 ≤ fileLength ∧ fileLength ≤ maxFileSize ∧
  (header.osAbi = 0 ∨ header.osAbi = 3) ∧
  0 < count ∧ count ≤ maxProgramHeaders ∧
  64 ≤ header.programOffset ∧ header.programOffset % 8 = 0 ∧
  header.programOffset + count * 56 ≤ fileLength ∧
  0 < header.sectionCount ∧ header.sectionCount ≤ maxFileSize / 64 ∧
  64 ≤ header.sectionOffset ∧ header.sectionOffset % 8 = 0 ∧
  header.sectionOffset + header.sectionCount * 64 ≤ fileLength ∧
  header.sectionNames < header.sectionCount

instance (header : Header) (fileLength count : Nat) :
    Decidable (header.Shape fileLength count) := inferInstanceAs (Decidable (_ ∧ _))

def ProgramHeader.fields (row : ProgramHeader) (base : Nat) : List Field := [
  ⟨base, 4, row.kind⟩, ⟨base + 4, 4, row.segment.flags⟩,
  ⟨base + 8, 8, row.segment.offset⟩, ⟨base + 16, 8, row.segment.virtualAddress⟩,
  ⟨base + 24, 8, row.physicalAddress⟩, ⟨base + 32, 8, row.segment.fileSize⟩,
  ⟨base + 40, 8, row.segment.memorySize⟩, ⟨base + 48, 8, row.segment.alignment⟩]

/-- Only PT_LOAD maps cells. Recognized metadata is bounded opaque data; in
particular accepting PT_DYNAMIC neither applies nor validates relocations. -/
def ProgramHeader.Supported (row : ProgramHeader) (fileLength : Nat) : Prop :=
  row.kind = 1 ∨
  (row.kind ∈ [0, 2, 3, 4, 6, 0x6474e550, 0x6474e551, 0x6474e552, 0x6474e553] ∧
    row.segment.offset + row.segment.fileSize ≤ fileLength ∧
    row.segment.fileSize ≤ row.segment.memorySize ∧ row.segment.flags < 8 ∧
    row.segment.virtualAddress + row.segment.memorySize ≤ 2^47 ∧
    (row.kind = 0x6474e551 → row.segment.flags = 6 ∧
      row.segment.fileSize = 0 ∧ row.segment.memorySize = 0))

instance (row : ProgramHeader) (fileLength : Nat) :
    Decidable (row.Supported fileLength) := inferInstanceAs (Decidable (_ ∨ _))

/-- Declarative syntax/layout contract: all 64 header bytes and every 56-byte
program row match, every row is supported, and all LOADs pass the existing
validator (including ordered disjoint rounded pages and entry validation). -/
structure Layout (file : List Byte) (table : Table) : Prop where
  bounded : table.header.Shape file.length table.programs.length
  header : ∀ field ∈ table.header.fields table.programs.length, field.Holds file
  rows : ∀ pair ∈ table.programs.zipIdx,
    (∀ field ∈ pair.1.fields (table.header.programOffset + pair.2 * 56), field.Holds file) ∧
    pair.1.Supported file.length
  loads : valid file table.image = true

private def checkFields (file : List Byte) (fields : List Field) : Bool :=
  fields.all fun field =>
    match readNat file field.offset field.width with
    | .ok observed => decide (observed = field.value)
    | .error _ => false

def checkLayout (file : List Byte) (table : Table) : Bool :=
  decide (table.header.Shape file.length table.programs.length) &&
  checkFields file (table.header.fields table.programs.length) &&
  table.programs.zipIdx.all (fun pair =>
    checkFields file (pair.1.fields (table.header.programOffset + pair.2 * 56)) &&
    decide (pair.1.Supported file.length)) && valid file table.image

private theorem checkFields_sound (file : List Byte) (fields : List Field)
    (checked : checkFields file fields = true) : ∀ field ∈ fields, field.Holds file := by
  intro field member
  have read := List.all_eq_true.mp checked field member
  cases decoded : readNat file field.offset field.width with
  | error error => simp [decoded] at read
  | ok observed =>
    have equal : observed = field.value := of_decide_eq_true (by simpa [decoded] using read)
    have bound := readNat_bound file field.offset field.width observed decoded
    unfold readNat at decoded
    rw [ite_eq_left bound] at decoded
    exact ⟨bound, (Except.ok.inj decoded).trans equal⟩

theorem checkLayout_sound {file : List Byte} {table : Table}
    (checked : checkLayout file table = true) : Layout file table := by
  simp only [checkLayout, Bool.and_eq_true] at checked
  refine ⟨of_decide_eq_true checked.1.1.1,
    checkFields_sound _ _ checked.1.1.2, ?_, checked.2⟩
  intro pair member
  have row := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked.1.2 pair member)
  exact ⟨checkFields_sound _ _ row.1, of_decide_eq_true row.2⟩

def Window.BoundsWith (window : Window) (maxBytes fileLength length : Nat) : Prop :=
  0 < length ∧ length ≤ maxBytes ∧ window.address + length ≤ 2^47 ∧
  window.offset + length ≤ fileLength

instance (window : Window) (maxBytes fileLength length : Nat) :
    Decidable (window.BoundsWith maxBytes fileLength length) := inferInstanceAs (Decidable (_ ∧ _))

/-- Compatibility bound: exactly the original 64-byte limit. -/
def Window.Bounds (window : Window) (fileLength length : Nat) : Prop :=
  window.BoundsWith 64 fileLength length

instance (window : Window) (fileLength length : Nat) :
    Decidable (window.Bounds fileLength length) := inferInstanceAs
      (Decidable (window.BoundsWith 64 fileLength length))

def Window.CoveredBy (window : Window) (length : Nat) (segment : Segment) : Prop :=
  segment.executable = true ∧ segment.virtualAddress ≤ window.address ∧
  window.address + length ≤ segment.virtualAddress + segment.fileSize ∧
  window.offset = segment.offset + (window.address - segment.virtualAddress)

instance (window : Window) (length : Nat) (segment : Segment) :
    Decidable (window.CoveredBy length segment) := inferInstanceAs (Decidable (_ ∧ _))

/-- Exact selected bytes and a complete, file-backed executable LOAD interval.
The descriptor conveys no function boundaries or symbol identity. -/
structure Selection (file : List Byte) (image : Image) (window : Window)
    (bytes : List Byte) (maxBytes : Nat := 64) : Prop where
  bounds : window.BoundsWith maxBytes file.length bytes.length
  covered : ∃ segment ∈ image.segments, window.CoveredBy bytes.length segment
  source : (file.drop window.offset).take bytes.length = bytes

-- Share one checker body while preserving the shallow public definition shape
-- used by literal-file proofs after `unfold check` or `unfold checkWith`.
local macro "checkWindow%(" maxBytes:term ", " file:term ", " table:term ", "
    window:term ", " bytes:term ")" : term =>
  `(checkLayout $file $table &&
    decide (Window.BoundsWith $window $maxBytes (List.length $file) (List.length $bytes)) &&
    (Table.image $table).segments.any
      (fun segment => decide (Window.CoveredBy $window (List.length $bytes) segment)) &&
    decide ((List.drop (Window.offset $window) $file).take (List.length $bytes) = $bytes) &&
    checkCode (toMemory (install $file (Table.image $table) empty)) (Window.base $window) $bytes)

/-- Explicit caller-selected admission bound, sharing the default checker body. -/
def checkWith (maxBytes : Nat) (file : List Byte) (table : Table) (window : Window)
    (bytes : List Byte) : Bool := checkWindow%(maxBytes, file, table, window, bytes)

theorem selection_soundWith {maxBytes : Nat} {file bytes : List Byte} {table : Table} {window : Window}
    (checked : checkWith maxBytes file table window bytes = true) :
    Layout file table ∧ Selection file table.image window bytes maxBytes := by
  simp only [checkWith, Bool.and_eq_true] at checked
  obtain ⟨segment, member, covers⟩ := List.any_eq_true.mp checked.1.1.2
  exact ⟨checkLayout_sound checked.1.1.1.1,
    ⟨of_decide_eq_true checked.1.1.1.2,
      ⟨segment, member, of_decide_eq_true covers⟩, of_decide_eq_true checked.1.2⟩⟩

theorem Selection.file_byteWith {maxBytes : Nat} {file bytes : List Byte} {image : Image} {window : Window}
    (selected : Selection file image window bytes maxBytes) {index : Nat} {byte : Byte}
    (present : bytes[index]? = some byte) : file[window.offset + index]? = some byte := by
  have inside := (List.getElem_of_getElem? present).1
  rw [← selected.source] at present
  simpa only [List.getElem?_take_of_lt inside, List.getElem?_drop] using present

private theorem ordered_disjoint {segments : List Segment}
    (ordered : segments.Pairwise Segment.pageOrdered) :
    ∀ left ∈ segments, ∀ right ∈ segments, left ≠ right → left.pageDisjoint right := by
  induction ordered with
  | nil => simp
  | @cons first rest before _ induction =>
    intro left leftIn right rightIn different
    simp only [List.mem_cons] at leftIn rightIn
    rcases leftIn with rfl | leftIn
    · rcases rightIn with rfl | rightIn
      · exact (different rfl).elim
      · exact Or.inl (before right rightIn)
    · rcases rightIn with rfl | rightIn
      · exact Or.inr (before left leftIn)
      · exact induction left leftIn right rightIn different

/-- Includes competing partial mappings and disjoint byte ranges sharing a page. -/
theorem Layout.no_competing_pages {file : List Byte} {table : Table}
    (layout : Layout file table) : ∀ left ∈ table.image.segments,
    ∀ right ∈ table.image.segments, left ≠ right → left.pageDisjoint right := by
  have validated := layout.loads
  simp only [valid, Bool.and_eq_true] at validated
  exact ordered_disjoint (of_decide_eq_true validated.1.2)

/-- The selected LOAD itself is validated, with no distinct competing page map. -/
theorem selected_segmentWith {maxBytes : Nat} {file bytes : List Byte} {table : Table} {window : Window}
    (checked : checkWith maxBytes file table window bytes = true) :
    ∃ segment ∈ table.image.segments, segment.valid file.length = true ∧
      window.CoveredBy bytes.length segment ∧
      ∀ other ∈ table.image.segments, segment ≠ other → segment.pageDisjoint other := by
  obtain ⟨layout, selected⟩ := selection_soundWith checked
  obtain ⟨segment, member, covered⟩ := selected.covered
  have validated := layout.loads
  simp only [valid, Bool.and_eq_true] at validated
  exact ⟨segment, member, List.all_eq_true.mp validated.1.1.2 segment member, covered,
    layout.no_competing_pages segment member⟩

/-- Reuses the existing byte-fetch checker and its prior-space independence
proof. This is a theorem about the exact abstract installation, before any
interpreter, relocation, runtime patching or concurrent modification. -/
theorem checked_codeWith {maxBytes : Nat} {file bytes : List Byte} {table : Table} {window : Window}
    (checked : checkWith maxBytes file table window bytes = true) (prior : Space) :
    CodeAt (toMemory (install file table.image prior)) window.base bytes := by
  have code := checkCode_sound _ _ _ (Bool.and_eq_true_iff.mp checked).2
  refine ⟨code.1, ?_⟩
  intro index byte present
  exact installed_fetch_independent file table.image prior _ byte (code.2 index byte present)

/-- Freshness is mandatory for admission, including hidden cells in page
padding. This does not call or extend the restricted legacy ELF parser. -/
-- Term templates preserve the shallow public definitions used by existing
-- explicit simplification clients, while keeping one admission implementation.
local macro "admitChecked%(" checked:term ", " file:term ", " table:term ", " prior:term ")" : term =>
  `(if $checked then
      if fresh (Table.image $table) $prior then
        .ok ⟨Table.image $table, install $file (Table.image $table) $prior⟩
      else .error .mappingCollision
    else .error .invalidImage)

def admitWith (maxBytes : Nat) (file : List Byte) (table : Table) (window : Window)
    (bytes : List Byte) (prior : Space) : Except Error Loaded :=
  admitChecked%(checkWith maxBytes file table window bytes, file, table, prior)

theorem admit_okWith {maxBytes : Nat} {file bytes : List Byte} {table : Table} {window : Window}
    {prior : Space} {loaded : Loaded} (success : admitWith maxBytes file table window bytes prior = .ok loaded) :
    checkWith maxBytes file table window bytes = true ∧ fresh table.image prior = true ∧
    loaded.image = table.image ∧ loaded.space = install file table.image prior := by
  by_cases checked : checkWith maxBytes file table window bytes = true
  · by_cases free : fresh table.image prior = true
    · simp [admitWith, checked, free] at success
      cases success
      exact ⟨checked, free, rfl, rfl⟩
    · simp [admitWith, checked, free] at success
  · simp [admitWith, checked] at success

/-- Generic LOAD admission bridge: literal syntax, selected source bytes,
executable CodeAt and preservation of every pre-existing caller cell. It
establishes neither physical ownership nor an ABI or OS startup contract. -/
theorem admitted_soundWith {maxBytes : Nat} {file bytes : List Byte} {table : Table} {window : Window}
    {prior : Space} {loaded : Loaded} (success : admitWith maxBytes file table window bytes prior = .ok loaded) :
    Layout file table ∧ Selection file loaded.image window bytes maxBytes ∧
    CodeAt (toMemory loaded.space) window.base bytes ∧
    ∀ address cell, prior.cells address = some cell → loaded.space.cells address = some cell := by
  obtain ⟨checked, free, image, space⟩ := admit_okWith success
  obtain ⟨layout, selected⟩ := selection_soundWith checked
  refine ⟨layout, image ▸ selected, ?_, ?_⟩
  · rw [space]
    exact checked_codeWith checked prior
  · rw [space]
    exact install_preserves_existing file table.image prior layout.loads free

/-- Explicit runtime environment condition. Current readable bytes and execute
permissions at the selected interval still equal the checked installation.
Discharging this requires OS/loader/ownership/synchronization reasoning. -/
def TextUnchanged (installed current : X86.Memory) (window : Window) (length : Nat) : Prop :=
  ∀ index, index < length →
    let address := window.base + BitVec.ofNat 64 index
    current.read address = installed.read address ∧
    current.executable address = installed.executable address

theorem admitted_current_codeWith {maxBytes : Nat} {file bytes : List Byte} {table : Table} {window : Window}
    {prior : Space} {loaded : Loaded} {current : X86.Memory}
    (success : admitWith maxBytes file table window bytes prior = .ok loaded)
    (unchanged : TextUnchanged (toMemory loaded.space) current window bytes.length) :
    CodeAt current window.base bytes := by
  have code := (admitted_soundWith success).2.2.1
  refine ⟨code.1, ?_⟩
  intro index byte present
  have same := unchanged index (List.getElem_of_getElem? present).1
  simpa only [fetchByte, same.1, same.2] using code.2 index byte present

/-- The legacy checker always keeps the original 64-byte admission bound. -/
def check (file : List Byte) (table : Table) (window : Window) (bytes : List Byte) : Bool :=
  checkWindow%(64, file, table, window, bytes)

theorem Selection.file_byte {file bytes : List Byte} {image : Image} {window : Window}
    (selected : Selection file image window bytes) {index : Nat} {byte : Byte}
    (present : bytes[index]? = some byte) : file[window.offset + index]? = some byte :=
  selected.file_byteWith present

theorem selection_sound {file bytes : List Byte} {table : Table} {window : Window}
    (checked : check file table window bytes = true) :
    Layout file table ∧ Selection file table.image window bytes := selection_soundWith checked

theorem selected_segment {file bytes : List Byte} {table : Table} {window : Window}
    (checked : check file table window bytes = true) :
    ∃ segment ∈ table.image.segments, segment.valid file.length = true ∧
      window.CoveredBy bytes.length segment ∧
      ∀ other ∈ table.image.segments, segment ≠ other → segment.pageDisjoint other :=
  selected_segmentWith checked

theorem checked_code {file bytes : List Byte} {table : Table} {window : Window}
    (checked : check file table window bytes = true) (prior : Space) :
    CodeAt (toMemory (install file table.image prior)) window.base bytes :=
  checked_codeWith checked prior

def admit (file : List Byte) (table : Table) (window : Window) (bytes : List Byte)
    (prior : Space) : Except Error Loaded :=
  admitChecked%(check file table window bytes, file, table, prior)

theorem admit_ok {file bytes : List Byte} {table : Table} {window : Window}
    {prior : Space} {loaded : Loaded} (success : admit file table window bytes prior = .ok loaded) :
    check file table window bytes = true ∧ fresh table.image prior = true ∧
    loaded.image = table.image ∧ loaded.space = install file table.image prior := admit_okWith success

theorem admitted_sound {file bytes : List Byte} {table : Table} {window : Window}
    {prior : Space} {loaded : Loaded} (success : admit file table window bytes prior = .ok loaded) :
    Layout file table ∧ Selection file loaded.image window bytes ∧
    CodeAt (toMemory loaded.space) window.base bytes ∧
    ∀ address cell, prior.cells address = some cell → loaded.space.cells address = some cell :=
  admitted_soundWith success

theorem admitted_current_code {file bytes : List Byte} {table : Table} {window : Window}
    {prior : Space} {loaded : Loaded} {current : X86.Memory}
    (success : admit file table window bytes prior = .ok loaded)
    (unchanged : TextUnchanged (toMemory loaded.space) current window bytes.length) :
    CodeAt current window.base bytes := admitted_current_codeWith success unchanged

end EDSL.ELF.FunctionWindow
