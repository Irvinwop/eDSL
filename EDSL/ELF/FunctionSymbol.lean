/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionWindow

namespace EDSL.ELF.FunctionSymbol
open X86 OS.AddressSpace
open FunctionWindow (Field Window)

/-- All ELF64 section-header fields. Witnesses are untrusted until checked
against their exact 64-byte rows in the literal complete file. -/
structure Section where
  name : Nat
  kind : Nat
  flags : Nat
  address : Nat
  offset : Nat
  size : Nat
  link : Nat
  info : Nat
  alignment : Nat
  entrySize : Nat
  deriving DecidableEq, Repr, Inhabited

def Section.fields (sh : Section) (base : Nat) : List Field := [
  ⟨base, 4, sh.name⟩, ⟨base + 4, 4, sh.kind⟩,
  ⟨base + 8, 8, sh.flags⟩, ⟨base + 16, 8, sh.address⟩,
  ⟨base + 24, 8, sh.offset⟩, ⟨base + 32, 8, sh.size⟩,
  ⟨base + 40, 4, sh.link⟩, ⟨base + 44, 4, sh.info⟩,
  ⟨base + 48, 8, sh.alignment⟩, ⟨base + 56, 8, sh.entrySize⟩]

/-- NOBITS has no file payload. Extended indexes and compressed metadata are
outside this profile; ordinary uninterpreted section payloads remain opaque. -/
def Section.Bounded (sh : Section) (fileLength : Nat) : Prop :=
  sh.offset ≤ fileLength ∧
  (sh.kind = 8 ∨ sh.offset + sh.size ≤ fileLength)

instance (sh : Section) (fileLength : Nat) :
    Decidable (sh.Bounded fileLength) := inferInstanceAs (Decidable (_ ∧ _))

def Section.isSymbols (sh : Section) : Bool := sh.kind == 2 || sh.kind == 11

/-- Every ELF64 symbol field, including binding/type, visibility and declared
extent. No semantic property of a program is inferred from these fields. -/
structure Symbol where
  nameOffset : Nat
  info : Nat
  other : Nat
  sh : Nat
  value : Nat
  size : Nat
  deriving DecidableEq, Repr, Inhabited

def Symbol.fields (symbol : Symbol) (base : Nat) : List Field := [
  ⟨base, 4, symbol.nameOffset⟩, ⟨base + 4, 1, symbol.info⟩,
  ⟨base + 5, 1, symbol.other⟩, ⟨base + 6, 2, symbol.sh⟩,
  ⟨base + 8, 8, symbol.value⟩, ⟨base + 16, 8, symbol.size⟩]

/-- Byte names avoid an implicit Unicode or lossy host-string conversion. ELF
permits suffix references: the first terminating NUL at the offset is used. -/
def nameAt (strings : List Byte) (offset : Nat) : List Byte :=
  (strings.drop offset).takeWhile (· != 0)

def Terminated (strings : List Byte) (offset : Nat) : Prop :=
  offset < strings.length ∧ strings[offset + (nameAt strings offset).length]? = some 0

instance (strings : List Byte) (offset : Nat) : Decidable (Terminated strings offset) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Strings where
  sectionIndex : Nat
  sh : Section
  bytes : List Byte
  deriving DecidableEq, Repr

/-- A complete linked STRTAB, including leading and trailing NUL. -/
def Strings.Shape (strings : Strings) (sections : List Section) : Prop :=
  sections[strings.sectionIndex]? = some strings.sh ∧
  strings.sectionIndex > 0 ∧ strings.sh.kind = 3 ∧
  (strings.sh.flags = 0 ∨ strings.sh.flags = 2) ∧
  strings.sh.entrySize = 0 ∧ strings.sh.link = 0 ∧ strings.sh.info = 0 ∧
  strings.sh.size = strings.bytes.length ∧
  strings.bytes.head? = some 0 ∧ strings.bytes.getLast? = some 0

instance (strings : Strings) (sections : List Section) :
    Decidable (strings.Shape sections) := inferInstanceAs (Decidable (_ ∧ _))

structure Symbols where
  sectionIndex : Nat
  sh : Section
  rows : List Symbol
  strings : Strings
  deriving DecidableEq, Repr

/-- Complete ordinary ELF64 tables only: one NULL row, exact entry count,
linked strings and the local/nonlocal partition recorded by sh_info. -/
def Symbols.Shape (symbols : Symbols) (sections : List Section) : Prop :=
  sections[symbols.sectionIndex]? = some symbols.sh ∧
  symbols.sectionIndex > 0 ∧ symbols.sh.isSymbols = true ∧
  (symbols.sh.flags = 0 ∨ symbols.sh.flags = 2) ∧
  symbols.sh.entrySize = 24 ∧ symbols.sh.size = symbols.rows.length * 24 ∧
  0 < symbols.sh.info ∧ symbols.sh.info ≤ symbols.rows.length ∧
  symbols.sh.link = symbols.strings.sectionIndex ∧ symbols.strings.Shape sections ∧
  symbols.rows.head? = some default ∧
  ∀ pair ∈ symbols.rows.zipIdx,
    Terminated symbols.strings.bytes pair.1.nameOffset ∧ pair.1.other < 4 ∧
    (pair.1.sh < sections.length ∨ pair.1.sh = 0xfff1 ∨ pair.1.sh = 0xfff2) ∧
    (if pair.2 < symbols.sh.info then pair.1.info / 16 = 0 else pair.1.info / 16 ≠ 0)

instance (symbols : Symbols) (sections : List Section) :
    Decidable (symbols.Shape sections) := inferInstanceAs (Decidable (_ ∧ _))

structure Metadata where
  sections : List Section
  names : Strings
  tables : List Symbols
  deriving DecidableEq, Repr

/-- Exact coverage of all static and dynamic symbol tables. Repeated static or
repeated dynamic tables are rejected; a requested duplicate in either table is
also rejected below. No table can be silently omitted by a witness producer. -/
def Metadata.Shape (metadata : Metadata) (header : FunctionWindow.Header) : Prop :=
  metadata.sections.length = header.sectionCount ∧
  metadata.sections.head? = some default ∧
  metadata.names.sectionIndex = header.sectionNames ∧ metadata.names.Shape metadata.sections ∧
  (metadata.sections.filter (fun sh => sh.kind == 2)).length = 1 ∧
  (metadata.sections.filter (fun sh => sh.kind == 11)).length ≤ 1 ∧
  metadata.tables.map (·.sectionIndex) =
    ((metadata.sections.zipIdx.filter fun pair => pair.1.isSymbols).map (·.2)) ∧
  (∀ sh ∈ metadata.sections, Terminated metadata.names.bytes sh.name)

instance (metadata : Metadata) (header : FunctionWindow.Header) :
    Decidable (metadata.Shape header) := inferInstanceAs (Decidable (_ ∧ _))

private def checkFields (file : List Byte) (fields : List Field) : Bool :=
  fields.all fun field =>
    match readNat file field.offset field.width with
    | .ok observed => decide (observed = field.value)
    | .error _ => false

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

private def relocate (base : Nat) (field : Field) : Field :=
  ⟨base + field.offset, field.width, field.value⟩

private theorem holds_relocate {file : List Byte} {base : Nat} {field : Field}
    (bounded : base ≤ file.length) (held : field.Holds (file.drop base)) :
    (relocate base field).Holds file := by
  obtain ⟨inside, equal⟩ := held
  refine ⟨?_, ?_⟩
  · simp only [List.length_drop] at inside
    dsimp [relocate]
    omega
  · simpa only [relocate, List.drop_drop, Nat.add_comm] using equal

/-- Drop the file prefix once for a whole table. Per-row offsets are relative
to this shared slice; the soundness proof restores absolute file locations. -/
private def checkTableFields (file : List Byte) (base : Nat)
    (rows : List (List Field)) : Bool :=
  decide (base ≤ file.length) &&
  let source := file.drop base
  rows.all fun fields => checkFields source fields

private theorem checkTableFields_sound {file : List Byte} {base : Nat}
    {rows : List (List Field)} (checked : checkTableFields file base rows = true) :
    ∀ fields ∈ rows, ∀ field ∈ fields, (relocate base field).Holds file := by
  obtain ⟨bounded, rowsChecked⟩ := Bool.and_eq_true_iff.mp checked
  intro fields member field present
  exact holds_relocate (of_decide_eq_true bounded)
    (checkFields_sound _ _ (List.all_eq_true.mp rowsChecked fields member) field present)

private theorem Section.fields_relocate (sh : Section) (base offset : Nat) :
    sh.fields (base + offset) = (sh.fields offset).map (relocate base) := by
  simp [Section.fields, relocate, Nat.add_assoc]

private theorem Symbol.fields_relocate (symbol : Symbol) (base offset : Nat) :
    symbol.fields (base + offset) = (symbol.fields offset).map (relocate base) := by
  simp [Symbol.fields, relocate, Nat.add_assoc]

/-- All section rows and every row/string byte of every symbol table agree
with the literal file. This is separate from the existing program-header
layout contract supplied by FunctionWindow. -/
structure CheckedMetadata (file : List Byte) (header : FunctionWindow.Header)
    (metadata : Metadata) : Prop where
  shape : metadata.Shape header
  sections : ∀ pair ∈ metadata.sections.zipIdx,
    pair.1.Bounded file.length ∧
    ∀ field ∈ pair.1.fields (header.sectionOffset + pair.2 * 64), field.Holds file
  names : (file.drop metadata.names.sh.offset).take metadata.names.bytes.length =
    metadata.names.bytes
  tables : ∀ symbols ∈ metadata.tables, symbols.Shape metadata.sections ∧
    (file.drop symbols.strings.sh.offset).take symbols.strings.bytes.length =
      symbols.strings.bytes ∧
    ∀ pair ∈ symbols.rows.zipIdx,
      ∀ field ∈ pair.1.fields (symbols.sh.offset + pair.2 * 24), field.Holds file

def checkMetadata (file : List Byte) (header : FunctionWindow.Header)
    (metadata : Metadata) : Bool :=
  decide (metadata.Shape header) &&
  metadata.sections.zipIdx.all (fun pair => decide (pair.1.Bounded file.length)) &&
  checkTableFields file header.sectionOffset
    (metadata.sections.zipIdx.map fun pair => pair.1.fields (pair.2 * 64)) &&
  decide ((file.drop metadata.names.sh.offset).take metadata.names.bytes.length =
    metadata.names.bytes) &&
  metadata.tables.all (fun symbols =>
    decide (symbols.Shape metadata.sections) &&
    decide ((file.drop symbols.strings.sh.offset).take symbols.strings.bytes.length =
      symbols.strings.bytes) &&
    checkTableFields file symbols.sh.offset
      (symbols.rows.zipIdx.map fun pair => pair.1.fields (pair.2 * 24)))

theorem checkMetadata_sound {file : List Byte} {header : FunctionWindow.Header}
    {metadata : Metadata} (checked : checkMetadata file header metadata = true) :
    CheckedMetadata file header metadata := by
  simp only [checkMetadata, Bool.and_eq_true] at checked
  refine ⟨of_decide_eq_true checked.1.1.1.1, ?_, of_decide_eq_true checked.1.2, ?_⟩
  · intro pair member
    refine ⟨of_decide_eq_true (List.all_eq_true.mp checked.1.1.1.2 pair member), ?_⟩
    rw [Section.fields_relocate]
    intro field present
    obtain ⟨relative, relativeIn, rfl⟩ := List.mem_map.mp present
    exact checkTableFields_sound checked.1.1.2 (pair.1.fields (pair.2 * 64))
      (List.mem_map.mpr ⟨pair, member, rfl⟩) relative relativeIn
  · intro symbols member
    have row := List.all_eq_true.mp checked.2 symbols member
    simp only [Bool.and_eq_true] at row
    refine ⟨of_decide_eq_true row.1.1, of_decide_eq_true row.1.2, ?_⟩
    intro pair present
    rw [Symbol.fields_relocate]
    intro field fieldIn
    obtain ⟨relative, relativeIn, rfl⟩ := List.mem_map.mp fieldIn
    exact checkTableFields_sound row.2 (pair.1.fields (pair.2 * 24))
      (List.mem_map.mpr ⟨pair, present, rfl⟩) relative relativeIn

structure Occurrence where
  table : Nat
  index : Nat
  symbol : Symbol
  deriving DecidableEq, Repr

def Metadata.matches (metadata : Metadata) (name : List Byte) : List Occurrence :=
  metadata.tables.flatMap fun symbols =>
    (symbols.rows.zipIdx.filter fun pair => nameAt symbols.strings.bytes pair.1.nameOffset == name).map
      fun pair => ⟨symbols.sectionIndex, pair.2, pair.1⟩

/-- Every match comes from an actual row in a completely checked table; an
occurrence descriptor cannot invent its table, row index or byte name. -/
theorem Metadata.named_of_mem {metadata : Metadata} {name : List Byte}
    {occurrence : Occurrence} (present : occurrence ∈ metadata.matches name) :
    ∃ symbols ∈ metadata.tables,
      occurrence.table = symbols.sectionIndex ∧
      (occurrence.symbol, occurrence.index) ∈ symbols.rows.zipIdx ∧
      nameAt symbols.strings.bytes occurrence.symbol.nameOffset = name := by
  obtain ⟨symbols, member, present⟩ := List.mem_flatMap.mp present
  obtain ⟨pair, filtered, rfl⟩ := List.mem_map.mp present
  refine ⟨symbols, member, rfl, (List.mem_filter.mp filtered).1, ?_⟩
  simpa using (List.mem_filter.mp filtered).2

/-- Only a selected occurrence and its defining section are untrusted hints.
The whole declared extent, rather than an arbitrary prefix, is selected. -/
structure Function where
  occurrence : Occurrence
  sh : Section
  window : Window
  deriving DecidableEq, Repr

/-- Uniqueness is stricter than uniqueness of global defined functions: any
other symbol bearing the requested byte name, even undefined or local, rejects
the selection. In particular a second dynamic-table alias is not ignored. -/
def Function.Contract (function : Function) (metadata : Metadata)
    (name : List Byte) (length : Nat) : Prop :=
  name ≠ [] ∧ (∀ byte ∈ name, byte ≠ 0) ∧
  metadata.matches name = [function.occurrence] ∧
  function.occurrence.symbol.info = 0x12 ∧ function.occurrence.symbol.other < 4 ∧
  0 < function.occurrence.symbol.sh ∧
  metadata.sections[function.occurrence.symbol.sh]? = some function.sh ∧
  function.sh.kind = 1 ∧ function.sh.flags = 6 ∧
  function.sh.address ≤ function.occurrence.symbol.value ∧
  function.occurrence.symbol.value + function.occurrence.symbol.size ≤
    function.sh.address + function.sh.size ∧
  function.window.address = function.occurrence.symbol.value ∧
  function.window.offset = function.sh.offset +
    (function.occurrence.symbol.value - function.sh.address) ∧
  function.occurrence.symbol.size = length

instance (function : Function) (metadata : Metadata) (name : List Byte) (length : Nat) :
    Decidable (function.Contract metadata name length) := inferInstanceAs (Decidable (_ ∧ _))

/-- No external symbol extractor is an authority: every supplied field,
string, row count, table link and window is checked against the literal file. -/
def check (file : List Byte) (table : FunctionWindow.Table) (metadata : Metadata)
    (name : List Byte) (function : Function) (bytes : List Byte) : Bool :=
  checkMetadata file table.header metadata &&
  decide (function.Contract metadata name bytes.length) &&
  FunctionWindow.check file table function.window bytes

theorem checked_sound {file bytes name : List Byte} {table : FunctionWindow.Table}
    {metadata : Metadata} {function : Function}
    (checked : check file table metadata name function bytes = true) :
    CheckedMetadata file table.header metadata ∧
    function.Contract metadata name bytes.length ∧
    FunctionWindow.Layout file table ∧
    FunctionWindow.Selection file table.image function.window bytes := by
  simp only [check, Bool.and_eq_true] at checked
  exact ⟨checkMetadata_sound checked.1.1, of_decide_eq_true checked.1.2,
    FunctionWindow.selection_sound checked.2⟩

/-- Literal symbol-row and complete linked-string evidence for the selected
unique name. Exact section-header rows and the full tables are additionally
available from checked_sound; no host extraction result appears as a premise. -/
theorem checked_symbol {file bytes name : List Byte} {table : FunctionWindow.Table}
    {metadata : Metadata} {function : Function}
    (checked : check file table metadata name function bytes = true) :
    ∃ symbols ∈ metadata.tables,
      function.occurrence.table = symbols.sectionIndex ∧
      (function.occurrence.symbol, function.occurrence.index) ∈ symbols.rows.zipIdx ∧
      symbols.Shape metadata.sections ∧
      (∀ field ∈ function.occurrence.symbol.fields
        (symbols.sh.offset + function.occurrence.index * 24), field.Holds file) ∧
      (file.drop symbols.strings.sh.offset).take symbols.strings.bytes.length =
        symbols.strings.bytes ∧
      nameAt symbols.strings.bytes function.occurrence.symbol.nameOffset = name ∧
      Terminated symbols.strings.bytes function.occurrence.symbol.nameOffset := by
  obtain ⟨metadataChecked, contract, _, _⟩ := checked_sound checked
  have present : function.occurrence ∈ metadata.matches name := by
    rw [contract.2.2.1]
    exact List.mem_singleton_self _
  obtain ⟨symbols, member, tableIndex, row, named⟩ := Metadata.named_of_mem present
  obtain ⟨shape, strings, rows⟩ := metadataChecked.tables symbols member
  refine ⟨symbols, member, tableIndex, row, shape, ?_, strings, named, ?_⟩
  · exact rows (function.occurrence.symbol, function.occurrence.index) row
  rcases shape with ⟨_, _, _, _, _, _, _, _, _, _, _, validRows⟩
  exact (validRows (function.occurrence.symbol, function.occurrence.index) row).1

/-- The selected declared symbol extent maps to the same file interval through
both its executable PROGBITS section and an executable validated LOAD. -/
theorem checked_mapping {file bytes name : List Byte} {table : FunctionWindow.Table}
    {metadata : Metadata} {function : Function}
    (checked : check file table metadata name function bytes = true) :
    function.window.address = function.occurrence.symbol.value ∧
    function.occurrence.symbol.size = bytes.length ∧
    function.sh.kind = 1 ∧ function.sh.flags = 6 ∧
    function.window.offset = function.sh.offset +
      (function.occurrence.symbol.value - function.sh.address) ∧
    ∃ segment ∈ table.image.segments,
      function.window.CoveredBy bytes.length segment := by
  obtain ⟨_, contract, _, selected⟩ := checked_sound checked
  rcases contract with ⟨_, _, _, _, _, _, _, kind, flags, _, _, address, offset, size⟩
  exact ⟨address, size, kind, flags, offset, selected.covered⟩

/-- Admission keeps FunctionWindow's freshness/page-collision requirements.
It does not execute an interpreter, apply relocations or establish an ABI. -/
def admit (file : List Byte) (table : FunctionWindow.Table) (metadata : Metadata)
    (name : List Byte) (function : Function) (bytes : List Byte) (prior : Space) : Except Error Loaded :=
  if check file table metadata name function bytes then
    FunctionWindow.admit file table function.window bytes prior
  else .error .invalidImage

theorem admit_ok {file bytes name : List Byte} {table : FunctionWindow.Table}
    {metadata : Metadata} {function : Function} {prior : Space} {loaded : Loaded}
    (success : admit file table metadata name function bytes prior = .ok loaded) :
    check file table metadata name function bytes = true ∧
    FunctionWindow.admit file table function.window bytes prior = .ok loaded := by
  by_cases checked : check file table metadata name function bytes = true
  · exact ⟨checked, by simpa [admit, checked] using success⟩
  · simp [admit, checked] at success

theorem admitted_sound {file bytes name : List Byte} {table : FunctionWindow.Table}
    {metadata : Metadata} {function : Function} {prior : Space} {loaded : Loaded}
    (success : admit file table metadata name function bytes prior = .ok loaded) :
    CheckedMetadata file table.header metadata ∧
    function.Contract metadata name bytes.length ∧
    FunctionWindow.Layout file table ∧
    FunctionWindow.Selection file loaded.image function.window bytes ∧
    CodeAt (toMemory loaded.space) function.window.base bytes ∧
    ∀ address cell, prior.cells address = some cell → loaded.space.cells address = some cell := by
  obtain ⟨checked, admitted⟩ := admit_ok success
  obtain ⟨metadata, contract, _, _⟩ := checked_sound checked
  exact ⟨metadata, contract, FunctionWindow.admitted_sound admitted⟩

/-- Current-code use still requires explicit post-installation text and
execute-permission preservation. Symbol metadata discharges neither of them. -/
theorem admitted_current_code {file bytes name : List Byte} {table : FunctionWindow.Table}
    {metadata : Metadata} {function : Function} {prior : Space} {loaded : Loaded}
    {current : X86.Memory}
    (success : admit file table metadata name function bytes prior = .ok loaded)
    (unchanged : FunctionWindow.TextUnchanged (toMemory loaded.space) current
      function.window bytes.length) : CodeAt current function.window.base bytes :=
  FunctionWindow.admitted_current_code (admit_ok success).2 unchanged

end EDSL.ELF.FunctionSymbol
