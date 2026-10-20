/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionSymbol
import EDSL.Audit

namespace EDSL.Tests.ELFFunctionSymbol
open X86 OS.AddressSpace EDSL.ELF

-- The encoders below know only ELF64LE's byte layout, not the production
-- Field lists, witnesses, readers or checkers. Witnesses are written separately.
def le (width value : Nat) : List Byte :=
  (List.range width).map fun index => BitVec.ofNat 8 (value / 256 ^ index)

def sectionRow (name kind flags address offset size link info alignment entrySize : Nat) :
    List Byte :=
  le 4 name ++ le 4 kind ++ le 8 flags ++ le 8 address ++ le 8 offset ++
  le 8 size ++ le 4 link ++ le 4 info ++ le 8 alignment ++ le 8 entrySize

def symbolRow (name info other sh value size : Nat) : List Byte :=
  le 4 name ++ le 1 info ++ le 1 other ++ le 2 sh ++ le 8 value ++ le 8 size

def overwrite (file : List Byte) (offset : Nat) (bytes : List Byte) : List Byte :=
  file.take offset ++ bytes ++ file.drop (offset + bytes.length)

def putLE (file : List Byte) (offset width value : Nat) : List Byte :=
  overwrite file offset (le width value)

-- mov eax, 42; ret. These tests establish byte selection/transport, not a
-- semantic property inferred from the symbol's name or an OS startup contract.
def code : List Byte := [0xb8, 0x2a, 0, 0, 0, 0xc3]
def requested : List Byte := [0x74, 0x61, 0x72, 0x67, 0x65, 0x74] -- target
def stringBytes : List Byte :=
  [0, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74, 0,
      0x68, 0x65, 0x6c, 0x70, 0x65, 0x72, 0] -- target, helper
def sectionNames : List Byte :=
  [0, 0x2e, 0x74, 0x65, 0x78, 0x74, 0,
      0x2e, 0x73, 0x79, 0x6d, 0x74, 0x61, 0x62, 0,
      0x2e, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0,
      0x2e, 0x73, 0x68, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0,
      0x2e, 0x64, 0x79, 0x6e, 0x73, 0x79, 0x6d, 0]

-- ELF header (64), one program header (56), text at 0x80, STRTAB at
-- 0x88, three exact 24-byte symbol rows at 0xa0, SHSTRTAB at 0xf0,
-- and five exact 64-byte section rows at 0x180. The RX LOAD has equal
-- file/VA offsets within a 4096-byte page, with a file-backed entry.
def file : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  le 2 2 ++ le 2 62 ++ le 4 1 ++ le 8 0x400080 ++ le 8 64 ++ le 8 0x180 ++
  le 4 0 ++ le 2 64 ++ le 2 56 ++ le 2 1 ++ le 2 64 ++ le 2 5 ++ le 2 4 ++
  le 4 1 ++ le 4 5 ++ le 8 0x80 ++ le 8 0x400080 ++ le 8 0x400080 ++
  le 8 6 ++ le 8 6 ++ le 8 4096 ++
  List.replicate 8 0 ++ code ++ List.replicate 2 0 ++ stringBytes ++
  List.replicate 9 0 ++
  symbolRow 0 0 0 0 0 0 ++
  symbolRow 1 0x12 0 1 0x400080 6 ++
  symbolRow 8 0x12 0 1 0x400085 1 ++
  List.replicate 8 0 ++ sectionNames ++ List.replicate 103 0 ++
  sectionRow 0 0 0 0 0 0 0 0 0 0 ++
  sectionRow 1 1 6 0x400080 0x80 6 0 0 16 0 ++
  sectionRow 7 2 0 0 0xa0 72 3 1 8 24 ++
  sectionRow 15 3 0 0 0x88 15 0 0 1 0 ++
  sectionRow 23 3 0 0 0xf0 41 0 0 1 0

def table : FunctionWindow.Table :=
  ⟨⟨0, 0x400080, 64, 0x180, 5, 4⟩,
    [⟨1, 0x400080, ⟨0x80, 0x400080, 6, 6, 5, 4096⟩⟩]⟩
def text : FunctionSymbol.Section := ⟨1, 1, 6, 0x400080, 0x80, 6, 0, 0, 16, 0⟩
def symtab : FunctionSymbol.Section := ⟨7, 2, 0, 0, 0xa0, 72, 3, 1, 8, 24⟩
def strtab : FunctionSymbol.Section := ⟨15, 3, 0, 0, 0x88, 15, 0, 0, 1, 0⟩
def shstrtab : FunctionSymbol.Section := ⟨23, 3, 0, 0, 0xf0, 41, 0, 0, 1, 0⟩
def target : FunctionSymbol.Symbol := ⟨1, 0x12, 0, 1, 0x400080, 6⟩
def helper : FunctionSymbol.Symbol := ⟨8, 0x12, 0, 1, 0x400085, 1⟩
def symbols : FunctionSymbol.Symbols :=
  ⟨2, symtab, [default, target, helper], ⟨3, strtab, stringBytes⟩⟩
def metadata : FunctionSymbol.Metadata :=
  ⟨[default, text, symtab, strtab, shstrtab], ⟨4, shstrtab, sectionNames⟩, [symbols]⟩
def selected : FunctionSymbol.Function := ⟨⟨2, 1, target⟩, text, ⟨0x400080, 0x80⟩⟩

structure Fixture where
  file : List Byte
  table : FunctionWindow.Table
  metadata : FunctionSymbol.Metadata
  selected : FunctionSymbol.Function
  name : List Byte := requested
  bytes : List Byte := code

def base : Fixture := ⟨file, table, metadata, selected, requested, code⟩
def Fixture.check (fixture : Fixture) : Bool :=
  FunctionSymbol.check fixture.file fixture.table fixture.metadata fixture.name fixture.selected fixture.bytes
def Fixture.metadataOK (fixture : Fixture) : Bool :=
  FunctionSymbol.checkMetadata fixture.file fixture.table.header fixture.metadata
def Fixture.windowOK (fixture : Fixture) : Bool :=
  FunctionWindow.check fixture.file fixture.table fixture.selected.window fixture.bytes
def Fixture.contractOK (fixture : Fixture) : Bool :=
  decide (fixture.selected.Contract fixture.metadata fixture.name fixture.bytes.length)

-- Witness updates never encode file contents. Mutations supply independently
-- encoded rows at ELF-defined byte offsets alongside their witness changes.
def staticWitness (sh : FunctionSymbol.Section) (rows : List FunctionSymbol.Symbol) : FunctionSymbol.Metadata :=
  { metadata with
    sections := [default, text, sh, strtab, shstrtab]
    tables := [{ symbols with sh := sh, rows := rows }] }

def targetCase (literal : List Byte) (symbol : FunctionSymbol.Symbol) : Fixture :=
  { base with
    file := overwrite file 0xb8 literal
    metadata := staticWitness symtab [default, symbol, helper]
    selected := { selected with occurrence := ⟨2, 1, symbol⟩ } }

def textCase (literal : List Byte) (sh : FunctionSymbol.Section) : Fixture :=
  { base with
    file := overwrite file 0x1c0 literal
    metadata := { metadata with sections := [default, sh, symtab, strtab, shstrtab] }
    selected := { selected with sh := sh } }

theorem accepted : FunctionSymbol.check file table metadata requested selected code = true := by decide +kernel

theorem windowAccepted : FunctionWindow.check file table selected.window code = true :=
  (Bool.and_eq_true_iff.mp accepted).2

-- Avoid enumerating a page or raising any elaboration/kernel budgets.
theorem freshEmpty (image : EDSL.ELF.Image) : EDSL.ELF.fresh image empty = true := by
  unfold EDSL.ELF.fresh
  apply List.all_eq_true.mpr
  intro segment _
  unfold allUnmapped
  apply List.all_eq_true.mpr
  intro address _
  rfl

def installed : EDSL.ELF.Loaded := ⟨table.image, EDSL.ELF.install file table.image empty⟩

theorem admitted : FunctionSymbol.admit file table metadata requested selected code empty = .ok installed := by
  simp [FunctionSymbol.admit, accepted, FunctionWindow.admit, windowAccepted, freshEmpty, installed]

theorem installedCode : CodeAt (toMemory installed.space) selected.window.base code :=
  (FunctionSymbol.admitted_sound admitted).2.2.2.2.1

-- Exercise the current-memory transport with its explicit byte/permission
-- preservation premise; metadata by itself cannot discharge that premise.
theorem currentCode (current : X86.Memory)
    (unchanged : FunctionWindow.TextUnchanged (toMemory installed.space) current selected.window code.length) :
    CodeAt current selected.window.base code :=
  FunctionSymbol.admitted_current_code admitted unchanged

def observe (result : Except EDSL.ELF.Error EDSL.ELF.Loaded) :
    Option (Option Byte × Option Byte × Bool × Bool) := do
  let loaded ← result.toOption
  let memory := toMemory loaded.space
  return (memory.read 0x400080, memory.read 0x400085,
    memory.executable 0x400080, memory.writable 0x400080)

example : observe (FunctionSymbol.admit file table metadata requested selected code empty) =
    some (some 0xb8, some 0xc3, true, false) := by
  rw [admitted]
  decide +kernel

-- A hidden cell outside the six text bytes, but inside their rounded page,
-- must prevent admission. Its inaccessible permission must not hide it.
def collision : Space :=
  ⟨fun address => if address = 0x400000 then some ⟨0xa5, inaccessible⟩ else none⟩

theorem collisionRejected :
    FunctionSymbol.admit file table metadata requested selected code collision = .error .mappingCollision := by
  have occupied : EDSL.ELF.fresh table.image collision ≠ true := by
    intro free
    have unmapped := List.all_eq_true.mp free
      (⟨0x80, 0x400080, 6, 6, 5, 4096⟩ : EDSL.ELF.Segment) (by decide +kernel)
    have absent := allUnmapped_inside collision _ unmapped 0x400000 (by decide +kernel)
    simp [collision] at absent
  simp [FunctionSymbol.admit, accepted, FunctionWindow.admit, windowAccepted, occupied]

-- Duplicate requested names count even when the competing row is not a
-- defined global function. Metadata is accepted first to isolate uniqueness.
def duplicateGlobal : Fixture :=
  { base with
    file := overwrite file 0xd0 (symbolRow 1 0x12 0 1 0x400085 1)
    metadata := staticWitness symtab [default, target, { helper with nameOffset := 1 }] }
example : duplicateGlobal.metadataOK = true := by decide +kernel
example : duplicateGlobal.check = false := by decide +kernel

def duplicateUndefined : Fixture :=
  { base with
    file := overwrite file 0xd0 (symbolRow 1 0x10 0 0 0 0)
    metadata := staticWitness symtab [default, target, ⟨1, 0x10, 0, 0, 0, 0⟩] }
example : duplicateUndefined.metadataOK = true := by decide +kernel
example : duplicateUndefined.check = false := by decide +kernel

-- Put the local alias before the global target and advance sh_info to 2;
-- merely changing the binding would otherwise fail the partition guard.
def duplicateLocal : Fixture :=
  { base with
    file := overwrite (putLE file 0x22c 4 2) 0xb8
      (symbolRow 1 2 0 1 0x400085 1 ++ symbolRow 1 0x12 0 1 0x400080 6)
    metadata := staticWitness { symtab with info := 2 }
      [default, ⟨1, 2, 0, 1, 0x400085, 1⟩, target]
    selected := { selected with occurrence := ⟨2, 2, target⟩ } }
example : duplicateLocal.metadataOK = true := by decide +kernel
example : duplicateLocal.check = false := by decide +kernel

example : ({ base with name := [] } : Fixture).check = false := by decide +kernel
example : ({ base with name := [0x74, 0, 0x61] } : Fixture).check = false := by decide +kernel
example : ({ base with name := [0x61, 0x62, 0x73, 0x65, 0x6e, 0x74] } : Fixture).check = false :=
  by decide +kernel

-- ELF string offsets may point to a suffix, rather than only to string starts.
def suffixName : Fixture :=
  { targetCase (symbolRow 2 0x12 0 1 0x400080 6) { target with nameOffset := 2 } with
    name := [0x61, 0x72, 0x67, 0x65, 0x74] }
example : suffixName.check = true := by decide +kernel

-- Invalid names in an unrelated row cannot be ignored when selecting target.
def badNameOffset : Fixture :=
  { base with
    file := putLE file 0xd0 4 15
    metadata := staticWitness symtab [default, target, { helper with nameOffset := 15 }] }
example : badNameOffset.contractOK = true := by decide +kernel
example : badNameOffset.check = false := by decide +kernel

def missingTerminator : Fixture :=
  { base with
    file := putLE file 0x96 1 0x72
    metadata := { metadata with tables :=
      [{ symbols with strings := { symbols.strings with bytes := stringBytes.set 14 0x72 } }] } }
example : missingTerminator.contractOK = true := by decide +kernel
example : missingTerminator.check = false := by decide +kernel

def badSectionName : Fixture :=
  textCase (sectionRow 41 1 6 0x400080 0x80 6 0 0 16 0) { text with name := 41 }
example : badSectionName.contractOK = true := by decide +kernel
example : badSectionName.check = false := by decide +kernel

def missingSectionTerminator : Fixture :=
  { base with
    file := putLE file 0x118 1 0x6d
    metadata := { metadata with names := { metadata.names with bytes := sectionNames.set 40 0x6d } } }
example : missingSectionTerminator.check = false := by decide +kernel

-- A complete witness must agree with the actual string and symbol bytes.
example : ({ base with file := putLE file 0x89 1 0x54 } : Fixture).check = false := by decide +kernel
example : ({ base with file := putLE file 0xf1 1 0x58 } : Fixture).check = false := by decide +kernel
example : ({ base with file := putLE file 0xc0 8 0x400081 } : Fixture).check = false := by decide +kernel
example : ({ base with file := putLE file 0x1c8 8 2 } : Fixture).check = false := by decide +kernel

-- Completeness/shape errors: the file and relevant witness are changed
-- together except where an intentionally omitted row is the defect tested.
def missingSectionRow : Fixture :=
  { base with
    file := putLE (file ++ List.replicate 64 0) 60 2 6
    table := { table with header := { table.header with sectionCount := 6 } } }
example : FunctionWindow.checkLayout missingSectionRow.file missingSectionRow.table = true := by decide +kernel
example : missingSectionRow.check = false := by decide +kernel

example : ({ base with file := putLE file 58 2 63 } : Fixture).metadataOK = true := by decide +kernel
example : ({ base with file := putLE file 58 2 63 } : Fixture).check = false := by decide +kernel

def missingSymbolRow : Fixture :=
  { base with metadata := staticWitness symtab [default, target] }
example : missingSymbolRow.contractOK = true := by decide +kernel
example : missingSymbolRow.check = false := by decide +kernel

def partialSymbolRow : Fixture :=
  { base with
    file := putLE file 0x220 8 73
    metadata := staticWitness { symtab with size := 73 } [default, target, helper] }
example : partialSymbolRow.check = false := by decide +kernel

def wrongSymbolEntrySize : Fixture :=
  { base with
    file := putLE file 0x238 8 16
    metadata := staticWitness { symtab with entrySize := 16 } [default, target, helper] }
example : wrongSymbolEntrySize.check = false := by decide +kernel

def wrongLink : Fixture :=
  { base with
    file := putLE file 0x228 4 1
    metadata := staticWitness { symtab with link := 1 } [default, target, helper] }
example : wrongLink.contractOK = true := by decide +kernel
example : wrongLink.check = false := by decide +kernel

def wrongPartition : Fixture :=
  { base with
    file := putLE file 0x22c 4 2
    metadata := staticWitness { symtab with info := 2 } [default, target, helper] }
example : wrongPartition.check = false := by decide +kernel

def badNullSymbol : Fixture :=
  { base with
    file := putLE file 0xa4 1 1
    metadata := staticWitness symtab [⟨0, 1, 0, 0, 0, 0⟩, target, helper] }
example : badNullSymbol.check = false := by decide +kernel

def wrongStringEntrySize : Fixture :=
  { base with
    file := putLE file 0x278 8 1
    metadata := { metadata with
      sections := [default, text, symtab, { strtab with entrySize := 1 }, shstrtab]
      tables := [{ symbols with strings :=
        { symbols.strings with sh := { strtab with entrySize := 1 } } }] } }
example : wrongStringEntrySize.check = false := by decide +kernel

def wrongStringKind : Fixture :=
  { base with
    file := putLE file 0x244 4 1
    metadata := { metadata with
      sections := [default, text, symtab, { strtab with kind := 1 }, shstrtab]
      tables := [{ symbols with strings :=
        { symbols.strings with sh := { strtab with kind := 1 } } }] } }
example : wrongStringKind.check = false := by decide +kernel

-- An ordinary dynamic table is permitted, but every row must be covered and
-- aliases across static/dynamic tables remain ambiguous. The dynamic row is
-- initially an unrelated undefined global, so its presence alone must pass.
def dynsym : FunctionSymbol.Section := ⟨33, 11, 0, 0, 0x120, 48, 3, 1, 8, 24⟩
def dynamicSymbols : FunctionSymbol.Symbols :=
  ⟨5, dynsym, [default, ⟨8, 0x10, 0, 0, 0, 0⟩], ⟨3, strtab, stringBytes⟩⟩
def dynamic : Fixture :=
  { base with
    file := putLE (overwrite file 0x120
      (symbolRow 0 0 0 0 0 0 ++ symbolRow 8 0x10 0 0 0 0) ++
      sectionRow 33 11 0 0 0x120 48 3 1 8 24) 60 2 6
    table := { table with header := { table.header with sectionCount := 6 } }
    metadata := { metadata with
      sections := metadata.sections ++ [dynsym]
      tables := [symbols, dynamicSymbols] } }
example : dynamic.check = true := by decide +kernel

def omittedDynamic : Fixture :=
  { dynamic with metadata := { dynamic.metadata with tables := [symbols] } }
example : omittedDynamic.windowOK = true := by decide +kernel
example : omittedDynamic.check = false := by decide +kernel

def dynamicAlias : Fixture :=
  { dynamic with
    file := putLE dynamic.file 0x138 4 1
    metadata := { dynamic.metadata with tables :=
      [symbols, { dynamicSymbols with rows := [default, ⟨1, 0x10, 0, 0, 0, 0⟩] }] } }
example : dynamicAlias.metadataOK = true := by decide +kernel
example : dynamicAlias.check = false := by decide +kernel

def repeatedStatic : Fixture :=
  { dynamic with
    file := overwrite dynamic.file 0x2c0 (sectionRow 7 2 0 0 0x120 48 3 1 8 24)
    metadata := { dynamic.metadata with
      sections := metadata.sections ++ [{ dynsym with name := 7, kind := 2 }]
      tables := [symbols, { dynamicSymbols with sh := { dynsym with name := 7, kind := 2 } }] } }
example : repeatedStatic.windowOK = true := by decide +kernel
example : repeatedStatic.check = false := by decide +kernel

def repeatedDynamic : Fixture :=
  { dynamic with
    file := putLE (overwrite dynamic.file 0x150
      (symbolRow 0 0 0 0 0 0 ++ symbolRow 8 0x10 0 0 0 0) ++
      sectionRow 33 11 0 0 0x150 48 3 1 8 24) 60 2 7
    table := { table with header := { table.header with sectionCount := 7 } }
    metadata := { dynamic.metadata with
      sections := dynamic.metadata.sections ++ [{ dynsym with offset := 0x150 }]
      tables := [symbols, dynamicSymbols,
        { dynamicSymbols with sectionIndex := 6, sh := { dynsym with offset := 0x150 } }] } }
example : repeatedDynamic.windowOK = true := by decide +kernel
example : repeatedDynamic.check = false := by decide +kernel

example : ({ dynamic with metadata := { dynamic.metadata with
    tables := [dynamicSymbols, symbols] } } : Fixture).check = false := by decide +kernel

-- Declared extent is mandatory, even when an arbitrary shorter window passes.
def zeroExtent : Fixture :=
  { targetCase (symbolRow 1 0x12 0 1 0x400080 0) { target with size := 0 } with bytes := [] }
example : zeroExtent.metadataOK = true := by decide +kernel
example : zeroExtent.check = false := by decide +kernel

def partialExtent : Fixture := { base with bytes := [0xb8, 0x2a, 0, 0, 0] }
example : partialExtent.windowOK = true := by decide +kernel
example : partialExtent.check = false := by decide +kernel

-- Extend the LOAD and supplied code to seven bytes, leaving the section at
-- six. Thus the section extent, rather than LOAD/file coverage, must reject.
def beyondSection : Fixture :=
  { targetCase (symbolRow 1 0x12 0 1 0x400080 7) { target with size := 7 } with
    file := putLE (putLE (overwrite file 0xb8 (symbolRow 1 0x12 0 1 0x400080 7)) 96 8 7) 104 8 7
    table := { table with programs := [⟨1, 0x400080, ⟨0x80, 0x400080, 7, 7, 5, 4096⟩⟩] }
    bytes := [0xb8, 0x2a, 0, 0, 0, 0xc3, 0] }
example : beyondSection.metadataOK = true := by decide +kernel
example : beyondSection.windowOK = true := by decide +kernel
example : beyondSection.check = false := by decide +kernel

-- Both sides of the affine section mapping are checked, even though the
-- selected VA/file pair still agrees with the original valid LOAD.
def wrongSectionOffset : Fixture :=
  textCase (sectionRow 1 1 6 0x400080 0x81 6 0 0 16 0) { text with offset := 0x81 }
example : wrongSectionOffset.metadataOK = true := by decide +kernel
example : wrongSectionOffset.windowOK = true := by decide +kernel
example : wrongSectionOffset.check = false := by decide +kernel

def wrongSectionAddress : Fixture :=
  textCase (sectionRow 1 1 6 0x40007f 0x80 7 0 0 16 0)
    { text with address := 0x40007f, size := 7 }
example : wrongSectionAddress.metadataOK = true := by decide +kernel
example : wrongSectionAddress.windowOK = true := by decide +kernel
example : wrongSectionAddress.check = false := by decide +kernel

def beforeSection : Fixture :=
  textCase (sectionRow 1 1 6 0x400081 0x80 6 0 0 16 0) { text with address := 0x400081 }
example : beforeSection.metadataOK = true := by decide +kernel
example : beforeSection.windowOK = true := by decide +kernel
example : beforeSection.check = false := by decide +kernel

-- Duplicate the exact code at another file interval. Move section + window
-- together so the symbol contract holds and source bytes match, while the
-- executable LOAD still maps the original interval. Byte equality alone is
-- insufficient to establish the required file/VA correspondence.
def wrongLoadOffset : Fixture :=
  { textCase (sectionRow 1 1 6 0x400080 0x158 6 0 0 16 0) { text with offset := 0x158 } with
    file := overwrite (overwrite file 0x1c0
      (sectionRow 1 1 6 0x400080 0x158 6 0 0 16 0)) 0x158 [0xb8, 0x2a, 0, 0, 0, 0xc3]
    selected := ⟨⟨2, 1, target⟩, { text with offset := 0x158 }, ⟨0x400080, 0x158⟩⟩ }
example : wrongLoadOffset.metadataOK = true := by decide +kernel
example : wrongLoadOffset.contractOK = true := by decide +kernel
example : EDSL.ELF.checkCode
    (toMemory (EDSL.ELF.install wrongLoadOffset.file wrongLoadOffset.table.image empty))
    wrongLoadOffset.selected.window.base code = true := by decide +kernel
example : wrongLoadOffset.check = false := by decide +kernel

-- Binding/type errors remain structurally valid metadata. A local target
-- needs sh_info adjusted along with its binding to exercise the selection.
def objectSymbol : Fixture :=
  targetCase (symbolRow 1 0x11 0 1 0x400080 6) { target with info := 0x11 }
example : objectSymbol.metadataOK = true := by decide +kernel
example : objectSymbol.check = false := by decide +kernel

def weakSymbol : Fixture :=
  targetCase (symbolRow 1 0x22 0 1 0x400080 6) { target with info := 0x22 }
example : weakSymbol.metadataOK = true := by decide +kernel
example : weakSymbol.check = false := by decide +kernel

def localSymbol : Fixture :=
  { targetCase (symbolRow 1 2 0 1 0x400080 6) { target with info := 2 } with
    file := putLE (overwrite file 0xb8 (symbolRow 1 2 0 1 0x400080 6)) 0x22c 4 2
    metadata := staticWitness { symtab with info := 2 } [default, { target with info := 2 }, helper] }
example : localSymbol.metadataOK = true := by decide +kernel
example : localSymbol.check = false := by decide +kernel

def undefinedSymbol : Fixture :=
  targetCase (symbolRow 1 0x12 0 0 0x400080 6) { target with sh := 0 }
example : undefinedSymbol.metadataOK = true := by decide +kernel
example : undefinedSymbol.check = false := by decide +kernel

def nobitsText : Fixture :=
  textCase (sectionRow 1 8 6 0x400080 0x80 6 0 0 16 0) { text with kind := 8 }
example : nobitsText.metadataOK = true := by decide +kernel
example : nobitsText.check = false := by decide +kernel

def nonExecutableText : Fixture :=
  textCase (sectionRow 1 1 2 0x400080 0x80 6 0 0 16 0) { text with flags := 2 }
example : nonExecutableText.metadataOK = true := by decide +kernel
example : nonExecutableText.check = false := by decide +kernel

def writableText : Fixture :=
  textCase (sectionRow 1 1 7 0x400080 0x80 6 0 0 16 0) { text with flags := 7 }
example : writableText.metadataOK = true := by decide +kernel
example : writableText.check = false := by decide +kernel

-- Metadata and declared extent remain valid when a byte in the literal code
-- changes; the stale supplied byte contract must fail, including at the RET.
def staleImmediate : Fixture := { base with file := putLE file 0x81 1 0x2b }
example : staleImmediate.metadataOK = true := by decide +kernel
example : staleImmediate.contractOK = true := by decide +kernel
example : staleImmediate.check = false := by decide +kernel
example : ({ base with file := putLE file 0x85 1 0x90 } : Fixture).check = false := by decide +kernel

example : FunctionSymbol.admit staleImmediate.file table metadata requested selected code empty =
    .error .invalidImage := by
  have rejected : FunctionSymbol.check staleImmediate.file table metadata requested selected code = false :=
    by decide +kernel
  simp [FunctionSymbol.admit, rejected]

-- Source-review follow-up: a successful interior LOAD mapping must preserve
-- a nonzero VA displacement. Replacing the affine equation by offset equality
-- would reject this independently encoded positive case.
def interiorLoad : Fixture :=
  { base with
    file := putLE (putLE (putLE (putLE (putLE file
      72 8 0) 80 8 0x400000) 88 8 0x400000) 96 8 0x86) 104 8 0x86
    table := { table with programs := [
      ⟨1, 0x400000, ⟨0, 0x400000, 0x86, 0x86, 5, 4096⟩⟩] } }
example : interiorLoad.check = true := by decide +kernel

-- The seventh requested byte is zero in both file padding and installed BSS.
-- Match the complete symbol/PROGBITS extent while leaving it one byte beyond
-- the LOAD's file-backed range. A memory-size coverage check would accept it.
def zeroTailBSS : Fixture :=
  { base with
    file := putLE (putLE (putLE file 104 8 7) 0xc8 8 7) 0x1e0 8 7
    table := { table with programs := [
      ⟨1, 0x400080, ⟨0x80, 0x400080, 6, 7, 5, 4096⟩⟩] }
    metadata := { metadata with
      sections := [default, { text with size := 7 }, symtab, strtab, shstrtab]
      tables := [{ symbols with rows := [default, { target with size := 7 }, helper] }] }
    selected := ⟨⟨2, 1, { target with size := 7 }⟩, { text with size := 7 },
      ⟨0x400080, 0x80⟩⟩
    bytes := [0xb8, 0x2a, 0, 0, 0, 0xc3, 0] }
example : zeroTailBSS.metadataOK = true := by decide +kernel
example : zeroTailBSS.contractOK = true := by decide +kernel
example : EDSL.ELF.checkCode
    (toMemory (EDSL.ELF.install zeroTailBSS.file zeroTailBSS.table.image empty))
    zeroTailBSS.selected.window.base zeroTailBSS.bytes = true := by decide +kernel
example : zeroTailBSS.check = false := by decide +kernel

-- Turning that same zero byte into file-backed text supplies an accepted
-- control, with only the literal p_filesz and matching witness changed.
def zeroTailFile : Fixture :=
  { zeroTailBSS with
    file := putLE zeroTailBSS.file 96 8 7
    table := { zeroTailBSS.table with programs := [
      ⟨1, 0x400080, ⟨0x80, 0x400080, 7, 7, 5, 4096⟩⟩] } }
example : zeroTailFile.check = true := by decide +kernel

end EDSL.Tests.ELFFunctionSymbol

#audit_edsl
