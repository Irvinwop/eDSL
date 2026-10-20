/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionCandidateFacts

namespace EDSL.ELF.FunctionCandidate
open X86 FunctionWindow FunctionSymbol

/-- Extraction failures establish no program defect. Layout/profile rejection is
separate from a missing or ambiguous external name and a truncated input. -/
inductive Error where
  | fileSize
  | truncated
  | invalidName
  | invalidTable
  | missingName
  | duplicateName
  | rejected
  deriving DecidableEq, Repr

def fileBytes (data : ByteArray) : List Byte :=
  data.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat

private def read (data : ByteArray) (offset width : Nat) : Except Error Nat := do
  if offset + width > data.size then throw .truncated
  let mut result := 0
  for index in [:width] do
    result := result + data[offset + index]!.toNat * 256 ^ index
  return result

private def slice (data : ByteArray) (offset size : Nat) : Except Error (List Byte) := do
  if offset + size > data.size then throw .truncated
  return fileBytes (data.extract offset (offset + size))

private def programAt (data : ByteArray) (base : Nat) : Except Error ProgramHeader := do
  let kind ← read data base 4
  let flags ← read data (base + 4) 4
  let offset ← read data (base + 8) 8
  let address ← read data (base + 16) 8
  let physical ← read data (base + 24) 8
  let size ← read data (base + 32) 8
  let memory ← read data (base + 40) 8
  let alignment ← read data (base + 48) 8
  return ⟨kind, physical, ⟨offset, address, size, memory, flags, alignment⟩⟩

private def sectionAt (data : ByteArray) (base : Nat) : Except Error Section := do
  return ⟨← read data base 4, ← read data (base + 4) 4,
    ← read data (base + 8) 8, ← read data (base + 16) 8,
    ← read data (base + 24) 8, ← read data (base + 32) 8,
    ← read data (base + 40) 4, ← read data (base + 44) 4,
    ← read data (base + 48) 8, ← read data (base + 56) 8⟩

private def symbolAt (data : ByteArray) (base : Nat) : Except Error Symbol := do
  return ⟨← read data base 4, ← read data (base + 4) 1,
    ← read data (base + 5) 1, ← read data (base + 6) 2,
    ← read data (base + 8) 8, ← read data (base + 16) 8⟩

private def stringsAt (data : ByteArray) (sections : List Section) (index : Nat) :
    Except Error Strings := do
  let some sh := sections[index]? | throw .invalidTable
  return ⟨index, sh, ← slice data sh.offset sh.size⟩

private def symbolsAt (data : ByteArray) (sections : List Section)
    (sh : Section) (index : Nat) : Except Error Symbols := do
  -- These are the existing complete-table profile bounds, not compiler hints.
  if sh.entrySize != 24 || sh.size % 24 != 0 ||
      sh.offset + sh.size > data.size then throw .invalidTable
  let strings ← stringsAt data sections sh.link
  let rows ← (List.range (sh.size / 24)).mapM fun row =>
    symbolAt data (sh.offset + row * 24)
  return ⟨index, sh, rows, strings⟩

/-- Bounded *untrusted* proposal of every metadata row, including dynamic tables.
The full file and requested byte name are finally checked by FunctionInput.check.
No suffix, alternative symbol, zero-size inference or partial table is accepted. -/
def extract (data : ByteArray) (name : List Byte) : Except Error FunctionInput := do
  if data.size < 64 || data.size > maxFileSize then throw .fileSize
  if name.isEmpty || name.any (· == 0) then throw .invalidName
  let header : Header := ⟨← read data 7 1, ← read data 24 8,
    ← read data 32 8, ← read data 40 8, ← read data 60 2, ← read data 62 2⟩
  let count ← read data 56 2
  if count = 0 || count > maxProgramHeaders ||
      header.programOffset + count * 56 > data.size ||
      header.sectionCount = 0 || header.sectionCount > maxFileSize / 64 ||
      header.sectionOffset + header.sectionCount * 64 > data.size then throw .invalidTable
  let programs ← (List.range count).mapM fun index =>
    programAt data (header.programOffset + index * 56)
  let sections ← (List.range header.sectionCount).mapM fun index =>
    sectionAt data (header.sectionOffset + index * 64)
  -- Metadata.Shape requires exactly one static table and at most one dynamic
  -- table. Reject that necessary bound before proposing any potentially large
  -- symbol-row or string data; never select a subset of the tables.
  if (sections.filter (·.kind == 2)).length != 1 ||
      (sections.filter (·.kind == 11)).length > 1 then throw .invalidTable
  let names ← stringsAt data sections header.sectionNames
  let tables ← ((sections.zipIdx.filter fun pair => pair.1.isSymbols)).mapM fun pair =>
    symbolsAt data sections pair.1 pair.2
  let metadata : Metadata := ⟨sections, names, tables⟩
  let occurrence ← match metadata.matches name with
    | [] => throw .missingName
    | [selected] => pure selected
    | _ => throw .duplicateName
  let some sh := sections[occurrence.symbol.sh]? | throw .invalidTable
  let offset := sh.offset + (occurrence.symbol.value - sh.address)
  if occurrence.symbol.size = 0 || occurrence.symbol.size > 64 then throw .rejected
  let bytes ← slice data offset occurrence.symbol.size
  let input : FunctionInput := ⟨⟨header, programs⟩, metadata,
    ⟨occurrence, sh, ⟨occurrence.symbol.value, offset⟩⟩, bytes⟩
  if input.check (fileBytes data) name then return input else throw .rejected

end EDSL.ELF.FunctionCandidate
