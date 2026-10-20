/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean

/-! A bounded ELF64 symbol-window extractor for the frozen compiler corpus.
This is executable tooling, not a soundness theorem or a program certificate.
It deliberately does not replace EDSL.ELF's proved, restricted image loader. -/
namespace CorpusV1
open Lean

structure Section where
  kind : Nat
  flags : Nat
  address : Nat
  offset : Nat
  size : Nat
  link : Nat
  entrySize : Nat
  deriving Inhabited, Repr

structure Segment where
  kind : Nat
  flags : Nat
  offset : Nat
  address : Nat
  fileSize : Nat
  memorySize : Nat
  deriving Inhabited, Repr

structure Image where
  entry : Nat
  sections : Array Section
  segments : Array Segment

structure Window where
  name : String
  address : Nat
  offset : Nat
  bytes : ByteArray

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def readNat (data : ByteArray) (offset width : Nat) : Except String Nat := do
  require (offset + width ≤ data.size) s!"truncated field at file offset {offset}"
  let mut value := 0
  for index in [:width] do
    value := value + data[offset + index]!.toNat * 256^index
  return value

private def stringAt (data : ByteArray) (table : Section) (index : Nat) : Except String String := do
  require (index < table.size) "symbol string offset is outside its string table"
  let mut bytes : ByteArray := .empty
  for position in [index:table.size] do
    let byte := data[table.offset + position]!
    if byte == 0 then
      let some value := String.fromUTF8? bytes | throw "symbol name is not valid UTF-8"
      return value
    bytes := bytes.push byte
  throw "unterminated symbol name"

private def sectionAt (data : ByteArray) (base : Nat) : Except String Section := do
  return ⟨← readNat data (base + 4) 4, ← readNat data (base + 8) 8,
    ← readNat data (base + 16) 8, ← readNat data (base + 24) 8,
    ← readNat data (base + 32) 8, ← readNat data (base + 40) 4,
    ← readNat data (base + 56) 8⟩

private def segmentAt (data : ByteArray) (base : Nat) : Except String Segment := do
  return ⟨← readNat data base 4, ← readNat data (base + 4) 4,
    ← readNat data (base + 8) 8, ← readNat data (base + 16) 8,
    ← readNat data (base + 32) 8, ← readNat data (base + 40) 8⟩

private def parseImage (data : ByteArray) : Except String Image := do
  require (64 ≤ data.size && data.size ≤ 4 * 1024 * 1024) "ELF size outside 64 bytes..4 MiB tooling bound"
  require (data.extract 0 7 == ⟨#[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1]⟩) "expected ELF64 little-endian version 1"
  require ((← readNat data 16 2) == 2 && (← readNat data 18 2) == 62 &&
    (← readNat data 20 4) == 1 && (← readNat data 52 2) == 64) "expected x86-64 ET_EXEC ELF header"
  let entry ← readNat data 24 8
  let programOffset ← readNat data 32 8
  let sectionOffset ← readNat data 40 8
  let programCount ← readNat data 56 2
  let sectionCount ← readNat data 60 2
  require ((← readNat data 54 2) == 56 && 0 < programCount && programCount ≤ 128 &&
    64 ≤ programOffset && programOffset + programCount * 56 ≤ data.size) "invalid program-header table"
  require ((← readNat data 58 2) == 64 && 0 < sectionCount && sectionCount ≤ 1024 &&
    64 ≤ sectionOffset && sectionOffset + sectionCount * 64 ≤ data.size) "invalid section-header table"
  let mut sections := #[]
  for index in [:sectionCount] do
    let codeSection ← sectionAt data (sectionOffset + index * 64)
    if codeSection.kind != 8 then
      require (codeSection.offset + codeSection.size ≤ data.size) "section exceeds file bounds"
    sections := sections.push codeSection
  let mut segments := #[]
  for index in [:programCount] do
    let segment ← segmentAt data (programOffset + index * 56)
    if segment.kind == 1 then
      require (0 < segment.memorySize && segment.fileSize ≤ segment.memorySize &&
        segment.offset + segment.fileSize ≤ data.size &&
        4096 ≤ segment.address && segment.address + segment.memorySize ≤ 2^47 &&
        segment.offset % 4096 == segment.address % 4096) "invalid or non-page-congruent low-canonical PT_LOAD extent"
    segments := segments.push segment
  -- Reject competing partial mappings and permission changes too, not merely
  -- two executable segments that each contain an entire selected symbol.
  for left in [:segments.size] do
    for right in [left + 1:segments.size] do
      let first := segments[left]!
      let second := segments[right]!
      if first.kind == 1 && second.kind == 1 then
        let firstEnd := (first.address + first.memorySize + 4095) / 4096
        let secondEnd := (second.address + second.memorySize + 4095) / 4096
        require (firstEnd ≤ second.address / 4096 || secondEnd ≤ first.address / 4096)
          "overlapping PT_LOAD pages are outside the corpus extraction profile"
  return ⟨entry, sections, segments⟩

private def windowAt (data : ByteArray) (image : Image) (name : String)
    (symbolBase : Nat) : Except String Window := do
  let info ← readNat data (symbolBase + 4) 1
  let sectionIndex ← readNat data (symbolBase + 6) 2
  let address ← readNat data (symbolBase + 8) 8
  let size ← readNat data (symbolBase + 16) 8
  require (info == 18 && 0 < sectionIndex && sectionIndex < image.sections.size &&
    0 < size && size ≤ 65536 && address + size ≤ 2^64)
    s!"{name}: expected one global, defined, nonempty STT_FUNC symbol within tooling limits"
  let codeSection := image.sections[sectionIndex]!
  require (codeSection.kind == 1 && codeSection.flags &&& 6 == 6 &&
    codeSection.address ≤ address && address + size ≤ codeSection.address + codeSection.size)
    s!"{name}: symbol is outside its allocated executable PROGBITS section"
  let fileOffset := codeSection.offset + (address - codeSection.address)
  let covering := image.segments.filter fun segment =>
    segment.kind == 1 && segment.flags &&& 5 == 5 &&
      segment.address ≤ address && address + size ≤ segment.address + segment.fileSize
  require (covering.size == 1) s!"{name}: expected one readable executable file-backed PT_LOAD interval"
  let segment := covering[0]!
  require (fileOffset == segment.offset + (address - segment.address) &&
    fileOffset + size ≤ data.size) s!"{name}: section and PT_LOAD file mapping disagree"
  return ⟨name, address, fileOffset, data.extract fileOffset (fileOffset + size)⟩

private def extractWindows (data : ByteArray) (names : Array String) : Except String (Image × Array Window) := do
  let image ← parseImage data
  let tables := image.sections.filter (·.kind == 2)
  require (tables.size == 1) "expected exactly one SHT_SYMTAB"
  let symbols := tables[0]!
  require (symbols.entrySize == 24 && symbols.size % 24 == 0 &&
    symbols.size / 24 ≤ 65536 && symbols.link < image.sections.size) "invalid symbol table"
  let strings := image.sections[symbols.link]!
  require (strings.kind == 3 && 0 < strings.size) "symbol table link is not a string table"
  let mut windows := #[]
  for name in names do
    let mut found : Option Window := none
    for index in [:symbols.size / 24] do
      let base := symbols.offset + index * 24
      let observed ← stringAt data strings (← readNat data base 4)
      if observed == name then
        require found.isNone s!"duplicate selected symbol {name}"
        found := some (← windowAt data image name base)
    let some window := found | throw s!"missing corpus function {name}"
    windows := windows.push window
  return (image, windows)

private def hexByte (byte : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!]

private def bytesHex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map hexByte)

private def definitionId (number : Nat) : String :=
  if number < 10 then "0" ++ toString number else toString number

private def windowJson (id : String) (window : Window) : Json := Json.mkObj [
  ("definition_id", toJson id),
  ("symbol", toJson window.name),
  ("contract_id", toJson ("v1:" ++ id ++ ":" ++ window.name)),
  ("address", toJson window.address),
  ("file_offset", toJson window.offset),
  ("size", toJson window.bytes.size),
  ("bytes_hex", toJson (bytesHex window.bytes)),
  ("certification", toJson ("unverified" : String))]

private def parseNames (specifications : String) : Except String (Array String) := do
  let mut names := #[]
  for line in specifications.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let fields := line.splitOn "\t"
    require (fields.length == 5) "specification row must have five tab-separated columns"
    require (fields[0]! == definitionId (names.size + 1)) "definition IDs must be ordered 01 through 40"
    for field in fields do
      require (field.toList.any fun character => !character.isWhitespace) "empty specification field"
    let name := fields[1]!
    require (name.startsWith "c_" && name.toList.all fun character =>
      character.isAlphanum || character == '_') "unsafe function symbol in corpus definition"
    require (!names.contains name) "duplicate corpus function in definition"
    names := names.push name
  require (names.size == 40) "v1 is frozen at exactly 40 function definitions"
  return names

private def run (specPath elfPath outputPath label : String) : IO Unit := do
  let specifications ← IO.FS.readFile specPath
  let names ← IO.ofExcept (parseNames specifications)
  let data ← IO.FS.readBinFile elfPath
  let (image, windows) ← IO.ofExcept (extractWindows data names)
  IO.FS.createDirAll outputPath
  for window in windows do
    IO.FS.writeBinFile (System.FilePath.mk outputPath / (window.name ++ ".bin")) window.bytes
  let manifest := Json.mkObj [
    ("schema", toJson ("edsl.compiler-corpus.v1" : String)),
    ("compiler", toJson label),
    ("elf_kind", toJson ("ELF64LE ET_EXEC EM_X86_64" : String)),
    ("elf_size", toJson data.size),
    ("elf_entry", toJson image.entry),
    ("functions_extracted", toJson windows.size),
    ("functions_certified_end_to_end", toJson (0 : Nat)),
    ("scope", toJson ("Executable symbol windows extracted from final ELF; no decoding, functional, concurrency, or OS proof is implied." : String)),
    ("functions", Json.arr (windows.mapIdx fun index window => windowJson (definitionId (index + 1)) window))]
  IO.FS.writeFile (System.FilePath.mk outputPath / "manifest.json") (manifest.pretty ++ "\n")
  (← IO.getStdout).putStrLn s!"EXTRACTED {windows.size} final-ELF function windows for {label}; CERTIFIED 0"

end CorpusV1

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [specPath, elfPath, outputPath, label] =>
    try
      CorpusV1.run specPath elfPath outputPath label
      return 0
    catch error =>
      (← IO.getStderr).putStrLn s!"CORPUS-REJECTED: {error}; no program-defect conclusion"
      return 1
  | _ =>
    (← IO.getStderr).putStrLn "usage: lean --run corpus/Extract.lean SPECIFICATIONS.tsv FINAL.elf OUTPUT_DIR COMPILER_LABEL"
    return 2
