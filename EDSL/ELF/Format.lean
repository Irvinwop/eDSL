/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AddressSpace

namespace EDSL.ELF
open X86

abbrev pageSize : Nat := 4096
abbrev maxFileSize : Nat := 65536
abbrev maxProgramHeaders : Nat := 16
abbrev maxSegmentSize : Nat := 65536

inductive Error where
  | truncated
  | badMagic
  | unsupportedFormat
  | unsupportedProgramHeader (kind : Nat)
  | resourceLimit
  | invalidImage
  | mappingCollision
  deriving DecidableEq, Repr

/-- Integer fields remain natural numbers until validated address conversion. -/
structure Segment where
  offset : Nat
  virtualAddress : Nat
  fileSize : Nat
  memorySize : Nat
  flags : Nat
  alignment : Nat
  deriving DecidableEq, Repr

structure Image where
  entry : Nat
  segments : List Segment
  deriving DecidableEq, Repr

def Segment.executable (segment : Segment) : Bool := decide (segment.flags % 2 = 1)
def Segment.writable (segment : Segment) : Bool := decide ((segment.flags / 2) % 2 = 1)

def Segment.permissions (segment : Segment) : OS.AddressSpace.Permissions :=
  ⟨true, segment.writable, segment.executable⟩

def Segment.pageStart (segment : Segment) : Nat := segment.virtualAddress / pageSize * pageSize

def Segment.pageEnd (segment : Segment) : Nat :=
  (segment.virtualAddress + segment.memorySize + (pageSize - 1)) / pageSize * pageSize

def Segment.pageRegion (segment : Segment) : OS.AddressSpace.Region :=
  ⟨BitVec.ofNat 64 segment.pageStart, segment.pageEnd - segment.pageStart⟩

def Segment.pageDisjoint (left right : Segment) : Prop :=
  left.pageEnd ≤ right.pageStart ∨ right.pageEnd ≤ left.pageStart

instance (left right : Segment) : Decidable (left.pageDisjoint right) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Segment.pageOrdered (left right : Segment) : Prop := left.pageEnd ≤ right.pageStart

instance (left right : Segment) : Decidable (left.pageOrdered right) :=
  inferInstanceAs (Decidable (_ ≤ _))

def powerOfTwo (value : Nat) : Bool :=
  decide (0 < value ∧ Nat.land value (value - 1) = 0)

def Segment.valid (fileLength : Nat) (segment : Segment) : Bool :=
  decide (0 < segment.memorySize ∧ segment.memorySize ≤ maxSegmentSize ∧
    segment.fileSize ≤ segment.memorySize ∧ segment.offset + segment.fileSize ≤ fileLength ∧
    pageSize ≤ segment.virtualAddress ∧ segment.virtualAddress + segment.memorySize ≤ 2^47 ∧
    4 ≤ segment.flags ∧ segment.flags < 8 ∧
    segment.offset % pageSize = segment.virtualAddress % pageSize) &&
  (decide (segment.alignment = 0 ∨ segment.alignment = 1) ||
    (powerOfTwo segment.alignment &&
      decide (segment.offset % segment.alignment = segment.virtualAddress % segment.alignment)))

/-- A segment is accepted only with readable ordinary-memory permissions. Entry
must initially name an executable file byte, not BSS or a hole. -/
def valid (file : List Byte) (image : Image) : Bool :=
  decide (image.entry < 2^47 ∧ image.segments ≠ []) &&
  image.segments.all (Segment.valid file.length) &&
  decide (image.segments.Pairwise Segment.pageOrdered) &&
  image.segments.any (fun segment => segment.executable &&
    decide (segment.virtualAddress ≤ image.entry ∧ image.entry < segment.virtualAddress + segment.fileSize))

/-- Bounded little-endian decoding; arithmetic cannot wrap a host-sized offset. -/
def readNat (file : List Byte) (offset width : Nat) : Except Error Nat :=
  if offset + width ≤ file.length then
    .ok (((file.drop offset).take width).foldr (fun byte rest => byte.toNat + rest * 256) 0)
  else .error .truncated

private structure Header where
  entry : Nat
  programOffset : Nat
  programCount : Nat

private def readHeader (file : List Byte) : Except Error Header := do
  if file.length > maxFileSize then throw .resourceLimit
  if file.length < 64 then throw .truncated
  if file.take 4 ≠ [0x7f, 0x45, 0x4c, 0x46] then throw .badMagic
  let elfClass ← readNat file 4 1
  let encoding ← readNat file 5 1
  let identVersion ← readNat file 6 1
  let osAbi ← readNat file 7 1
  let abiVersion ← readNat file 8 1
  let padding ← readNat file 9 7
  let kind ← readNat file 16 2
  let machine ← readNat file 18 2
  let version ← readNat file 20 4
  let entry ← readNat file 24 8
  let programOffset ← readNat file 32 8
  let flags ← readNat file 48 4
  let headerSize ← readNat file 52 2
  let programSize ← readNat file 54 2
  let programCount ← readNat file 56 2
  if elfClass ≠ 2 ∨ encoding ≠ 1 ∨ identVersion ≠ 1 ∨
      (osAbi ≠ 0 ∧ osAbi ≠ 3) ∨ abiVersion ≠ 0 ∨ padding ≠ 0 ∨
      kind ≠ 2 ∨ machine ≠ 62 ∨ version ≠ 1 ∨ flags ≠ 0 ∨
      headerSize ≠ 64 ∨ programSize ≠ 56 then throw .unsupportedFormat
  if programCount = 0 ∨ programCount > maxProgramHeaders then throw .resourceLimit
  if programOffset < 64 ∨ programOffset % 8 ≠ 0 ∨
      programOffset + programCount * 56 > file.length then throw .truncated
  return ⟨entry, programOffset, programCount⟩

private def readSegment (file : List Byte) (base : Nat) : Except Error Segment := do
  let flags ← readNat file (base + 4) 4
  let offset ← readNat file (base + 8) 8
  let virtualAddress ← readNat file (base + 16) 8
  let fileSize ← readNat file (base + 32) 8
  let memorySize ← readNat file (base + 40) 8
  let alignment ← readNat file (base + 48) 8
  return ⟨offset, virtualAddress, fileSize, memorySize, flags, alignment⟩

private def decode (file : List Byte) : Except Error Image := do
  let header ← readHeader file
  let mut segments : List Segment := []
  let mut stackSeen := false
  for index in List.range header.programCount do
    let base := header.programOffset + index * 56
    let kind ← readNat file base 4
    if kind = 1 then
      segments := (← readSegment file base) :: segments
    else if kind = 0 then
      pure ()
    else if kind = 0x6474e551 then
      let stack ← readSegment file base
      if stackSeen ∨ stack.flags ≠ 6 ∨ stack.fileSize ≠ 0 ∨ stack.memorySize ≠ 0 then
        throw .unsupportedFormat
      stackSeen := true
    else throw (.unsupportedProgramHeader kind)
  return ⟨header.entry, segments.reverse⟩

/-- Restricted ELF64LE ET_EXEC/EM_X86_64 containers. Section tables, symbol names
and objcopy output are not consulted. This is not Linux process startup. -/
def parse (file : List Byte) : Except Error Image := do
  let image ← decode file
  if valid file image then return image else throw .invalidImage

theorem readNat_bound (file : List Byte) (offset width value : Nat)
    (success : readNat file offset width = .ok value) : offset + width ≤ file.length := by
  unfold readNat at success
  split at success <;> simp_all

theorem parse_valid (file : List Byte) (image : Image)
    (success : parse file = .ok image) : valid file image = true := by
  cases decoded : decode file with
  | error error => simp [parse, decoded] at success
  | ok candidate =>
    simp only [parse, decoded, ok_bind] at success
    split at success <;> simp_all

/-- Decidable certificate check without requiring equality on general effects. -/
def checkParsed (file : List Byte) (image : Image) : Bool :=
  match parse file with
  | .ok observed => decide (observed = image)
  | .error _ => false

theorem checkParsed_sound (file : List Byte) (image : Image)
    (checked : checkParsed file image = true) : parse file = .ok image := by
  cases parsed : parse file with
  | error error => simp [checkParsed, parsed] at checked
  | ok observed =>
    have equal : observed = image := of_decide_eq_true (by simpa [checkParsed, parsed] using checked)
    cases equal
    rfl

end EDSL.ELF
