/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Contract
import EDSL.ELF.Loader

set_option warningAsError true

namespace EDSL.Grading.CallStack
open X86 EDSL.CallStack

/-- Literal complete file identity and selected entry offset. An ELF span is
the whole code window, including any helpers preceding the entry. -/
inductive Artifact where
  | raw (file : List Byte) (entryOffset : Nat)
  | elf (file : List Byte) (span entryOffset : Nat)

namespace Artifact

inductive Error where
  | empty | codeLimit | fileLimit | entry | elf (error : ELF.Error) | window
  deriving DecidableEq, Repr

structure Selection where
  program : Program
  image : Option ELF.Image
  start : Option Nat

/-- The entire natural interval must be executable and file-backed in one
segment. The start is independent of the ELF entry and cannot wrap. -/
def executableWindow (image : ELF.Image) (start length : Nat) : Bool :=
  decide (0 < length ∧ length ≤ 4096 ∧ start + length ≤ 2^47) &&
    image.segments.any fun segment => segment.executable &&
      decide (segment.virtualAddress ≤ start ∧
        start + length ≤ segment.virtualAddress + segment.fileSize)

/-- Check every literal byte at the whole window's start, and bind its
selected program entry to the actual ELF entry. No first-RET scan is used. -/
def checkWindow (file : List Byte) (image : ELF.Image) (start : Nat)
    (program : Program) : Bool :=
  (executableWindow image start program.bytes.length &&
    decide (program.entry < program.bytes.length ∧ start + program.entry = image.entry)) &&
  ELF.checkCode (OS.AddressSpace.toMemory (ELF.install file image OS.AddressSpace.empty))
    (BitVec.ofNat 64 start) program.bytes

private def selectImage (file : List Byte) (image : ELF.Image)
    (span entryOffset : Nat) : Except Error Selection :=
  if image.entry < entryOffset then .error .entry else
  let start := image.entry - entryOffset
  match image.segments.find? fun segment => segment.executable &&
    decide (segment.virtualAddress ≤ start ∧
      start + span ≤ segment.virtualAddress + segment.fileSize) with
  | none => .error .window
  | some segment =>
    let code := (file.drop (segment.offset + (start - segment.virtualAddress))).take span
    if code.length ≠ span then .error .window else
    let program : Program := ⟨code, entryOffset⟩
    if !checkWindow file image start program then .error .window else
    .ok ⟨program, some image, some start⟩

def select : Artifact → Except Error Selection
  | .raw file entryOffset =>
    if file.isEmpty then .error .empty else
    if file.length > 4096 then .error .codeLimit else
    if entryOffset ≥ file.length then .error .entry else
    .ok ⟨⟨file, entryOffset⟩, none, none⟩
  | .elf file span entryOffset =>
    if file.length > ELF.maxFileSize then .error .fileLimit else
    if span = 0 then .error .empty else
    if span > 4096 then .error .codeLimit else
    if entryOffset ≥ span then .error .entry else
    match ELF.parse file with
    | .error error => .error (.elf error)
    | .ok image => selectImage file image span entryOffset

def selectedProgram (artifact : Artifact) : Option Program :=
  (select artifact).toOption.map (·.program)

/-- The final theorem binds the entire literal file, span and entry metadata,
successful selection, and the fixed closed resource-first program claim. -/
def Claim (artifact : Artifact) : Prop :=
  ∃ selected, select artifact = .ok selected ∧ CallStack.Claim selected.program

theorem certify (artifact : Artifact) (program : Program)
    (selection : selectedProgram artifact = some program) (proof : CallStack.Claim program) :
    Claim artifact := by
  cases result : select artifact with
  | error error => simp [selectedProgram, result, Except.toOption] at selection
  | ok selected =>
    have same : selected.program = program := by
      simpa [selectedProgram, result, Except.toOption] using selection
    exact ⟨selected, result, same.symm ▸ proof⟩

/-- The exact whole window is present in the installed current memory for
every prior space, including occupied priors. Loader freshness and native
CPU correspondence are separate environmental obligations. -/
theorem checked_window_code (file : List Byte) (image : ELF.Image) (start : Nat)
    (program : Program) (prior : OS.AddressSpace.Space)
    (checked : checkWindow file image start program = true) :
    CodeAt (OS.AddressSpace.toMemory (ELF.install file image prior))
      (BitVec.ofNat 64 start) program.bytes := by
  have code := ELF.checkCode_sound _ _ _ (Bool.and_eq_true_iff.mp checked).2
  exact ⟨code.1, fun index byte atIndex =>
    ELF.installed_fetch_independent file image prior _ byte (code.2 index byte atIndex)⟩

theorem checked_window_binding {file image start program}
    (checked : checkWindow file image start program = true) :
    program.entry < program.bytes.length ∧ start + program.entry = image.entry :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).2

theorem checked_window_entry {file image start program}
    (checked : checkWindow file image start program = true) :
    BitVec.ofNat 64 start + BitVec.ofNat 64 program.entry = ELF.codeAddress image := by
  rw [← BitVec.ofNat_add, (checked_window_binding checked).2]
  rfl

theorem select_raw {file entryOffset selected}
    (selection : select (.raw file entryOffset) = .ok selected) :
    selected.program.bytes = file ∧ selected.program.entry = entryOffset ∧
      selected.image = none ∧ selected.start = none ∧
      entryOffset < file.length ∧ file.length ≤ 4096 := by
  simp only [select] at selection
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  cases selection
  simp_all

private theorem selectImage_sound {file image span entryOffset selected}
    (selection : selectImage file image span entryOffset = .ok selected) :
    selected.program.entry = entryOffset ∧ selected.program.bytes.length = span ∧
      selected.image = some image ∧ selected.start = some (image.entry - entryOffset) ∧
      checkWindow file image (image.entry - entryOffset) selected.program = true := by
  simp only [selectImage] at selection
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  cases selection
  simp_all

/-- Successful ELF selection binds the parsed image and whole file-backed
window to the selected Program, including a possible helper prefix. -/
theorem select_elf {file span entryOffset selected}
    (selection : select (.elf file span entryOffset) = .ok selected) :
    ∃ image, ELF.parse file = .ok image ∧
      selected.program.entry = entryOffset ∧ selected.program.bytes.length = span ∧
      selected.image = some image ∧ selected.start = some (image.entry - entryOffset) ∧
      checkWindow file image (image.entry - entryOffset) selected.program = true := by
  simp only [select] at selection
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  split at selection <;> try simp_all
  cases parsed : ELF.parse file with
  | error error => simp [parsed] at selection
  | ok image =>
    simp only [parsed] at selection
    exact ⟨image, rfl, selectImage_sound selection⟩

/-- Selection itself entails the current installed CodeAt proof for any
prior space and the correct entry address within that same whole window. -/
theorem selected_elf_code {file span entryOffset selected}
    (selection : select (.elf file span entryOffset) = .ok selected)
    (prior : OS.AddressSpace.Space) :
    ∃ image start, ELF.parse file = .ok image ∧ selected.image = some image ∧
      selected.start = some start ∧ selected.program.entry = entryOffset ∧
      selected.program.bytes.length = span ∧
      CodeAt (OS.AddressSpace.toMemory (ELF.install file image prior))
        (BitVec.ofNat 64 start) selected.program.bytes ∧
      BitVec.ofNat 64 start + BitVec.ofNat 64 selected.program.entry = ELF.codeAddress image := by
  obtain ⟨image, parsed, entry, length, installed, start, checked⟩ := select_elf selection
  exact ⟨image, image.entry - entryOffset, parsed, installed, start, entry, length,
    checked_window_code file image _ selected.program prior checked, checked_window_entry checked⟩

end Artifact
end EDSL.Grading.CallStack
