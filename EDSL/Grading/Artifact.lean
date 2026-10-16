/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Hex
import EDSL.Grading.Task
import EDSL.ELF.Loader

namespace EDSL.Grading
open X86

/-- Full file identity is literal bytes. ELF spans are explicit; selection
never stops at the first return instruction. The controller quotes large files
with a balanced tree of list appends, avoiding deep expression syntax. -/
inductive Artifact where
  | raw (file : List Byte)
  | elf (file : List Byte) (span : Nat)
  deriving Repr

namespace Artifact

inductive Error where
  | empty | codeLimit | fileLimit | elf (error : ELF.Error) | window
  deriving Repr

structure Selection where
  code : List Byte
  image : Option ELF.Image
  deriving Repr

/-- This admission bound is independent of the task's universal input domain. -/
def executableWindow (image : ELF.Image) (length : Nat) : Bool :=
  decide (0 < length ∧ length ≤ 4096 ∧ image.entry + length ≤ 2^47) &&
  image.segments.any fun segment => segment.executable &&
    decide (segment.virtualAddress ≤ image.entry ∧
      image.entry + length ≤ segment.virtualAddress + segment.fileSize)

def checkWindow (file : List Byte) (image : ELF.Image) (code : List Byte) : Bool :=
  executableWindow image code.length &&
    ELF.checkCode (OS.AddressSpace.toMemory (ELF.install file image OS.AddressSpace.empty))
      (ELF.codeAddress image) code

def select : Artifact → Except Error Selection
  | .raw code => do
    if code.isEmpty then throw .empty
    if code.length > 4096 then throw .codeLimit
    return ⟨code, none⟩
  | .elf file span => do
    if file.length > ELF.maxFileSize then throw .fileLimit
    if span = 0 then throw .empty
    if span > 4096 then throw .codeLimit
    let image ← (ELF.parse file).mapError Error.elf
    let some segment := image.segments.find? fun segment => segment.executable &&
      decide (segment.virtualAddress ≤ image.entry ∧
        image.entry + span ≤ segment.virtualAddress + segment.fileSize)
      | throw .window
    let code := (file.drop (segment.offset + (image.entry - segment.virtualAddress))).take span
    if code.length ≠ span then throw .window
    if !checkWindow file image code then throw .window
    return ⟨code, some image⟩

def selectedBytes (artifact : Artifact) : Option (List Byte) :=
  (select artifact).toOption.map (·.code)

/-- Full-artifact statement, including successful parsing/window admission.
It entails the fixed task contract for the exact selected bytes. -/
def Claim (id : TaskID) (artifact : Artifact) : Prop :=
  ∃ selected, select artifact = .ok selected ∧ Grading.Claim id selected.code

theorem certify (id : TaskID) (artifact : Artifact) (code : List Byte)
    (selection : selectedBytes artifact = some code) (proof : Grading.Claim id code) :
    Claim id artifact := by
  cases result : select artifact with
  | error e => simp [selectedBytes, result, Except.toOption] at selection
  | ok selected =>
    have eq : selected.code = code := by
      simpa [selectedBytes, result, Except.toOption] using selection
    exact ⟨selected, result, eq.symm ▸ proof⟩

/-- Checked executable bytes in the abstract ELF image remain the same for any
fresh prior address space. Loading/freshness and native CPU correspondence are
separate environmental obligations. -/
theorem checked_window_code (file : List Byte) (image : ELF.Image) (code : List Byte)
    (prior : OS.AddressSpace.Space) (checked : checkWindow file image code = true) :
    CodeAt (OS.AddressSpace.toMemory (ELF.install file image prior))
      (ELF.codeAddress image) code := by
  have bytes := ELF.checkCode_sound _ _ _ (Bool.and_eq_true_iff.mp checked).2
  exact ⟨bytes.1, fun index byte atIndex =>
    ELF.installed_fetch_independent file image prior _ byte (bytes.2 index byte atIndex)⟩

end Artifact
end EDSL.Grading
