/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicSet64.Contract
import EDSL.ELF.Loader
import EDSL.Sum32.Artifact

namespace EDSL.AtomicSet64.Artifact
open X86 OS.AddressSpace

/-- The whole raw artifact must equal the selected complete locked routine. -/
def checkRaw (operation : Logical64.Operation) (candidate : List Byte) : Bool :=
  decide (candidate = bytes operation)

def RawClaim (operation : Logical64.Operation) (candidate : List Byte) : Prop :=
  ∀ input shared initial, Pre candidate input shared initial →
    LockedSet64.AllExecutions initial (ResultContract operation input shared initial)

def RunClaim (operation : Logical64.Operation) (candidate : List Byte) : Prop :=
  ∀ input shared initial, Pre candidate input shared initial → ∀ choices,
    ∃ output, LockedSet64.run choices 2 initial = .ok output ∧
      ResultContract operation input shared initial output

theorem raw_sound {operation : Logical64.Operation} {candidate : List Byte}
    (accepted : checkRaw operation candidate = true) : RawClaim operation candidate := by
  have same : candidate = bytes operation := of_decide_eq_true accepted
  subst candidate
  exact fun _ _ _ admitted => semantics operation admitted

theorem raw_run {operation : Logical64.Operation} {candidate : List Byte}
    (accepted : checkRaw operation candidate = true) : RunClaim operation candidate := by
  have same : candidate = bytes operation := of_decide_eq_true accepted
  subst candidate
  exact fun _ _ _ admitted choices => AtomicSet64.run operation admitted choices

/-- All three routines occupy exactly five bytes. There must be one executable
segment, starting at entry, without executable prefix, suffix or BSS. Other
nonexecutable segments remain loader data; symbols and sections confer no trust. -/
def completeText (image : ELF.Image) : Bool :=
  match image.segments.filter ELF.Segment.executable with
  | [segment] => decide (segment.virtualAddress = image.entry ∧
      segment.fileSize = 5 ∧ segment.memorySize = 5)
  | _ => false

def checkELF (operation : Logical64.Operation) (file : List Byte) (image : ELF.Image) : Bool :=
  ELF.checkParsed file image && completeText image && ELF.checkEntry file image (bytes operation)

theorem checkELF_sound {operation : Logical64.Operation} {file : List Byte} {image : ELF.Image}
    (accepted : checkELF operation file image = true) :
    ELF.parse file = .ok image ∧ completeText image = true ∧
      ELF.checkEntry file image (bytes operation) = true := by
  obtain ⟨parsedAndComplete, entry⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨parsed, complete⟩ := Bool.and_eq_true_iff.mp parsedAndComplete
  exact ⟨ELF.checkParsed_sound _ _ parsed, complete, entry⟩

theorem pre_of_loaded {operation : Logical64.Operation} {file : List Byte} {image : ELF.Image}
    {input shared initial} (accepted : checkELF operation file image = true) (prior : Space)
    (resources : Resources (bytes operation) input shared initial)
    (space : shared.legacy.shared.resources.space = ELF.install file image prior)
    (entry : initial.rip = ELF.codeAddress image) :
    Pre (bytes operation) input shared initial := by
  refine ⟨resources, ?_⟩
  rw [resources.coupled, space, entry]
  exact ELF.checked_entry_code _ _ _ prior (checkELF_sound accepted).2.2

/-- Bind the literal whole file, its actual parsed metadata and fresh loader
installation to a callable theorem with current code/stack/actor authority.
This does not establish process startup or source/TSO/physical/kernel refinement. -/
def ELFClaim (operation : Logical64.Operation) (file : List Byte) (image : ELF.Image) : Prop :=
  ELF.parse file = .ok image ∧ completeText image = true ∧
    ∀ prior, ELF.fresh image prior = true → ∀ input shared initial,
      Resources (bytes operation) input shared initial →
      shared.legacy.shared.resources.space = ELF.install file image prior →
      initial.rip = ELF.codeAddress image →
      ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
      LockedSet64.AllExecutions initial (ResultContract operation input shared initial)

theorem elf_sound {operation : Logical64.Operation} {file : List Byte} {image : ELF.Image}
    (accepted : checkELF operation file image = true) : ELFClaim operation file image := by
  obtain ⟨parsed, complete, _⟩ := checkELF_sound accepted
  refine ⟨parsed, complete, ?_⟩
  intro prior fresh input shared initial resources space entry
  exact ⟨ELF.load_success _ _ _ parsed fresh,
    semantics operation (pre_of_loaded accepted prior resources space entry)⟩

private def operationLiteral : Logical64.Operation → String
  | .intersection => ".intersection"
  | .union => ".union"
  | .symmetricDifference => ".symmetricDifference"

private def header (operation : Logical64.Operation) : String :=
  "import EDSL.AtomicSet64.Artifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedAtomicSet64\nopen X86\n\n" ++
  "/- Exact full64 LOCK AND/OR/XOR with RET and current actor/code/stack authority.\n" ++
  "Independent set membership, all AF streams, one event and exactly two retired instructions.\n" ++
  "No source memory-order, TSO, physical CPU or kernel refinement claim. -/\n\n" ++
  s!"def operation : Logical64.Operation := {operationLiteral operation}\n\n"

private def rawDeclarations (candidate : List Byte) : String :=
  s!"def observedBytes : List Byte := [{Sum32.Artifact.byteLiterals candidate}]\n\n" ++
  "theorem accepted : AtomicSet64.Artifact.checkRaw operation observedBytes = true := by decide +kernel\n\n" ++
  "theorem certified : AtomicSet64.Artifact.RawClaim operation observedBytes :=\n" ++
  "  AtomicSet64.Artifact.raw_sound accepted\n\n" ++
  "theorem runCertified : AtomicSet64.Artifact.RunClaim operation observedBytes :=\n" ++
  "  AtomicSet64.Artifact.raw_run accepted\n\n"

def rawSource (operation : Logical64.Operation) (candidate : List Byte) : String :=
  header operation ++ rawDeclarations candidate ++ "end EDSL.GeneratedAtomicSet64\n\n#audit_edsl\n"

/-- Balanced append expressions keep whole-file literals within ordinary
elaboration limits; every leaf still contains explicit typed byte literals. -/
private def appendTree : Nat → List String → String
  | _, [] => "[]"
  | _, [name] => name
  | 0, names => "(" ++ String.intercalate " ++ " names ++ ")"
  | depth + 1, names =>
    let middle := names.length / 2
    "(" ++ appendTree depth (names.take middle) ++ " ++ " ++
      appendTree depth (names.drop middle) ++ ")"

private def fileDeclarations (file : List Byte) : String := Id.run do
  let mut declarations := ""
  let mut names := []
  for index in List.range ((file.length + 63) / 64) do
    let name := s!"observedELFChunk{index}"
    let chunk := (file.drop (64 * index)).take 64
    declarations := declarations ++
      s!"def {name} : List Byte := [{Sum32.Artifact.byteLiterals chunk}]\n"
    names := name :: names
  return declarations ++ s!"\ndef observedELF : List Byte := {appendTree 16 names.reverse}\n\n" ++
    s!"theorem literalLength : observedELF.length = {file.length} := by decide +kernel\n\n"

def elfSource (operation : Logical64.Operation) (file : List Byte) (image : ELF.Image) : String :=
  header operation ++ rawDeclarations (bytes operation) ++ fileDeclarations file ++
  s!"def observedImage : ELF.Image := {Sum32.Artifact.imageLiteral image}\n\n" ++
  "theorem acceptedELF : AtomicSet64.Artifact.checkELF operation observedELF observedImage = true := by decide +kernel\n\n" ++
  "theorem loadedCertified : AtomicSet64.Artifact.ELFClaim operation observedELF observedImage :=\n" ++
  "  AtomicSet64.Artifact.elf_sound acceptedELF\n\n" ++
  "end EDSL.GeneratedAtomicSet64\n\n#audit_edsl\n"

end EDSL.AtomicSet64.Artifact
