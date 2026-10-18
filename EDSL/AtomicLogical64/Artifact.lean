/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicLogical64.Contract
import EDSL.ELF.Loader
import EDSL.Sum32.Artifact

namespace EDSL.AtomicLogical64.Artifact
open X86 OS.AddressSpace

/-- Bind the COMPLETE raw routine, including RET and any suffix. -/
def checkRaw (candidate : List Byte) : Bool := decide (candidate = OS.Atomics64.Routine.bytes)

def RawClaim (candidate : List Byte) : Prop :=
  ∀ input shared initial, Pre candidate input shared initial →
    LockedLogical64.AllExecutions initial (ResultContract input shared initial)

def RunClaim (candidate : List Byte) : Prop :=
  ∀ input shared initial, Pre candidate input shared initial → ∀ choices,
    ∃ output, LockedLogical64.run choices 2 initial = .ok output ∧
      ResultContract input shared initial output

theorem raw_sound {candidate : List Byte} (accepted : checkRaw candidate = true) : RawClaim candidate := by
  have same : candidate = OS.Atomics64.Routine.bytes := of_decide_eq_true accepted
  subst candidate
  exact fun _ _ _ admitted => semantics admitted

theorem raw_run {candidate : List Byte} (accepted : checkRaw candidate = true) : RunClaim candidate := by
  have same : candidate = OS.Atomics64.Routine.bytes := of_decide_eq_true accepted
  subst candidate
  exact fun _ _ _ admitted choices => AtomicLogical64.run admitted choices

/-- This convenience ELF profile accepts exactly one executable segment,
beginning at entry, containing the complete five-byte routine and no executable
prefix, suffix or BSS. Other nonexecutable segments remain loader data. Section
names, symbol tables and disassembler/extractor output are not trusted. -/
def completeText (image : ELF.Image) : Bool :=
  match image.segments.filter ELF.Segment.executable with
  | [segment] => decide (segment.virtualAddress = image.entry ∧
      segment.fileSize = OS.Atomics64.Routine.bytes.length ∧
      segment.memorySize = OS.Atomics64.Routine.bytes.length)
  | _ => false

def checkELF (file : List Byte) (image : ELF.Image) : Bool :=
  ELF.checkParsed file image && completeText image &&
    ELF.checkEntry file image OS.Atomics64.Routine.bytes

theorem checkELF_sound {file : List Byte} {image : ELF.Image} (accepted : checkELF file image = true) :
    ELF.parse file = .ok image ∧ completeText image = true ∧
      ELF.checkEntry file image OS.Atomics64.Routine.bytes = true := by
  obtain ⟨parsedAndComplete, entry⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨parsed, complete⟩ := Bool.and_eq_true_iff.mp parsedAndComplete
  exact ⟨ELF.checkParsed_sound _ _ parsed, complete, entry⟩

theorem pre_of_loaded {file : List Byte} {image : ELF.Image} {input shared initial}
    (accepted : checkELF file image = true) (prior : Space)
    (resources : Resources OS.Atomics64.Routine.bytes input shared initial)
    (space : shared.legacy.shared.resources.space = ELF.install file image prior)
    (entry : initial.rip = ELF.codeAddress image) :
    Pre OS.Atomics64.Routine.bytes input shared initial := by
  refine ⟨resources, ?_⟩
  rw [resources.coupled, space, entry]
  exact ELF.checked_entry_code _ _ _ prior (checkELF_sound accepted).2.2

/-- Whole literal file and parsed segment metadata are bound to the callable
theorem. Fresh installation and present code/stack/actor authority stay explicit;
this does not certify process startup, OS implementation or C memory orders. -/
def ELFClaim (file : List Byte) (image : ELF.Image) : Prop :=
  ELF.parse file = .ok image ∧ completeText image = true ∧
    ∀ prior, ELF.fresh image prior = true → ∀ input shared initial,
      Resources OS.Atomics64.Routine.bytes input shared initial →
      shared.legacy.shared.resources.space = ELF.install file image prior →
      initial.rip = ELF.codeAddress image →
      ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
      LockedLogical64.AllExecutions initial (ResultContract input shared initial)

theorem elf_sound {file : List Byte} {image : ELF.Image} (accepted : checkELF file image = true) :
    ELFClaim file image := by
  obtain ⟨parsed, complete, _⟩ := checkELF_sound accepted
  refine ⟨parsed, complete, ?_⟩
  intro prior fresh input shared initial resources space entry
  exact ⟨ELF.load_success _ _ _ parsed fresh,
    semantics (pre_of_loaded accepted prior resources space entry)⟩

private def header : String :=
  "import EDSL.AtomicLogical64.Artifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedAtomicLogical64\nopen X86\n\n" ++
  "/- Exact full64 LOCK OR/RET bytes with current named actor/code/stack authority.\n" ++
  "Independent per-bit union, all AF streams, one event and two retired instructions.\n" ++
  "No source memory-order, native/kernel, TSO or physical refinement claim. -/\n\n"

private def rawDeclarations (candidate : List Byte) : String :=
  s!"def observedBytes : List Byte := [{Sum32.Artifact.byteLiterals candidate}]\n\n" ++
  "theorem accepted : AtomicLogical64.Artifact.checkRaw observedBytes = true := by decide +kernel\n\n" ++
  "theorem certified : AtomicLogical64.Artifact.RawClaim observedBytes :=\n" ++
  "  AtomicLogical64.Artifact.raw_sound accepted\n\n" ++
  "theorem runCertified : AtomicLogical64.Artifact.RunClaim observedBytes :=\n" ++
  "  AtomicLogical64.Artifact.raw_run accepted\n\n"

def rawSource (candidate : List Byte) : String :=
  header ++ rawDeclarations candidate ++ "end EDSL.GeneratedAtomicLogical64\n\n#audit_edsl\n"

/-- A bounded renderer tree keeps large literal files within ordinary
elaboration recursion limits. Leaves remain explicit typed byte literals. -/
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
    let bytes := (file.drop (64 * index)).take 64
    declarations := declarations ++
      s!"def {name} : List Byte := [{Sum32.Artifact.byteLiterals bytes}]\n"
    names := name :: names
  return declarations ++ s!"\ndef observedELF : List Byte := {appendTree 16 names.reverse}\n\n" ++
    s!"theorem literalLength : observedELF.length = {file.length} := by decide +kernel\n\n"

def elfSource (file : List Byte) (image : ELF.Image) : String :=
  header ++ rawDeclarations OS.Atomics64.Routine.bytes ++
  fileDeclarations file ++
  s!"def observedImage : ELF.Image := {Sum32.Artifact.imageLiteral image}\n\n" ++
  "theorem acceptedELF : AtomicLogical64.Artifact.checkELF observedELF observedImage = true := by decide +kernel\n\n" ++
  "theorem loadedCertified : AtomicLogical64.Artifact.ELFClaim observedELF observedImage :=\n" ++
  "  AtomicLogical64.Artifact.elf_sound acceptedELF\n\n" ++
  "end EDSL.GeneratedAtomicLogical64\n\n#audit_edsl\n"

end EDSL.AtomicLogical64.Artifact
