/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.Resources
import EDSL.Sum32.Artifact

set_option warningAsError true

namespace EDSL.StoreReturn32.Artifact
open X86 X86.Sequential

theorem raw_sound {candidate : List Byte} {shape : Shape} {input initial}
    (accepted : check candidate = some shape)
    (pre : Grading.Write32.Pre candidate input initial) :
    AllExecutions initial (ResultContract input initial) ∧
      Grading.Write32.RawPolicy candidate input initial := by
  have same := check_sound accepted
  subst candidate
  exact raw_semantics pre

theorem raw_run {candidate : List Byte} {shape : Shape} {input initial}
    (accepted : check candidate = some shape)
    (pre : Grading.Write32.Pre candidate input initial) (choices : Choices) :
    ∃ result, Sequential.run choices 3 initial = .ok result ∧ ResultContract input initial result :=
  AllExecutions.run (raw_sound accepted pre).1 (fun _ contract => contract.2.1) choices

theorem resource_sound {candidate : List Byte} {shape : Shape} {resource initial}
    (accepted : check candidate = some shape)
    (pre : Grading.Write32.ResourcePre candidate resource initial) :
    AllExecutions initial (fun result =>
      ResultContract (Grading.Write32.resourceInput resource) initial result ∧
      Grading.Write32.ResourceReturn resource initial result) ∧
      Grading.Write32.ResourcePolicy resource initial := by
  have same := check_sound accepted
  subst candidate
  exact resource_semantics pre

theorem resource_run {candidate : List Byte} {shape : Shape} {resource initial}
    (accepted : check candidate = some shape)
    (pre : Grading.Write32.ResourcePre candidate resource initial) (choices : Choices) :
    ∃ result, Sequential.run choices 3 initial = .ok result ∧
      ResultContract (Grading.Write32.resourceInput resource) initial result ∧
      Grading.Write32.ResourceReturn resource initial result :=
  AllExecutions.run (resource_sound accepted pre).1 (fun _ contract => contract.1.2.1) choices

/-- The actual installed code supplies the code premise. All remaining fields
are present caller data, permissions and ABI facts, without future execution. -/
theorem pre_of_loaded {file bytes : List Byte} {image : ELF.Image}
    {input : Grading.Write32.Input} {initial : State}
    (checked : ELF.checkEntry file image bytes = true) (prior : OS.AddressSpace.Space)
    (memory : initial.memory = OS.AddressSpace.toMemory (ELF.install file image prior))
    (entry : initial.rip = ELF.codeAddress image)
    (pointer : initial.registers .rdi = input.address)
    (source : initial.registers .rsi = input.argument)
    (oldValue : loadDWord initial.memory input.address = .ok input.oldValue)
    (writable : canStoreDWord initial.memory input.address = true)
    (codeDisjoint : DWordDisjoint input.address initial.rip bytes.length)
    (stackDisjoint : DWordDisjoint input.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress)
    (returnCanonical : canonical input.returnAddress = true)
    (stackBound : (initial.registers .rsp).toNat + 8 < 2^64)
    (postStackCanonical : canonical (initial.registers .rsp + 8) = true) :
    Grading.Write32.Pre bytes input initial := by
  refine ⟨?_, pointer, source, oldValue, writable, codeDisjoint, stackDisjoint,
    stack, returnCanonical, stackBound, postStackCanonical⟩
  rw [memory, entry]
  exact ELF.checked_entry_code file image bytes prior checked

private def shapeLiteral : Shape → String
  | .storeCopy => ".storeCopy"
  | .copyStore => ".copyStore"
  | .copyStoreRax => ".copyStoreRax"

private def header : String :=
  "import EDSL.StoreReturn32.Artifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedStoreReturn32\nopen X86 X86.Sequential StoreReturn32\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  "/- Callable function result: low32 store, full returned pointer and frames.\n" ++
  "Present caller RAM, permissions, ABI and current OS resources remain explicit.\n" ++
  "Native CPU/kernel conformance, source preservation and process startup are external.\n" ++
  "Exact instruction accounting does not establish global operation optimality. -/\n\n"

private def layoutSource (bytes : List Byte) (shape : Shape) : String :=
  s!"def observedBytes : List Byte := [{Sum32.Artifact.byteLiterals bytes}]\n\n" ++
  s!"def selectedShape : StoreReturn32.Shape := {shapeLiteral shape}\n\n" ++
  "theorem accepted : StoreReturn32.check observedBytes = some selectedShape := by decide\n\n"

private def semanticSource : String :=
  "theorem certified (input : Grading.Write32.Input) (initial : State)\n" ++
  "    (admitted : Grading.Write32.Pre observedBytes input initial) (choices : Choices) :\n" ++
  "    ∃ result, Sequential.run choices 3 initial = .ok result ∧\n" ++
  "      StoreReturn32.ResultContract input initial result :=\n" ++
  "  StoreReturn32.Artifact.raw_run accepted admitted choices\n\n" ++
  "theorem rawPolicy (input : Grading.Write32.Input) (initial : State)\n" ++
  "    (admitted : Grading.Write32.Pre observedBytes input initial) :\n" ++
  "    Grading.Write32.RawPolicy observedBytes input initial :=\n" ++
  "  (StoreReturn32.Artifact.raw_sound accepted admitted).2\n\n" ++
  "theorem resourceCertified (resource : Grading.Write32.Resources) (initial : State)\n" ++
  "    (admitted : Grading.Write32.ResourcePre observedBytes resource initial) (choices : Choices) :\n" ++
  "    (∃ result, Sequential.run choices 3 initial = .ok result ∧\n" ++
  "      StoreReturn32.ResultContract (Grading.Write32.resourceInput resource) initial result ∧\n" ++
  "      Grading.Write32.ResourceReturn resource initial result) ∧\n" ++
  "      Grading.Write32.ResourcePolicy resource initial :=\n" ++
  "  ⟨StoreReturn32.Artifact.resource_run accepted admitted choices,\n" ++
  "    (StoreReturn32.Artifact.resource_sound accepted admitted).2⟩\n\n"

private def containerSource (file : List Byte) (image : ELF.Image) : String :=
  s!"def observedELF : List Byte := [{Sum32.Artifact.byteLiterals file}]\n\n" ++
  s!"def observedImage : ELF.Image := {Sum32.Artifact.imageLiteral image}\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  "def loadedSpace (prior : OS.AddressSpace.Space) := ELF.install observedELF observedImage prior\n\n" ++
  "theorem loadedCode (prior : OS.AddressSpace.Space) :\n" ++
  "    CodeAt (OS.AddressSpace.toMemory (loadedSpace prior))\n" ++
  "      (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem loadedCertified (prior : OS.AddressSpace.Space)\n" ++
  "    (free : ELF.fresh observedImage prior = true)\n" ++
  "    (input : Grading.Write32.Input) (initial : State)\n" ++
  "    (memory : initial.memory = OS.AddressSpace.toMemory (loadedSpace prior))\n" ++
  "    (entry : initial.rip = ELF.codeAddress observedImage)\n" ++
  "    (pointer : initial.registers .rdi = input.address)\n" ++
  "    (source : initial.registers .rsi = input.argument)\n" ++
  "    (oldValue : loadDWord initial.memory input.address = .ok input.oldValue)\n" ++
  "    (writable : canStoreDWord initial.memory input.address = true)\n" ++
  "    (codeDisjoint : DWordDisjoint input.address initial.rip observedBytes.length)\n" ++
  "    (stackDisjoint : DWordDisjoint input.address (initial.registers .rsp) 8)\n" ++
  "    (stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress)\n" ++
  "    (returnCanonical : canonical input.returnAddress = true)\n" ++
  "    (stackBound : (initial.registers .rsp).toNat + 8 < 2^64)\n" ++
  "    (postStackCanonical : canonical (initial.registers .rsp + 8) = true) (choices : Choices) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "      ∃ result, Sequential.run choices 3 initial = .ok result ∧\n" ++
  "        StoreReturn32.ResultContract input initial result := by\n" ++
  "  refine ⟨ELF.load_success _ _ _ parsedImage free, ?_⟩\n" ++
  "  exact StoreReturn32.Artifact.raw_run accepted\n" ++
  "    (StoreReturn32.Artifact.pre_of_loaded checkedEntry prior memory entry pointer source\n" ++
  "      oldValue writable codeDisjoint stackDisjoint stack returnCanonical stackBound\n" ++
  "      postStackCanonical) choices\n\n"

/-- Literal certificate text uses typed bytes, shape and image fields only. -/
def rawSource (bytes : List Byte) (shape : Shape) : String :=
  header ++ layoutSource bytes shape ++ semanticSource ++
    "end EDSL.GeneratedStoreReturn32\n\n#audit_edsl\n"

def elfSource (file bytes : List Byte) (image : ELF.Image) (shape : Shape) : String :=
  header ++ layoutSource bytes shape ++ containerSource file image ++ semanticSource ++
    "end EDSL.GeneratedStoreReturn32\n\n#audit_edsl\n"

end EDSL.StoreReturn32.Artifact
