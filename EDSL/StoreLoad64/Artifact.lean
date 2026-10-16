/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreLoad64
import EDSL.Sum32.Artifact

set_option warningAsError true

namespace EDSL.StoreLoad64.Artifact
open X86 X86.Sequential

/-- The direct convenience profile binds the complete seven-byte function. -/
def check (candidate : List Byte) : Bool := decide (candidate = StoreLoad64.bytes)

theorem raw_sound {candidate : List Byte} {input initial}
    (accepted : check candidate = true) (pre : Pre candidate input initial) :
    AllExecutions initial (ResultContract input initial) := by
  have same : candidate = StoreLoad64.bytes := of_decide_eq_true accepted
  subst candidate
  exact raw_semantics pre

theorem raw_run {candidate : List Byte} {input initial}
    (accepted : check candidate = true) (pre : Pre candidate input initial) (choices : Choices) :
    ∃ result, Sequential.run choices 3 initial = .ok result ∧ ResultContract input initial result :=
  AllExecutions.run (raw_sound accepted pre) (fun _ contract => contract.2.1) choices

theorem resource_sound {candidate : List Byte} {resource initial}
    (accepted : check candidate = true) (pre : ResourcePre candidate resource initial) :
    AllExecutions initial (fun result => ResultContract (resourceInput resource) initial result ∧
      ResourceReturn resource initial result) ∧ ResourcePolicy resource initial := by
  have same : candidate = StoreLoad64.bytes := of_decide_eq_true accepted
  subst candidate
  exact resource_semantics pre

theorem resource_run {candidate : List Byte} {resource initial}
    (accepted : check candidate = true) (pre : ResourcePre candidate resource initial) (choices : Choices) :
    ∃ result, Sequential.run choices 3 initial = .ok result ∧
      ResultContract (resourceInput resource) initial result ∧ ResourceReturn resource initial result :=
  AllExecutions.run (resource_sound accepted pre).1 (fun _ contract => contract.1.2.1) choices

/-- Installed literal code supplies the code premise; all remaining premises
are present caller memory, permissions and ABI facts. -/
theorem pre_of_loaded {file candidate : List Byte} {image : ELF.Image} {input : Input} {initial : State}
    (checked : ELF.checkEntry file image candidate = true) (prior : OS.AddressSpace.Space)
    (memory : initial.memory = OS.AddressSpace.toMemory (ELF.install file image prior))
    (entry : initial.rip = ELF.codeAddress image)
    (pointer : initial.registers .rdi = input.address)
    (source : initial.registers .rsi = input.argument)
    (oldValue : loadQWord initial.memory input.address = .ok input.oldValue)
    (writable : canStoreQWord initial.memory input.address = true)
    (codeDisjoint : QWordDisjoint input.address initial.rip candidate.length)
    (stackDisjoint : QWordDisjoint input.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress)
    (returnCanonical : canonical input.returnAddress = true)
    (stackBound : (initial.registers .rsp).toNat + 8 < 2^64)
    (postStackCanonical : canonical (initial.registers .rsp + 8) = true) :
    Pre candidate input initial := by
  refine ⟨?_, pointer, source, oldValue, writable, codeDisjoint, stackDisjoint,
    stack, returnCanonical, stackBound, postStackCanonical⟩
  rw [memory, entry]
  exact ELF.checked_entry_code file image candidate prior checked

private def header : String :=
  "import EDSL.StoreLoad64.Artifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedStoreLoad64\nopen X86 X86.Sequential StoreLoad64\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  "/- Exact callable bytes: full64 store/load result, ABI and memory frames.\n" ++
  "Caller RAM, all-byte permissions and current OS authority remain explicit.\n" ++
  "No source/volatile preservation, concurrent atomicity or timing claim. -/\n\n"

private def layoutSource (candidate : List Byte) : String :=
  s!"def observedBytes : List Byte := [{Sum32.Artifact.byteLiterals candidate}]\n\n" ++
  "theorem accepted : StoreLoad64.Artifact.check observedBytes = true := by decide\n\n"

private def semanticSource : String :=
  "theorem certified (input : StoreLoad64.Input) (initial : State)\n" ++
  "    (admitted : StoreLoad64.Pre observedBytes input initial) (choices : Choices) :\n" ++
  "    ∃ result, Sequential.run choices 3 initial = .ok result ∧\n" ++
  "      StoreLoad64.ResultContract input initial result :=\n" ++
  "  StoreLoad64.Artifact.raw_run accepted admitted choices\n\n" ++
  "theorem resourceCertified (resource : StoreLoad64.Resources) (initial : State)\n" ++
  "    (admitted : StoreLoad64.ResourcePre observedBytes resource initial) (choices : Choices) :\n" ++
  "    (∃ result, Sequential.run choices 3 initial = .ok result ∧\n" ++
  "      StoreLoad64.ResultContract (StoreLoad64.resourceInput resource) initial result ∧\n" ++
  "      StoreLoad64.ResourceReturn resource initial result) ∧\n" ++
  "      StoreLoad64.ResourcePolicy resource initial :=\n" ++
  "  ⟨StoreLoad64.Artifact.resource_run accepted admitted choices,\n" ++
  "    (StoreLoad64.Artifact.resource_sound accepted admitted).2⟩\n\n"

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
  "    (input : StoreLoad64.Input) (initial : State)\n" ++
  "    (memory : initial.memory = OS.AddressSpace.toMemory (loadedSpace prior))\n" ++
  "    (entry : initial.rip = ELF.codeAddress observedImage)\n" ++
  "    (pointer : initial.registers .rdi = input.address)\n" ++
  "    (source : initial.registers .rsi = input.argument)\n" ++
  "    (oldValue : loadQWord initial.memory input.address = .ok input.oldValue)\n" ++
  "    (writable : canStoreQWord initial.memory input.address = true)\n" ++
  "    (codeDisjoint : QWordDisjoint input.address initial.rip observedBytes.length)\n" ++
  "    (stackDisjoint : QWordDisjoint input.address (initial.registers .rsp) 8)\n" ++
  "    (stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress)\n" ++
  "    (returnCanonical : canonical input.returnAddress = true)\n" ++
  "    (stackBound : (initial.registers .rsp).toNat + 8 < 2^64)\n" ++
  "    (postStackCanonical : canonical (initial.registers .rsp + 8) = true) (choices : Choices) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "      ∃ result, Sequential.run choices 3 initial = .ok result ∧\n" ++
  "        StoreLoad64.ResultContract input initial result := by\n" ++
  "  refine ⟨ELF.load_success _ _ _ parsedImage free, ?_⟩\n" ++
  "  exact StoreLoad64.Artifact.raw_run accepted\n" ++
  "    (StoreLoad64.Artifact.pre_of_loaded checkedEntry prior memory entry pointer source\n" ++
  "      oldValue writable codeDisjoint stackDisjoint stack returnCanonical stackBound\n" ++
  "      postStackCanonical) choices\n\n"

def rawSource (candidate : List Byte) : String :=
  header ++ layoutSource candidate ++ semanticSource ++ "end EDSL.GeneratedStoreLoad64\n\n#audit_edsl\n"

def elfSource (file candidate : List Byte) (image : ELF.Image) : String :=
  header ++ layoutSource candidate ++ containerSource file image ++ semanticSource ++
    "end EDSL.GeneratedStoreLoad64\n\n#audit_edsl\n"

end EDSL.StoreLoad64.Artifact
