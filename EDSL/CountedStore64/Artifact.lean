/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Accounting
import EDSL.Sum32.Artifact

set_option warningAsError true

namespace EDSL.CountedStore64.Artifact
open X86 X86.Sequential

/-- This convenience profile binds the exact complete GCC function window. -/
def check (candidate : List Byte) : Bool := decide (candidate = GCC.bytes)

theorem raw_sound {candidate : List Byte} {input initial}
    (accepted : check candidate = true) (pre : Pre candidate input initial) :
    AllExecutions initial (fun result => Post input initial result.state ∧
      result.instructions ≤ 7 * (input.count.toNat + 2)) := by
  have same : candidate = GCC.bytes := of_decide_eq_true accepted
  subst candidate
  exact GCC.raw_semantics pre

theorem raw_run {candidate : List Byte} {input initial}
    (accepted : check candidate = true) (pre : Pre candidate input initial) (choices : Choices) :
    ∃ result, Sequential.run choices (7 * (input.count.toNat + 2)) initial = .ok result ∧
      Post input initial result.state ∧ result.instructions ≤ 7 * (input.count.toNat + 2) := by
  obtain ⟨result, actual, contract⟩ := raw_sound accepted pre choices
  exact ⟨result, run_complete actual contract.2, contract⟩

theorem raw_policy {candidate : List Byte} {input initial}
    (accepted : check candidate = true) (pre : Pre candidate input initial) :
    RawPolicy candidate input initial := by
  have same : candidate = GCC.bytes := of_decide_eq_true accepted
  subst candidate
  exact GCC.raw_policy pre

theorem resource_sound {candidate : List Byte} {resource initial}
    (accepted : check candidate = true) (pre : ResourcePre candidate resource initial) :
    AllExecutions initial (fun result => Post (resourceInput resource) initial result.state ∧
      ResourceReturn resource initial result ∧
      result.instructions ≤ 7 * (resource.count.toNat + 2)) ∧ ResourcePolicy resource initial := by
  have same : candidate = GCC.bytes := of_decide_eq_true accepted
  subst candidate
  exact GCC.resource_semantics pre

theorem resource_run {candidate : List Byte} {resource initial}
    (accepted : check candidate = true) (pre : ResourcePre candidate resource initial) (choices : Choices) :
    ∃ result, Sequential.run choices (7 * (resource.count.toNat + 2)) initial = .ok result ∧
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result ∧
      result.instructions ≤ 7 * (resource.count.toNat + 2) := by
  obtain ⟨result, actual, contract⟩ := (resource_sound accepted pre).1 choices
  exact ⟨result, run_complete actual contract.2.2, contract⟩

/-- Accounting follows the same actual execution as the independent result.
The complete count, RET and original caller operand are included. -/
theorem exact_accounting {candidate : List Byte} {input initial choices result}
    (accepted : check candidate = true) (pre : Pre candidate input initial)
    (actual : Sequential.Executes choices initial result) :
    result.instructions = 6 * input.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  have same : candidate = GCC.bytes := of_decide_eq_true accepted
  subst candidate
  exact GCC.execution_exact pre actual

/-- Exact fuel is derived after totality; it is never an admission premise. -/
theorem raw_exact_run {candidate : List Byte} {input initial}
    (accepted : check candidate = true) (pre : Pre candidate input initial) (choices : Choices) :
    ∃ result, Sequential.run choices (6 * input.count.toNat + 4) initial = .ok result ∧
      Post input initial result.state ∧ result.instructions = 6 * input.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  obtain ⟨result, actual, post, _⟩ := raw_sound accepted pre choices
  obtain ⟨cost, reads⟩ := exact_accounting accepted pre actual
  exact ⟨result, run_complete actual (Nat.le_of_eq cost), post, cost, reads⟩

/-- Exact cost retains the existing coherent returned authority and frames. -/
theorem resource_exact_run {candidate : List Byte} {resource initial}
    (accepted : check candidate = true) (pre : ResourcePre candidate resource initial) (choices : Choices) :
    ∃ result, Sequential.run choices (6 * resource.count.toNat + 4) initial = .ok result ∧
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result ∧
      result.instructions = 6 * resource.count.toNat + 4 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  obtain ⟨result, actual, post, returned, _⟩ := (resource_sound accepted pre).1 choices
  obtain ⟨cost, reads⟩ := exact_accounting accepted pre.machine actual
  exact ⟨result, run_complete actual (Nat.le_of_eq cost), post, returned, cost, reads⟩

/-- Loaded literal code supplies the code premise. The complete RDX count and
all other caller bindings, current RAM and permissions remain explicit. -/
theorem pre_of_loaded {file candidate : List Byte} {image : ELF.Image} {input : Input} {initial : State}
    (checked : ELF.checkEntry file image candidate = true) (prior : OS.AddressSpace.Space)
    (memory : initial.memory = OS.AddressSpace.toMemory (ELF.install file image prior))
    (entry : initial.rip = ELF.codeAddress image)
    (pointer : initial.registers .rdi = input.address)
    (source : initial.registers .rsi = input.argument)
    (count : initial.registers .rdx = input.count)
    (oldValue : loadQWord initial.memory input.address = .ok input.oldValue)
    (writable : canStoreQWord initial.memory input.address = true)
    (codeDisjoint : QWordDisjoint input.address initial.rip candidate.length)
    (stackDisjoint : QWordDisjoint input.address (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress)
    (returnCanonical : canonical input.returnAddress = true)
    (stackBound : (initial.registers .rsp).toNat + 8 < 2^64)
    (postStackCanonical : canonical (initial.registers .rsp + 8) = true) :
    Pre candidate input initial := by
  refine ⟨⟨?_, pointer, source, oldValue, writable, codeDisjoint, stackDisjoint,
    stack, returnCanonical, stackBound, postStackCanonical⟩, count⟩
  rw [memory, entry]
  exact ELF.checked_entry_code file image candidate prior checked

private def header : String :=
  "import EDSL.CountedStore64.Artifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedCountedStore64\nopen X86 X86.Sequential CountedStore64\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  "/- Exact callable bytes: full64 counted-store result and complete target/ABI frames.\n" ++
  "Caller RAM, all-byte permissions and current OS authority remain explicit.\n" ++
  "Exact retired instructions and STACK8 reads are separate from the result contract.\n" ++
  "No source/volatile preservation, concurrent atomicity or timing claim. -/\n\n"

private def layoutSource (candidate : List Byte) : String :=
  s!"def observedBytes : List Byte := [{Sum32.Artifact.byteLiterals candidate}]\n\n" ++
  "theorem accepted : CountedStore64.Artifact.check observedBytes = true := by decide\n\n"

private def semanticSource : String :=
  "theorem exactCertified (input : CountedStore64.Input) (initial : State)\n" ++
  "    (admitted : CountedStore64.Pre observedBytes input initial) (choices : Choices) :\n" ++
  "    ∃ result, Sequential.run choices (6 * input.count.toNat + 4) initial = .ok result ∧\n" ++
  "      CountedStore64.Post input initial result.state ∧\n" ++
  "      result.instructions = 6 * input.count.toNat + 4 ∧\n" ++
  "      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] :=\n" ++
  "  CountedStore64.Artifact.raw_exact_run accepted admitted choices\n\n" ++
  "theorem resourceExactCertified (resource : CountedStore64.Resources) (initial : State)\n" ++
  "    (admitted : CountedStore64.ResourcePre observedBytes resource initial) (choices : Choices) :\n" ++
  "    ∃ result, Sequential.run choices (6 * resource.count.toNat + 4) initial = .ok result ∧\n" ++
  "      CountedStore64.Post (CountedStore64.resourceInput resource) initial result.state ∧\n" ++
  "      CountedStore64.ResourceReturn resource initial result ∧\n" ++
  "      result.instructions = 6 * resource.count.toNat + 4 ∧\n" ++
  "      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] :=\n" ++
  "  CountedStore64.Artifact.resource_exact_run accepted admitted choices\n\n" ++
  "theorem certified (input : CountedStore64.Input) (initial : State)\n" ++
  "    (admitted : CountedStore64.Pre observedBytes input initial) (choices : Choices) :\n" ++
  "    ∃ result, Sequential.run choices (7 * (input.count.toNat + 2)) initial = .ok result ∧\n" ++
  "      CountedStore64.Post input initial result.state ∧\n" ++
  "      result.instructions ≤ 7 * (input.count.toNat + 2) :=\n" ++
  "  CountedStore64.Artifact.raw_run accepted admitted choices\n\n" ++
  "theorem rawPolicy (input : CountedStore64.Input) (initial : State)\n" ++
  "    (admitted : CountedStore64.Pre observedBytes input initial) :\n" ++
  "    CountedStore64.RawPolicy observedBytes input initial :=\n" ++
  "  CountedStore64.Artifact.raw_policy accepted admitted\n\n" ++
  "theorem resourceCertified (resource : CountedStore64.Resources) (initial : State)\n" ++
  "    (admitted : CountedStore64.ResourcePre observedBytes resource initial) (choices : Choices) :\n" ++
  "    (∃ result, Sequential.run choices (7 * (resource.count.toNat + 2)) initial = .ok result ∧\n" ++
  "      CountedStore64.Post (CountedStore64.resourceInput resource) initial result.state ∧\n" ++
  "      CountedStore64.ResourceReturn resource initial result ∧\n" ++
  "      result.instructions ≤ 7 * (resource.count.toNat + 2)) ∧\n" ++
  "      CountedStore64.ResourcePolicy resource initial :=\n" ++
  "  ⟨CountedStore64.Artifact.resource_run accepted admitted choices,\n" ++
  "    (CountedStore64.Artifact.resource_sound accepted admitted).2⟩\n\n"

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
  "    (input : CountedStore64.Input) (initial : State)\n" ++
  "    (memory : initial.memory = OS.AddressSpace.toMemory (loadedSpace prior))\n" ++
  "    (entry : initial.rip = ELF.codeAddress observedImage)\n" ++
  "    (pointer : initial.registers .rdi = input.address)\n" ++
  "    (source : initial.registers .rsi = input.argument)\n" ++
  "    (count : initial.registers .rdx = input.count)\n" ++
  "    (oldValue : loadQWord initial.memory input.address = .ok input.oldValue)\n" ++
  "    (writable : canStoreQWord initial.memory input.address = true)\n" ++
  "    (codeDisjoint : QWordDisjoint input.address initial.rip observedBytes.length)\n" ++
  "    (stackDisjoint : QWordDisjoint input.address (initial.registers .rsp) 8)\n" ++
  "    (stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress)\n" ++
  "    (returnCanonical : canonical input.returnAddress = true)\n" ++
  "    (stackBound : (initial.registers .rsp).toNat + 8 < 2^64)\n" ++
  "    (postStackCanonical : canonical (initial.registers .rsp + 8) = true) (choices : Choices) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "      ∃ result, Sequential.run choices (7 * (input.count.toNat + 2)) initial = .ok result ∧\n" ++
  "        CountedStore64.Post input initial result.state ∧\n" ++
  "        result.instructions ≤ 7 * (input.count.toNat + 2) := by\n" ++
  "  refine ⟨ELF.load_success _ _ _ parsedImage free, ?_⟩\n" ++
  "  exact CountedStore64.Artifact.raw_run accepted\n" ++
  "    (CountedStore64.Artifact.pre_of_loaded checkedEntry prior memory entry pointer source count\n" ++
  "      oldValue writable codeDisjoint stackDisjoint stack returnCanonical stackBound\n" ++
  "      postStackCanonical) choices\n\n"

def rawSource (candidate : List Byte) : String :=
  header ++ layoutSource candidate ++ semanticSource ++ "end EDSL.GeneratedCountedStore64\n\n#audit_edsl\n"

def elfSource (file candidate : List Byte) (image : ELF.Image) : String :=
  header ++ layoutSource candidate ++ containerSource file image ++ semanticSource ++
    "end EDSL.GeneratedCountedStore64\n\n#audit_edsl\n"

end EDSL.CountedStore64.Artifact
