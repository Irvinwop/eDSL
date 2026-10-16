/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Correctness
import EDSL.ELF.Loader
import EDSL.OS.ArrayResources

namespace EDSL.Sum32.Artifact
open X86

/-- Selection errors describe the supported entry window, not defects in an
input program. A decoder rejection is kept at its actual sequential offset. -/
inductive EntryError where
  | decode (offset : Nat) (error : X86.Error)
  | byteLimit
  | instructionLimit
  deriving DecidableEq, Repr

private def entryWindowFrom (memory : Memory) (base : Word) :
    Nat → Nat → Except EntryError (List Byte)
  | 0, _ => .error .instructionLimit
  | remaining + 1, offset => do
    if offset ≥ 64 then throw .byteLimit
    let instruction ← (Sequential.decodeAt ⟨fun _ => 0,
      base + BitVec.ofNat 64 offset, 0, memory⟩).mapError (.decode offset)
    let finish := offset + instruction.length
    if finish > 64 then throw .byteLimit
    match instruction with
    | .legacy .ret =>
      (List.range finish).mapM fun index =>
        (fetchByte memory (base + BitVec.ofNat 64 index)).mapError (.decode index)
    | _ => entryWindowFrom memory base remaining finish

/-- Decode the installed candidate itself through the first RET, with explicit
64-byte/32-instruction bounds. Unsupported bytes before RET are not skipped.
Trailing container bytes are outside this callable function window; admission
by the semantic CFG checker must independently establish all reachable edges. -/
def entryWindow (file : List Byte) (image : ELF.Image) : Except EntryError (List Byte) :=
  entryWindowFrom (OS.AddressSpace.toMemory
    (ELF.install file image OS.AddressSpace.empty)) (ELF.codeAddress image) 32 0

/-- Register names and constructors come from typed data. No candidate string,
path, section name, symbol name, or disassembler output is Lean source. -/
def registerLiteral : Register → String
  | .rax => ".rax" | .rcx => ".rcx" | .rdx => ".rdx" | .rbx => ".rbx"
  | .rsp => ".rsp" | .rbp => ".rbp" | .rsi => ".rsi" | .rdi => ".rdi"
  | .r8 => ".r8" | .r9 => ".r9" | .r10 => ".r10" | .r11 => ".r11"
  | .r12 => ".r12" | .r13 => ".r13" | .r14 => ".r14" | .r15 => ".r15"

def byteLiterals (bytes : List Byte) : String :=
  String.intercalate ", " (bytes.map fun byte => toString byte.toNat)

def addressLiteral : Sequential.Address → String
  | .base register => s!"(.base {registerLiteral register})"
  | .indexed baseReg index scale =>
    s!"(.indexed {registerLiteral baseReg} {registerLiteral index} {scale.val})"

def legacyLiteral : X86.Instruction → String
  | .leaEaxRdiDisp8 value => s!"(.leaEaxRdiDisp8 {value.toNat})"
  | .leaEaxRaxDisp8 value => s!"(.leaEaxRaxDisp8 {value.toNat})"
  | .movEaxEdi => ".movEaxEdi" | .movEaxEsi => ".movEaxEsi"
  | .exchangeEaxRdi => ".exchangeEaxRdi" | .fetchAddEaxRdi => ".fetchAddEaxRdi"
  | .jrcxz value => s!"(.jrcxz {value.toNat})"
  | .loopRcx value => s!"(.loopRcx {value.toNat})"
  | .jnz value => s!"(.jnz {value.toNat})"
  | .cmpEaxZero => ".cmpEaxZero"
  | .loadEaxRdi => ".loadEaxRdi" | .loadEaxRsi => ".loadEaxRsi"
  | .storeEsiRdi => ".storeEsiRdi" | .storeEaxRsi => ".storeEaxRsi"
  | .mov32 register value => s!"(.mov32 {registerLiteral register} {value.toNat})"
  | .syscall => ".syscall" | .ret => ".ret"

def instructionLiteral : Sequential.Instruction → String
  | .legacy instruction => s!"(.legacy {legacyLiteral instruction})"
  | .xorSelf32 register => s!"(.xorSelf32 {registerLiteral register})"
  | .test64 left right => s!"(.test64 {registerLiteral left} {registerLiteral right})"
  | .cmp64 left right => s!"(.cmp64 {registerLiteral left} {registerLiteral right})"
  | .addMem32 destination address =>
    s!"(.addMem32 {registerLiteral destination} {addressLiteral address})"
  | .movReg32 destination source =>
    s!"(.movReg32 {registerLiteral destination} {registerLiteral source})"
  | .movReg64 destination source =>
    s!"(.movReg64 {registerLiteral destination} {registerLiteral source})"
  | .loadMem32 destination address =>
    s!"(.loadMem32 {registerLiteral destination} {addressLiteral address})"
  | .storeMem32 address source =>
    s!"(.storeMem32 {addressLiteral address} {registerLiteral source})"
  | .addImm64 register value => s!"(.addImm64 {registerLiteral register} {value.toNat})"
  | .inc64 register => s!"(.inc64 {registerLiteral register})"
  | .dec64 register => s!"(.dec64 {registerLiteral register})"
  | .je value => s!"(.je {value.toNat})"
  | .jmp value => s!"(.jmp {value.toNat})"

def nodeLiteral (node : Node) : String :=
  s!"⟨{node.offset}, {instructionLiteral node.instruction}⟩"

def branchLiteral (branch : Branch) : String :=
  s!"⟨{branch.offset}, {branch.displacement.toNat}⟩"

/-- Render every field of the actual discovered plan, including arbitrary
admitted MOV-zero/XOR-zero prologues and either pointer-update order. -/
def planLiteral (plan : Plan) : String :=
  let mode := match plan.mode with | .pointerCount => ".pointerCount" | .index => ".index"
  "{ mode := " ++ mode ++ ", prologue := [" ++
    String.intercalate ", " (plan.prologue.map nodeLiteral) ++
    s!"], header := {plan.header}, branch := {branchLiteral plan.branch}, load := {plan.load}, " ++
    "updates := [" ++ String.intercalate ", " (plan.updates.map nodeLiteral) ++
    s!"], back := {branchLiteral plan.back}, exit := {plan.exit}" ++ " }"

def imageLiteral (image : ELF.Image) : String :=
  let segments := String.intercalate ", " (image.segments.map fun segment =>
    s!"⟨{segment.offset}, {segment.virtualAddress}, {segment.fileSize}, " ++
      s!"{segment.memorySize}, {segment.flags}, {segment.alignment}⟩")
  s!"⟨{image.entry}, [{segments}]⟩"

private def sourceHeader : String :=
  "import EDSL.Sum32.Artifact\nimport EDSL.Audit\n\n" ++
  "namespace EDSL.GeneratedSum32\nopen X86 Sum32 OS.AddressSpace\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
  "/- Callable function contract: current caller input and return-stack RAM,\n" ++
  "resource authority, and the modeled ISA environment remain explicit.\n" ++
  "Memory is stable ordinary RAM; native CPU/kernel conformance is external.\n" ++
  "An ELF container theorem does not establish process startup or whole-ELF safety. -/\n\n"

private def layoutSource (bytes : List Byte) (plan : Plan) : String :=
  s!"def observedBytes : List Byte := [{byteLiterals bytes}]\n\n" ++
  s!"def literalPlan : Sum32.Plan := {planLiteral plan}\n\n" ++
  "theorem accepted : Sum32.check observedBytes = some literalPlan := by decide\n\n" ++
  "theorem valid : Sum32.Valid observedBytes literalPlan := Sum32.check_sound accepted\n\n"

/-- Bind the literal file, image, entry window, parser and actual loader. -/
private def containerSource (file : List Byte) (image : ELF.Image) : String :=
  s!"def observedELF : List Byte := [{byteLiterals file}]\n\n" ++
  s!"def observedImage : ELF.Image := {imageLiteral image}\n\n" ++
  "theorem parsedImage : ELF.parse observedELF = .ok observedImage :=\n" ++
  "  ELF.checkParsed_sound observedELF observedImage (by decide)\n\n" ++
  "theorem checkedEntry : ELF.checkEntry observedELF observedImage observedBytes = true := by decide\n\n" ++
  "def loadedSpace (prior : Space) : Space := ELF.install observedELF observedImage prior\n\n" ++
  "theorem loadedCode (prior : Space) : CodeAt (toMemory (loadedSpace prior))\n" ++
  "    (ELF.codeAddress observedImage) observedBytes :=\n" ++
  "  ELF.checked_entry_code observedELF observedImage observedBytes prior checkedEntry\n\n" ++
  "theorem loaded (prior : Space) (free : ELF.fresh observedImage prior = true) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ :=\n" ++
  "  ELF.load_success observedELF prior observedImage parsedImage free\n\n"

private def semanticSource : String :=
  "theorem certified (initial : State) (values : List (BitVec 32)) (target : Word)\n" ++
  "    (admitted : Sum32.Pre observedBytes initial values target) :\n" ++
  "    ∀ choices, ∃ result, Sequential.run choices (literalPlan.cost values.length) initial = .ok result ∧\n" ++
  "      Sum32.Post initial values target result.state ∧\n" ++
  "      result.instructions = literalPlan.cost values.length ∧\n" ++
  "      result.reads = Sum32.operandReads initial values :=\n" ++
  "  Sum32.sound valid admitted\n\n" ++
  "theorem resourceCertified (shared : OS.Borrowing.State) (call : OS.ArrayResources.Call)\n" ++
  "    (initial : State) (bytes : call.bytes = observedBytes)\n" ++
  "    (admitted : OS.ArrayResources.Admission shared call initial)\n" ++
  "    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)\n" ++
  "    (base : initial.registers .rdi = call.base)\n" ++
  "    (count : initial.registers .rsi = BitVec.ofNat 64 call.values.length) :\n" ++
  "    Sum32.Artifact.ResourceExecution shared call literalPlan initial := by\n" ++
  "  have validCall : Sum32.Valid call.bytes literalPlan := by rw [bytes]; exact valid\n" ++
  "  exact Sum32.Artifact.resource_sound validCall admitted entry stack base count\n\n"

private def loadedSemanticSource : String :=
  "theorem loadedCertified (prior : Space) (free : ELF.fresh observedImage prior = true)\n" ++
  "    (initial : State) (values : List (BitVec 32)) (target : Word)\n" ++
  "    (memory : initial.memory = toMemory (loadedSpace prior))\n" ++
  "    (entry : initial.rip = ELF.codeAddress observedImage)\n" ++
  "    (array : ArrayAt initial.memory (initial.registers .rdi) values)\n" ++
  "    (bound : ArrayBound (initial.registers .rdi) values)\n" ++
  "    (count : initial.registers .rsi = BitVec.ofNat 64 values.length)\n" ++
  "    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)\n" ++
  "    (canonicalTarget : canonical target = true)\n" ++
  "    (canonicalStackAfter : canonical (initial.registers .rsp + 8) = true) :\n" ++
  "    ELF.load observedELF prior = .ok ⟨observedImage, loadedSpace prior⟩ ∧\n" ++
  "      ∀ choices, ∃ result, Sequential.run choices (literalPlan.cost values.length) initial = .ok result ∧\n" ++
  "        Sum32.Post initial values target result.state ∧\n" ++
  "        result.instructions = literalPlan.cost values.length ∧\n" ++
  "        result.reads = Sum32.operandReads initial values :=\n" ++
  "  Sum32.Artifact.loaded_sound parsedImage checkedEntry valid prior free memory entry\n" ++
  "    array bound count stack canonicalTarget canonicalStackAfter\n\n"

/-- A self-contained literal certificate. Acceptance is kernel recomputed and
the semantic conclusion comes from the actual checked generic theorem. -/
def rawSource (bytes : List Byte) (plan : Plan) : String :=
  sourceHeader ++ layoutSource bytes plan ++ semanticSource ++
    "end EDSL.GeneratedSum32\n\n#audit_edsl\n"

def elfSource (file bytes : List Byte) (image : ELF.Image) (plan : Plan) : String :=
  sourceHeader ++ layoutSource bytes plan ++ containerSource file image ++ semanticSource ++
    loadedSemanticSource ++ "end EDSL.GeneratedSum32\n\n#audit_edsl\n"

/-- Current OS authority supplies the mathematical machine precondition only
with explicit full RAM and ABI argument/entry bindings. Code equality alone
does not manufacture resource admission. -/
theorem pre_of_admission {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : X86.State} (admitted : OS.ArrayResources.Admission shared call initial)
    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)
    (base : initial.registers .rdi = call.base)
    (count : initial.registers .rsi = BitVec.ofNat 64 call.values.length) :
    Pre call.bytes initial call.values call.target := by
  obtain ⟨code, returned, array⟩ := admitted.current
  refine ⟨?_, ?_, ?_, count, ?_, admitted.resources.returnCanonical, ?_⟩
  · simpa only [entry] using code
  · simpa only [base] using array
  · simpa only [base] using admitted.resources.bound
  · simpa only [stack] using returned
  · simpa only [stack] using admitted.resources.postStackCanonical

/-- The independent footprint describes exact successive four-byte operands.
This bridge turns its list membership into a current OS loan subregion. -/
theorem inputReads_member {base : Word} {values : List (BitVec 32)}
    {read : Sequential.Read} (member : read ∈ inputReads base values) :
    read.kind = .data ∧ read.bytes = 4 ∧
      ∃ index, index < values.length ∧ read.address = base + BitVec.ofNat 64 (4 * index) := by
  induction values generalizing base with
  | nil => cases member
  | cons value rest induction =>
    rcases List.mem_cons.mp member with head | tail
    · subst read
      exact ⟨rfl, rfl, 0, by simp, by simp⟩
    · obtain ⟨kind, width, index, inside, address⟩ := induction tail
      refine ⟨kind, width, index + 1, by simpa using Nat.succ_lt_succ inside, ?_⟩
      rw [address]
      simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
      rw [BitVec.add_assoc]
      exact congrArg (fun value : Word => base + value) (BitVec.add_comm _ _)

theorem operandReads_permission {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : State} (admitted : OS.ArrayResources.Admission shared call initial)
    (base : initial.registers .rdi = call.base) (stack : initial.registers .rsp = call.stack)
    {read : Sequential.Read} (member : read ∈ operandReads initial call.values) :
    OS.ArrayResources.ReadPermission shared call.worker read := by
  change read ∈ inputReads (initial.registers .rdi) call.values ++
    [⟨.stack, initial.registers .rsp, 8⟩] at member
  rw [base, stack] at member
  rcases List.mem_append.mp member with data | returned
  · exact OS.ArrayResources.arrayRead_permission admitted.resources (inputReads_member data)
  · have same := List.mem_singleton.mp returned
    subst read
    exact OS.ArrayResources.stackRead_permission admitted.resources

/-- All-choice completion, the common mathematical/ABI/memory contract, exact
cost/footprint, retained current admission, and permission for actual reads. -/
def ResourceExecution (shared : OS.Borrowing.State) (call : OS.ArrayResources.Call)
    (plan : Plan) (initial : State) : Prop :=
  ∀ choices, ∃ result, Sequential.run choices (plan.cost call.values.length) initial = .ok result ∧
    Post initial call.values call.target result.state ∧
    result.instructions = plan.cost call.values.length ∧
    result.reads = operandReads initial call.values ∧
    OS.ArrayResources.Admission shared call result.state ∧
    ∀ read ∈ result.reads, OS.ArrayResources.ReadPermission shared call.worker read

theorem resource_sound {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {plan : Plan} {initial : State} (valid : Valid call.bytes plan)
    (admitted : OS.ArrayResources.Admission shared call initial)
    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)
    (base : initial.registers .rdi = call.base)
    (count : initial.registers .rsi = BitVec.ofNat 64 call.values.length) :
    ResourceExecution shared call plan initial := by
  intro choices
  obtain ⟨result, execution, post, cost, reads⟩ :=
    Sum32.sound valid (pre_of_admission admitted entry stack base count) choices
  refine ⟨result, execution, post, cost, reads, admitted.unchangedMemory post.memory, ?_⟩
  intro read member
  exact operandReads_permission admitted base stack (by simpa only [reads] using member)

/-- The same function theorem at the actual installed ELF entry. The caller
supplies current input/stack RAM; a container does not establish their validity
or a process-startup ABI. The parser and full-file loader are checked too. -/
theorem loaded_sound {file bytes : List Byte} {image : ELF.Image} {plan : Plan}
    (parsed : ELF.parse file = .ok image) (checked : ELF.checkEntry file image bytes = true)
    (valid : Valid bytes plan) (prior : OS.AddressSpace.Space)
    (free : ELF.fresh image prior = true) {initial : State} {values : List (BitVec 32)} {target : Word}
    (memory : initial.memory = OS.AddressSpace.toMemory (ELF.install file image prior))
    (entry : initial.rip = ELF.codeAddress image)
    (array : ArrayAt initial.memory (initial.registers .rdi) values)
    (bound : ArrayBound (initial.registers .rdi) values)
    (count : initial.registers .rsi = BitVec.ofNat 64 values.length)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true)
    (canonicalStackAfter : canonical (initial.registers .rsp + 8) = true) :
    ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
      ∀ choices, ∃ result, Sequential.run choices (plan.cost values.length) initial = .ok result ∧
        Post initial values target result.state ∧ result.instructions = plan.cost values.length ∧
        result.reads = operandReads initial values := by
  have code : CodeAt initial.memory initial.rip bytes := by
    rw [memory, entry]
    exact ELF.checked_entry_code file image bytes prior checked
  exact ⟨ELF.load_success file prior image parsed free,
    Sum32.sound valid ⟨code, array, bound, count, stack, canonicalTarget, canonicalStackAfter⟩⟩

end EDSL.Sum32.Artifact
