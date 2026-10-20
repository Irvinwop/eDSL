/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PureCall
import EDSL.X86.VCGen.BufferCall
import EDSL.X86.VCGen.Frame
import EDSL.X86.VCGen.Artifact
import EDSL.X86.VCGen.Tactics
import EDSL.OS.CallResources.Domain
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

deriving instance DecidableEq for Except

namespace EDSL.Tests.CFGProfiles
open X86 X86.Sequential OS

/-- An explicit reusable static profile; execution fuel is supplied separately. -/
def roomy : CFG.Profile := ⟨96, 96, by decide⟩

namespace Loop

-- Owned literal 68-byte window, independent of the instruction encoders.
-- Eight padding instructions precede MOV RAX,RCX; LOOP MOV; RET.
-- The reachable LOOP and RET begin at offsets 65 and 67.
def bytes : List Byte :=
  (List.replicate 6 [0x66,0x0f,0x1f,0x84,0,0,0,0,0]).flatten ++
  [0x0f,0x1f,0x44,0,0, 0x0f,0x1f,0, 0x48,0x89,0xc8, 0xe2,0xfb, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .nop .nine, true, 11⟩, ⟨9, .nop .nine, false, 10⟩,
  ⟨18, .nop .nine, false, 9⟩, ⟨27, .nop .nine, false, 8⟩,
  ⟨36, .nop .nine, false, 7⟩, ⟨45, .nop .nine, false, 6⟩,
  ⟨54, .nop .five, false, 5⟩, ⟨59, .nop .three, false, 4⟩,
  ⟨62, .movReg64 .rax .rcx, true, 3⟩,
  ⟨65, .legacy (.loopRcx 0xfb), false, 2⟩,
  ⟨67, .legacy .ret, false, 1⟩], 11⟩

abbrev entry : graph.Index := ⟨0, by decide⟩
abbrev header : graph.Index := ⟨8, by decide⟩
abbrev exit : graph.Index := ⟨10, by decide⟩

theorem discovered : CFG.analyzeWith roomy bytes = .ok graph := by rfl
theorem valid : CFG.Valid bytes graph roomy := CFG.analyzeWith_sound discovered

-- The original API cannot silently select a larger profile from this input.
example : CFG.analyze bytes = .error .byteLimit := by rfl
example : CFG.check bytes graph = false := by decide
example : ¬ CFG.Valid bytes graph := by
  intro admitted
  have bound := admitted.byteBound
  change 68 ≤ 64 at bound
  omega

-- Each cap is enforced independently of structural validity and of fuel.
example : CFG.analyzeWith ⟨67, 96, by decide⟩ bytes = .error .byteLimit := by rfl
example : CFG.checkWith ⟨67, 96, by decide⟩ bytes graph = false := by decide
example : CFG.analyzeWith ⟨96, 10, by decide⟩ bytes = .error .instructionLimit := by rfl
example : CFG.checkWith ⟨96, 10, by decide⟩ bytes graph = false := by decide

-- Independent malformed certificates: omitted suffix and overlapping spans.
example : CFG.checkWith roomy bytes { graph with nodes := graph.nodes.take 10 } = false := by decide
example : CFG.checkWith roomy bytes { graph with nodes := graph.nodes.map fun node =>
    if node.offset = 59 then { node with offset := 58 } else node } = false := by decide

-- Mutating bytes beyond the old boundary cannot reuse the original graph.
-- -4 branches into MOV's operand; -128 wraps below the selected window.
example : CFG.checkWith roomy (bytes.set 66 0xfc) graph = false := by decide
example : CFG.analyzeWith roomy (bytes.set 66 0xfc) = .error .invalidGraph := by rfl
example : CFG.analyzeWith roomy (bytes.set 66 0x80) = .error .invalidGraph := by rfl
example : CFG.analyzeWith roomy (bytes.set 67 0x90) = .error .invalidGraph := by rfl

-- Cap changes retain every-node decode, read-only, and depth obligations.
example : CFG.checkWith roomy bytes { graph with nodes := graph.nodes.map fun node =>
    if node.offset = 62 then { node with instruction := .movReg64 .rax .rdi } else node } = false := by decide
example : CFG.checkWith roomy bytes { graph with nodes := graph.nodes.map fun node =>
    { node with depth := 0 } } = false := by decide
example : CFG.analyzeWith roomy [0x89,0x37,0xc3] = .error (.unsupportedInstruction 0) := by rfl
example : CFG.analyzeWith roomy [0x0f,0x05] = .error (.unsupportedInstruction 0) := by rfl
example : CFG.analyzeWith roomy [0x87,0x07,0xc3] = .error (.unsupportedInstruction 0) := by rfl

/-- Independent callable result: any positive RCX count returns one, with
the original caller, complete RAM, callee-saved registers, and all flags. -/
def Post (initial : State) (target : Word) (final : State) : Prop :=
  final.registers .rax = 1 ∧ final.registers .rcx = 0 ∧
  final.registers .rsp = initial.registers .rsp + 8 ∧ final.rip = target ∧
  final.memory = initial.memory ∧
  (∀ register ∈ EDSL.PureCall.calleeSaved, final.registers register = initial.registers register) ∧
  final.flags = initial.flags

def AllowedRead (initial : State) (_ : State) (read : Read) : Prop :=
  EDSL.PureCall.RawRead initial read

def Inv (initial : State) (_ : graph.Index) (state : State) : Prop :=
  state.memory = initial.memory ∧ state.registers .rsp = initial.registers .rsp ∧
  state.registers .rcx ≠ 0 ∧
  (∀ register ∈ EDSL.PureCall.calleeSaved, state.registers register = initial.registers register) ∧
  state.flags = initial.flags

def rank (node : graph.Index) (state : State) : Nat :=
  (state.registers .rcx).toNat + if node.val = 0 then 1 else 0

def annotations (initial : State) (base target : Word)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (Final : State → Prop)
    (project : ∀ final, Post initial target final → Final final) :
    VCGen.Cutpoints.Annotations bytes graph base Final (AllowedRead initial) where
  Inv := Inv initial
  rank := rank
  blocks cut state isCut binding admitted := by
    have onlyCuts : ∀ node : graph.Index, graph.cutpoint node = true →
        node = entry ∨ node = header := by decide
    obtain ⟨memory, rsp, nonzero, saved, flags⟩ := admitted
    rcases onlyCuts cut isCut with atEntry | atHeader
    · subst cut
      have pc : state.rip = base := by simpa [CFG.Graph.node, graph] using binding.2
      change VCGen.Cutpoints.wp graph base Final (AllowedRead initial)
        (Inv initial) rank (rank entry state) 12 entry state
      vcgen_block graph entry simp [pc, BitVec.add_assoc]
      simp [Inv, rank, memory, rsp, flags]
      exact ⟨nonzero, saved⟩
    · subst cut
      have pc : state.rip = base + 62 := by simpa [CFG.Graph.node, graph] using binding.2
      have canonicalHeader : canonical (base + (62#64)) = true :=
        valid.canonical_node binding.1 header
      have decreased : (state.registers .rcx - (1#64)).toNat < (state.registers .rcx).toNat := by
        have positive : 0 < (state.registers .rcx).toNat := by
          have naturalNonzero : (state.registers .rcx).toNat ≠ 0 := by
            intro zero
            apply nonzero
            apply BitVec.eq_of_toNat_eq
            simpa using zero
          omega
        have oneLe : (1#64) ≤ state.registers .rcx := by
          change 1 ≤ (state.registers .rcx).toNat
          omega
        rw [BitVec.toNat_sub_of_le oneLe]
        change (state.registers .rcx).toNat - 1 < (state.registers .rcx).toNat
        omega
      by_cases last : state.registers .rcx - 1 = 0
      · have one : state.registers .rcx = 1 :=
          (BitVec.sub_eq_iff_eq_add.mp last).trans (by decide)
        change VCGen.Cutpoints.wp graph base Final (AllowedRead initial)
          (Inv initial) rank (rank header state) 4 header state
        vcgen_block graph header simp [AllowedRead, EDSL.PureCall.RawRead,
          pc, memory, rsp, stack, canonicalTarget, one, BitVec.add_assoc]
        apply project
        simp [Post, flags, EDSL.PureCall.calleeSaved]
        simpa [EDSL.PureCall.calleeSaved] using saved
      · change VCGen.Cutpoints.wp graph base Final (AllowedRead initial)
          (Inv initial) rank (rank header state) 4 header state
        have condition : state.registers .rcx - (1#64) ≠ (0#64) := last
        vcgen_block graph header simp [AllowedRead, pc, memory, condition,
          canonicalHeader, BitVec.add_assoc]
        simp [Inv, rank, rsp, condition, flags, EDSL.PureCall.calleeSaved]
        constructor
        · simpa [EDSL.PureCall.calleeSaved] using saved
        · simpa only [BitVec.toNat_sub, BitVec.toNat_ofNat] using decreased

/-- Dynamic rank covers all positive 64-bit counters, not a static input cap. -/
theorem total (initial : State) (base target : Word)
    (code : CodeAt initial.memory base bytes) (pc : initial.rip = base)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (positive : initial.registers .rcx ≠ 0)
    (choices : Choices) :
    ∃ result, Sequential.run choices (12 * ((initial.registers .rcx).toNat + 2)) initial = .ok result ∧
      Post initial target result.state ∧
      result.instructions ≤ 12 * ((initial.registers .rcx).toNat + 2) := by
  have binding : CFG.At bytes graph base entry initial :=
    ⟨code, by simpa [graph, CFG.Graph.node] using pc⟩
  simpa [annotations, rank, graph, Nat.add_assoc] using
    (annotations initial base target stack canonicalTarget (Post initial target) (fun _ => id)).sound valid
      (entry := entry) rfl binding ⟨rfl, rfl, positive, fun _ _ => rfl, rfl⟩ choices

end Loop

namespace Call
open EDSL.PureCall

/-- Mathematical contract for the positive-count loop. It does not mention
padding, instruction counts, graph nodes, or a future successful execution. -/
def spec : Spec where
  Input := Word
  arguments value index := if index.val = 3 then some (.word64 value) else none
  domain value := value ≠ 0
  result _ value := value = 1
  useful value := 1 < value.toNat

theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) Loop.bytes := by
  apply VCGen.pureCall_semantics_of_cutpoints spec Loop.bytes Loop.graph Loop.valid
  intro input initial pre
  have count : initial.registers .rcx = input.value := by
    exact pre.arguments ⟨3, by decide⟩ (.word64 input.value) rfl
  have positive : initial.registers .rcx ≠ 0 := by rw [count]; exact pre.domain
  let annotations := Loop.annotations initial initial.rip input.returnAddress pre.stack pre.returnCanonical
    (Post spec input initial) (fun _ post =>
      ⟨post.1, post.2.2.2.2.1, post.2.2.2.1, post.2.2.1,
        post.2.2.2.2.2.1, congrArg (fun flags => flags &&& ~~~arithmeticFlagMask) post.2.2.2.2.2.2⟩)
  refine ⟨annotations, rfl, rfl, positive, fun _ _ => rfl, rfl⟩

def codeBase : Word := 0x401320
def stackBase : Word := 0x700008
def continuation : Word := 0x654321

def space : AddressSpace.Space where
  cells address :=
    if (⟨codeBase, Loop.bytes.length⟩ : AddressSpace.Region).Contains address then
      (Loop.bytes[address.toNat - codeBase.toNat]?).map fun byte => ⟨byte, AddressSpace.readExecute⟩
    else if (⟨stackBase, 8⟩ : AddressSpace.Region).Contains address then
      some ⟨continuation.extractLsb' ((address.toNat - stackBase.toNat) * 8) 8, AddressSpace.readOnly⟩
    else if address = 0x900000 then some ⟨0xa5, AddressSpace.readWrite⟩
    else none

def declared : CallResources.Domain.Initial :=
  ⟨space, 17, 29, 41, codeBase, Loop.bytes, stackBase, continuation⟩

theorem present : CallResources.Domain.Facts declared :=
  CallResources.Domain.check_sound (by decide)

def resource (count : Word) : Resources spec :=
  ⟨CallResources.Domain.shared declared, CallResources.Domain.call declared, count⟩

def caller (count : Word) (registers : Register → Word) (flags : Word) : State :=
  CallResources.Domain.machine declared
    (fun register => if register = .rcx then count else registers register) flags

theorem admitted (count : Word) (registers : Register → Word) (flags : Word) (positive : count ≠ 0) :
    ResourcePre spec Loop.bytes (resource count) (caller count registers flags) := by
  refine ⟨CallResources.Domain.current present _ _, rfl, rfl, ?_, positive, ?_⟩
  · simp [caller, CallResources.Domain.machine, declared, resource, CallResources.Domain.call]
  · intro index argument binding
    change (if index.val = 3 then some (Argument.word64 count) else none) = some argument at binding
    split at binding
    · have indexThree : index = ⟨3, by decide⟩ := Fin.ext (by assumption)
      subst index
      cases binding
      simp [Argument.Holds, caller, CallResources.Domain.machine, argumentRegister]
    · contradiction

/-- The exact 68-byte program reaches the original caller with original code
and stack loans. The same authority also holds at every continuing prefix. -/
theorem resources_survive (count : Word) (registers : Register → Word) (flags : Word)
    (positive : count ≠ 0) :
    AllExecutions (caller count registers flags) (fun result =>
      Post spec (resourceInput (resource count)) (caller count registers flags) result.state ∧
      CallResources.Current (resource count).call (resource count).shared result.state) ∧
    Grading.ReadOnlyPolicy (caller count registers flags)
      (CallResources.Current (resource count).call (resource count).shared)
      (fun _ => CallResources.ReadAllowed (resource count).call (resource count).shared) :=
  semantics.resource _ _ (admitted count registers flags positive)

def Expected (result : Result) : Prop :=
  result.state.registers .rax = 1 ∧ result.state.registers .rcx = 0 ∧
  result.state.registers .rsp = stackBase + 8 ∧ result.state.rip = continuation ∧
  result.instructions = 15 ∧ result.reads = [⟨.stack,stackBase,8⟩]

instance (result : Result) : Decidable (Expected result) := by
  unfold Expected
  infer_instance

def sample : State := caller 3 (fun _ => 0xfeedface) 0x246

instance (read : Read) : Decidable (RawRead sample read) := by
  unfold RawRead
  infer_instance

instance : Decidable (VCGen.wp Loop.graph codeBase (fun _ read => RawRead sample read)
    15 Loop.entry sample Expected) :=
  VCGen.decidableWP Loop.graph codeBase (fun _ read => RawRead sample read)
    (fun _ _ => inferInstance) 15 Loop.entry sample Expected (fun _ => inferInstance)

theorem generated : VCGen.wp Loop.graph codeBase (fun _ read => RawRead sample read)
    15 Loop.entry sample Expected := by decide +kernel

theorem certified : VCGen.certifyWith roomy Loop.bytes Loop.graph codeBase
    (fun _ read => RawRead sample read) 15 Loop.entry sample Expected = true := by decide

example : VCGen.certify Loop.bytes Loop.graph codeBase
    (fun _ read => RawRead sample read) 15 Loop.entry sample Expected = false := by decide

theorem bounded_run (choices : Choices) :
    ∃ result, Sequential.run choices 15 sample = .ok result ∧ Expected result ∧
      result.state.memory = sample.memory ∧ VCGen.CheckedTrace (fun _ read => RawRead sample read)
        choices sample result := by
  obtain ⟨result, actual, post, frame, _, trace⟩ :=
    VCGen.certifyWith_sound_frame certified choices
  exact ⟨result, actual, post, frame, trace⟩

def beforeLoop (count : Word) (registers : Register → Word) (flags : Word) : State :=
  { (caller count registers flags).writeRegister .rax count with rip := codeBase + 65 }

/-- Actual decoded execution reaches an instruction beyond offset 64. -/
theorem reaches_beyond64 (count : Word) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Sequential.Block choices (caller count registers flags) (beforeLoop count registers flags) 9 [] := by
  let atPC (offset : Word) : State := { caller count registers flags with rip := codeBase + offset }
  refine Sequential.Block.next (middle := atPC 9) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨0, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 18) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨1, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 27) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨2, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 36) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨3, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 45) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨4, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 54) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨5, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 59) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨6, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := atPC 62) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨7, by decide⟩ _ rfl rfl]; rfl
  refine Sequential.Block.next (middle := beforeLoop count registers flags) (reads := []) (rest := []) ?_ ?_
  · rw [Loop.valid.step_eq_execute present.code ⟨8, by decide⟩ _ rfl rfl]; rfl
  exact Sequential.Block.nil

example (count : Word) (registers : Register → Word) (flags : Word) :
    Sequential.decodeAt (beforeLoop count registers flags) = .ok (.legacy (.loopRcx 0xfb)) :=
  Loop.valid.decoded present.code ⟨9, by decide⟩ _ rfl rfl

-- A zero rank cannot certify the real backedge. Static byte/node capacity is
-- not a substitute for the independent dynamic termination obligation.
example : ¬ VCGen.Cutpoints.wp Loop.graph codeBase (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 4 Loop.header
    { sample with rip := codeBase + 62 } := by
  letI := VCGen.Cutpoints.decidableWP Loop.graph codeBase (fun _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => 0) 0 (fun _ => inferInstance)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) 4 Loop.header
    { sample with rip := codeBase + 62 }
  decide

instance : Decidable (VCGen.wp Loop.graph codeBase (fun _ _ => True) 15 Loop.entry sample
    (fun result => result.state.registers .rax = 2)) :=
  VCGen.decidableWP Loop.graph codeBase (fun _ _ => True)
    (fun _ _ => inferInstance) 15 Loop.entry sample (fun result => result.state.registers .rax = 2)
    (fun _ => inferInstance)

example : ¬ VCGen.wp Loop.graph codeBase (fun _ _ => True) 15 Loop.entry sample
    (fun result => result.state.registers .rax = 2) := by decide +kernel

example (choices : Choices) : Sequential.run choices 14 sample = .error .exhaustedFuel :=
  VCGen.lower_bound_exhausted Loop.valid (admitted 3 (fun _ => 0xfeedface) 0x246 (by decide)).machine.code
    rfl generated (minimum := 15) (fun _ post => Nat.le_of_eq post.2.2.2.2.1.symm) choices (by decide)
end Call

namespace Padding

-- An early RET does not excuse unpartitioned or unauthenticated padding.
def bytes : List Byte := [0xc3] ++
  (List.replicate 6 [0x66,0x0f,0x1f,0x84,0,0,0,0,0]).flatten ++
  [0x66,0x0f,0x1f,0x44,0,0, 0x66,0x0f,0x1f,0x44,0,0, 0xc3]
def graph : CFG.Graph := vcgen_graph_with roomy bytes
abbrev entry : graph.Index := ⟨0, by decide⟩

theorem valid : CFG.Valid bytes graph roomy := CFG.checkWith_sound (by decide)
example : CFG.checkWith roomy bytes ⟨[⟨0, .legacy .ret, true, 0⟩], 0⟩ = false := by decide
example : CFG.checkWith roomy bytes { graph with nodes := graph.nodes.take 9 } = false := by decide
example : CFG.checkWith roomy (bytes.set 67 0x90) graph = false := by decide
example : CFG.analyzeWith roomy (bytes.set 67 0x90) = .error .invalidGraph := by rfl

def ram : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4164 then
    bytes[address.toNat - 4096]? else if 8192 ≤ address.toNat ∧ address.toNat < 8200 then
    some ((12288 : Word).extractLsb' ((address.toNat - 8192) * 8) 8) else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4164)

def initial : State := ⟨fun register => if register = .rsp then 8192 else 37, 4096, 0, ram⟩
def Expected (result : Result) : Prop :=
  result.state.registers .rax = 37 ∧ result.state.registers .rsp = 8200 ∧
  result.state.rip = 12288 ∧ result.instructions = 1 ∧ result.reads = [⟨.stack,8192,8⟩]

instance (result : Result) : Decidable (Expected result) := by
  unfold Expected
  infer_instance

theorem generated : VCGen.wp graph 4096 (fun _ read => read = ⟨.stack,8192,8⟩)
    1 entry initial Expected := by
  letI := VCGen.decidableWP graph 4096 (fun _ read => read = ⟨.stack,8192,8⟩)
    (fun _ _ => inferInstance) 1 entry initial Expected (fun _ => inferInstance)
  decide

theorem total (choices : Choices) :
    ∃ result, Sequential.run choices 1 initial = .ok result ∧ Expected result ∧
      result.state.memory = initial.memory := by
  obtain ⟨result, actual, post, frame, _, _⟩ := VCGen.run_sound_frame valid
    (ELF.checkCode_sound _ _ _ (by decide)) rfl generated choices
  exact ⟨result, actual, post, frame⟩

def mutated : State := { initial with memory := { ram with
  read := fun address => if address = 4163 then some 0x90 else ram.read address } }

-- The early-return WP alone is still true. Complete admission authenticates
-- the unreachable final byte and rejects the same bytes/graph in changed RAM.
example : VCGen.wp graph 4096 (fun _ _ => True) 1 entry mutated Expected := by
  letI := VCGen.decidableWP graph 4096 (fun _ _ => True)
    (fun _ _ => inferInstance) 1 entry mutated Expected (fun _ => inferInstance)
  decide
example : ELF.checkCode mutated.memory 4096 bytes = false := by decide
instance : Decidable (VCGen.wp graph 4096 (fun _ _ => True) 1 entry mutated Expected) :=
  VCGen.decidableWP graph 4096 (fun _ _ => True)
    (fun _ _ => inferInstance) 1 entry mutated Expected (fun _ => inferInstance)
example : VCGen.certifyWith roomy bytes graph 4096 (fun _ _ => True) 1 entry mutated Expected = false := by decide

-- Supplying the complete bytes at modular addresses cannot authenticate a
-- wrapping window or a window crossing the canonical hole.
def relocated (base : Word) : Memory where
  read address := bytes[(address - base).toNat]?
  executable address := decide ((address - base).toNat < bytes.length)

example : ELF.checkCode (relocated 0x7fffffffffc0) 0x7fffffffffc0 bytes = false := by decide
example : ELF.checkCode (relocated 0xffffffffffffffc0) 0xffffffffffffffc0 bytes = false := by decide

def badReturn : State := { initial with memory := { ram with
  read := fun address => if 8192 ≤ address.toNat ∧ address.toNat < 8200 then
    some ((0x800000000000 : Word).extractLsb' ((address.toNat - 8192) * 8) 8)
    else ram.read address } }

-- Structural admission and authentic code do not supply a canonical caller.
example : ELF.checkCode badReturn.memory 4096 bytes = true := by decide
example (choices : Choices) : Sequential.run choices 1 badReturn =
    .error (.noncanonicalReturn 0x800000000000) := by rfl

end Padding

namespace NodeCaps

-- Independent 65-byte valid partition: explicit byte and node caps must both
-- be selected. Enlarging just the byte cap leaves the old node rejection.
def bytes : List Byte := (List.replicate 32 [0x66,0x90]).flatten ++ [0xc3]
def graph : CFG.Graph := CFG.annotate
  ((List.range 32).map (fun i => ⟨2 * i, .nop .two, false, 0⟩) ++ [⟨64, .legacy .ret, false, 0⟩])
example : CFG.checkWith roomy bytes graph = true := by decide
example : CFG.check bytes graph = false := by decide
example : CFG.analyze bytes = .error .byteLimit := by rfl
example : CFG.checkWith ⟨96,32,by decide⟩ bytes graph = false := by decide
example : CFG.analyzeWith ⟨96,32,by decide⟩ bytes = .error .instructionLimit := by decide +kernel
example : CFG.analyzeWith ⟨0,0,by decide⟩ bytes = .error .byteLimit := by rfl
example : CFG.analyzeWith roomy [] = .error .empty := by rfl
example : CFG.analyze (List.replicate 32 0x90 ++ [0xc3]) = .error .instructionLimit := by decide +kernel

end NodeCaps

end EDSL.Tests.CFGProfiles

#print axioms EDSL.X86.Sequential.CFG.checkWith_sound
#print axioms EDSL.X86.Sequential.CFG.Valid.wordOffset_injective
#print axioms EDSL.X86.VCGen.Cutpoints.Annotations.sound
#print axioms EDSL.Tests.CFGProfiles.Loop.total
#print axioms EDSL.Tests.CFGProfiles.Padding.total
#audit_edsl
