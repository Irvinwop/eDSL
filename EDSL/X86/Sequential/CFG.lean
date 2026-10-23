/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Code
import EDSL.X86.Sequential.Machine

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential.CFG

/-- Static structural admission caps, independent of execution fuel and dynamic
cutpoint ranks. The slack prevents wrapping the static decoder's fetch offsets;
it does not change the decoder or admit additional instructions. Zero caps are
well formed and reject every nonempty program. -/
structure Profile where
  maxBytes : Nat
  maxNodes : Nat
  fetchNoWrap : maxBytes + 15 ≤ 2^64
  deriving DecidableEq

/-- The unchanged public default: 64 bytes and 32 instructions. -/
def defaultProfile : Profile := ⟨64, 32, by decide⟩

/-- Finite certificate data. Cutpoints carry user-supplied dynamic invariants;
`depth` certifies only the acyclic interiors between those cutpoints. -/
structure Node where
  offset : Nat
  instruction : Instruction
  cutpoint : Bool
  depth : Nat
  deriving DecidableEq, Repr

structure Graph where
  nodes : List Node
  maxDepth : Nat
  deriving DecidableEq, Repr

abbrev Graph.Index (graph : Graph) := Fin graph.nodes.length

def Graph.node (graph : Graph) (index : graph.Index) : Node := graph.nodes[index.val]
def Graph.cutpoint (graph : Graph) (index : graph.Index) : Bool := (graph.node index).cutpoint
def Graph.depth (graph : Graph) (index : graph.Index) : Nat := (graph.node index).depth

/-- Resource-effect admission shared by every size profile. Stores, locked
operations and system calls need further resource-effect obligations. -/
def readOnly : Instruction → Bool
  | .legacy .storeEsiRdi | .legacy .storeEaxRsi | .legacy .exchangeEaxRdi
  | .legacy .fetchAddEaxRdi | .legacy .syscall | .storeMem32 _ _ | .storeMem64 _ _ => false
  | .legacy (.leaEaxRdiDisp8 _) | .legacy (.leaEaxRaxDisp8 _)
  | .legacy .movEaxEdi | .legacy .movEaxEsi | .legacy (.jrcxz _)
  | .legacy (.loopRcx _) | .legacy (.jnz _) | .legacy .cmpEaxZero
  | .legacy .loadEaxRdi | .legacy .loadEaxRsi | .legacy (.mov32 _ _)
  | .lea32 _ _ _ | .testImm8 _ _ _
  | .logicalReg32 _ _ _ _ | .logicalImm32 _ _ _ _ | .cmpImm64 _ _
  | .subImm32 _ _ _ | .cmpImm32 _ _ _
  | .shiftRightImm32 _ _ _ _ | .imulReg64 _ _ | .addImm32 _ _ _ | .inc32 _ _ | .negReg32 _ _ | .bswapReg64 _ | .shrOne64 _ | .rolCL64 _
  | .movzxMem8 _ _ _ | .movzxReg8 _ _ _ | .cmpReg8 _ _ _ | .subReg32 _ _ _
  | .test32 _ _ _ | .cmp32 _ _ _ | .cmpMemImm8 _ _ | .cmpRegMem8 _ _ _ | .cmpMemReg8 _ _ | .cmpMemReg32 _ _ | .endbr64IbtDisabled | .nop _
  | .legacy .ret | .xorSelf32 _ | .test64 _ _ | .cmp64 _ _
  | .addMem32 _ _ | .addMem64 _ _ | .movReg32 _ _ | .movReg64 _ _ | .setcc _ _ _ | .movImm8 _ _ _ | .movSignImm32 _ _ | .cmovReg32 _ _ _ _ | .cmovReg64 _ _ _ | .lea64 _ _ | .addReg64 _ _ | .logicalReg64 _ _ _
  | .xchgReg64 _ _ | .xchgRax64 _ | .loadMem32 _ _ | .loadMem64 _ _ | .addImm64 _ _
  | .inc64 _ | .dec64 _ | .je _ | .jcc _ _ | .jmp _ => true

/-- All possible relative RIP offsets, independently of runtime branch flags.
RET leaves the graph through the protected runtime stack instead. -/
def Node.successors (node : Node) : List Word :=
  let fallthrough := BitVec.ofNat 64 (node.offset + node.instruction.length)
  let branch (displacement : Byte) :=
    BitVec.ofNat 64 node.offset + 2 + displacement.signExtend 64
  match node.instruction with
  | .legacy .ret => []
  | .legacy (.jrcxz displacement) | .legacy (.loopRcx displacement)
  | .legacy (.jnz displacement) | .je displacement | .jcc _ displacement => [fallthrough, branch displacement]
  | .jmp displacement => [branch displacement]
  | _ => [fallthrough]

def Graph.Edge (graph : Graph) (source destination : graph.Index) : Prop :=
  BitVec.ofNat 64 (graph.node destination).offset ∈ (graph.node source).successors

instance (graph : Graph) (source destination : graph.Index) :
    Decidable (graph.Edge source destination) := inferInstanceAs (Decidable (_ ∈ _))

def Graph.edge (graph : Graph) (source destination : graph.Index) : Bool :=
  decide (graph.Edge source destination)

/-- A complete partition of the entire explicitly selected byte window. -/
def linearFrom (start : Nat) : List Node → Nat → Bool
  | [], finish => decide (start = finish)
  | node :: rest, finish =>
    decide (node.offset = start) && linearFrom (start + node.instruction.length) rest finish

def nodeMatches (bytes : List Byte) (node : Node) : Bool :=
  match decodeAt (codeState bytes node.offset) with
  | .ok instruction => decide (instruction = node.instruction)
  | .error _ => false

private def Facts (bytes : List Byte) (graph : Graph) : Prop :=
  0 < graph.nodes.length ∧
  linearFrom 0 graph.nodes bytes.length = true ∧
  (∀ i : graph.Index, i.val = 0 → graph.cutpoint i = true) ∧
  (∀ i : graph.Index, (graph.node i).offset < bytes.length ∧
    nodeMatches bytes (graph.node i) = true ∧
    readOnly (graph.node i).instruction = true ∧ graph.depth i ≤ graph.maxDepth) ∧
  (∀ i : graph.Index, (graph.node i).successors.all (fun target =>
    decide (∃ j : graph.Index, BitVec.ofNat 64 (graph.node j).offset = target)) = true) ∧
  (∀ i j : graph.Index, graph.Edge i j → graph.cutpoint j = false → graph.depth j < graph.depth i)

instance (bytes : List Byte) (graph : Graph) : Decidable (Facts bytes graph) := by
  unfold Facts
  infer_instance

/-- One cap-independent structural invariant, with explicit admission caps.
Discovery is untrusted; annotation data never selects execution opcodes. -/
def checkWith (profile : Profile) (bytes : List Byte) (graph : Graph) : Bool :=
  decide (bytes.length ≤ profile.maxBytes ∧ graph.nodes.length ≤ profile.maxNodes ∧
    Facts bytes graph)

/-- Compatibility checker; its default is never inferred from candidate bytes. -/
def check (bytes : List Byte) (graph : Graph) : Bool := checkWith defaultProfile bytes graph

/-- The profile is part of the proof's type. Omitting it means exactly the old
64-byte/32-node profile, including the original field and constructor order. -/
structure Valid (bytes : List Byte) (graph : Graph) (profile : Profile := defaultProfile) : Prop where
  byteBound : bytes.length ≤ profile.maxBytes
  instructionBound : graph.nodes.length ≤ profile.maxNodes
  nonempty : 0 < graph.nodes.length
  linear : linearFrom 0 graph.nodes bytes.length = true
  entryCutpoint : ∀ i : graph.Index, i.val = 0 → graph.cutpoint i = true
  nodes : ∀ i : graph.Index, (graph.node i).offset < bytes.length ∧
    decodeAt (codeState bytes (graph.node i).offset) = .ok (graph.node i).instruction ∧
    readOnly (graph.node i).instruction = true ∧ graph.depth i ≤ graph.maxDepth
  closed : ∀ i : graph.Index, ∀ target ∈ (graph.node i).successors,
    ∃ j : graph.Index, BitVec.ofNat 64 (graph.node j).offset = target
  decreases : ∀ i j : graph.Index, graph.Edge i j → graph.cutpoint j = false →
    graph.depth j < graph.depth i

variable {profile : Profile}

theorem checkWith_sound {bytes : List Byte} {graph : Graph}
    (checked : checkWith profile bytes graph = true) : Valid bytes graph profile := by
  have facts : bytes.length ≤ profile.maxBytes ∧ graph.nodes.length ≤ profile.maxNodes ∧
      Facts bytes graph := of_decide_eq_true checked
  rcases facts with ⟨size, count, nonempty, linear, entry, nodes, closed, decreases⟩
  refine ⟨size, count, nonempty, linear, entry, ?_, ?_, decreases⟩
  · intro i
    have facts := nodes i
    refine ⟨facts.1, ?_, facts.2.2⟩
    cases decoded : decodeAt (codeState bytes (graph.node i).offset) with
    | error fault => simp [nodeMatches, decoded] at facts
    | ok instruction =>
      have same : instruction = (graph.node i).instruction := by
        simpa only [nodeMatches, decoded, decide_eq_true_eq] using facts.2.1
      exact congrArg Except.ok same
  · intro i target member
    exact of_decide_eq_true (List.all_eq_true.mp (closed i) target member)

theorem check_sound {bytes : List Byte} {graph : Graph}
    (checked : check bytes graph = true) : Valid bytes graph := checkWith_sound checked

theorem checkWith_complete {bytes : List Byte} {graph : Graph}
    (valid : Valid bytes graph profile) : checkWith profile bytes graph = true := by
  have facts : Facts bytes graph := by
    refine ⟨valid.nonempty, valid.linear, valid.entryCutpoint, ?_, ?_, valid.decreases⟩
    · intro i
      have node := valid.nodes i
      exact ⟨node.1, by simp [nodeMatches, node.2.1], node.2.2⟩
    · intro i
      apply List.all_eq_true.mpr
      intro target member
      exact decide_eq_true (valid.closed i target member)
  exact decide_eq_true ⟨valid.byteBound, valid.instructionBound, facts⟩

theorem checkWith_iff {bytes : List Byte} {graph : Graph} :
    checkWith profile bytes graph = true ↔ Valid bytes graph profile :=
  ⟨checkWith_sound, checkWith_complete⟩

theorem check_iff {bytes : List Byte} {graph : Graph} :
    check bytes graph = true ↔ Valid bytes graph := checkWith_iff

theorem Valid.fetchNoWrap {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile) :
    bytes.length + 15 ≤ 2^64 := by
  have := valid.byteBound
  have := profile.fetchNoWrap
  omega

def Valid.entry {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile) : graph.Index :=
  ⟨0, valid.nonempty⟩

theorem Valid.entry_cutpoint {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile) :
    graph.cutpoint valid.entry = true := valid.entryCutpoint valid.entry rfl

theorem Valid.entry_offset {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile) :
    (graph.node valid.entry).offset = 0 := by
  cases nodes : graph.nodes with
  | nil => have nonempty := valid.nonempty; simp [nodes] at nonempty
  | cons node rest =>
    have linear := valid.linear
    simp only [nodes, linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] at linear
    simpa only [Graph.node, Valid.entry, nodes, List.getElem_cons_zero] using linear.1

/-- A checked node decodes in current actual RAM, with its actual runtime RIP. -/
theorem Valid.decoded {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {memory : Memory} {base : Word} (code : CodeAt memory base bytes)
    (index : graph.Index) (state : State) (currentMemory : state.memory = memory)
    (currentPC : state.rip = base + BitVec.ofNat 64 (graph.node index).offset) :
    decodeAt state = .ok (graph.node index).instruction :=
  decodeAt_transport
    (code_fetch_transport_of_bound code valid.fetchNoWrap (graph.node index).offset
      (valid.nodes index).1 state currentMemory currentPC) (valid.nodes index).2.1

theorem Valid.step_eq_execute {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {memory : Memory} {base : Word} (code : CodeAt memory base bytes)
    (index : graph.Index) (state : State) (currentMemory : state.memory = memory)
    (currentPC : state.rip = base + BitVec.ofNat 64 (graph.node index).offset) (af : Bool) :
    step af state = execute state (graph.node index).instruction af :=
  Sequential.step_eq_execute af (valid.decoded code index state currentMemory currentPC)

theorem Valid.canonical_node {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {memory : Memory} {base : Word} (code : CodeAt memory base bytes) (index : graph.Index) :
    canonical (base + BitVec.ofNat 64 (graph.node index).offset) = true :=
  code_canonical_offset code (graph.node index).offset (valid.nodes index).1

/-- The selected runtime node address is an ordinary, non-wrapping natural
sum. Relative branch arithmetic remains the production ISA's word arithmetic. -/
theorem Valid.address_no_wrap {bytes : List Byte} {graph : Graph}
    (valid : Valid bytes graph profile) {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (index : graph.Index) :
    base.toNat + (graph.node index).offset < 2^64 := by
  have := code.1
  have := (valid.nodes index).1
  omega

theorem Valid.address_toNat {bytes : List Byte} {graph : Graph}
    (valid : Valid bytes graph profile) {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (index : graph.Index) :
    (base + BitVec.ofNat 64 (graph.node index).offset).toNat =
      base.toNat + (graph.node index).offset := by
  have sum := valid.address_no_wrap code index
  have offsetSmall : (graph.node index).offset < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetSmall,
    Nat.mod_eq_of_lt sum]

theorem linearFrom_start_le_finish {nodes : List Node} {start finish : Nat}
    (linear : linearFrom start nodes finish = true) : start ≤ finish := by
  induction nodes generalizing start with
  | nil =>
    have same : start = finish := of_decide_eq_true linear
    omega
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + node.instruction.length) rest finish = true := by
      simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear
    have bound := induction parts.2
    omega

theorem linearFrom_bounds {nodes : List Node} {start finish : Nat}
    (linear : linearFrom start nodes finish = true) (index : Fin nodes.length) :
    start ≤ nodes[index.val].offset ∧
      nodes[index.val].offset + nodes[index.val].instruction.length ≤ finish := by
  induction nodes generalizing start with
  | nil => exact False.elim (by have bound := index.isLt; simp at bound)
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + node.instruction.length) rest finish = true := by
      simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear
    rcases index with ⟨index, inside⟩
    cases index with
    | zero =>
      have bound := linearFrom_start_le_finish parts.2
      simpa only [List.getElem_cons_zero, parts.1, Nat.le_refl, true_and] using bound
    | succ index =>
      have insideRest : index < rest.length := by simpa using inside
      have bounds := induction parts.2 ⟨index, insideRest⟩
      dsimp only at bounds
      simp only [List.getElem_cons_succ]
      exact ⟨by omega, bounds.2⟩

theorem linearFrom_strict {nodes : List Node} {start finish : Nat}
    (linear : linearFrom start nodes finish = true) (left right : Fin nodes.length)
    (ordered : left.val < right.val) : nodes[left.val].offset < nodes[right.val].offset := by
  induction nodes generalizing start with
  | nil => exact False.elim (by have bound := left.isLt; simp at bound)
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + node.instruction.length) rest finish = true := by
      simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear
    rcases left with ⟨left, leftInside⟩
    rcases right with ⟨right, rightInside⟩
    dsimp only at ordered
    cases left with
    | zero =>
      cases right with
      | zero => omega
      | succ right =>
        have rightRest : right < rest.length := by simpa using rightInside
        have bound := (linearFrom_bounds parts.2 ⟨right, rightRest⟩).1
        dsimp only at bound
        have positive := node.instruction.length_pos
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        omega
    | succ left =>
      cases right with
      | zero => omega
      | succ right =>
        have leftRest : left < rest.length := by simpa using leftInside
        have rightRest : right < rest.length := by simpa using rightInside
        exact induction parts.2 ⟨left, leftRest⟩ ⟨right, rightRest⟩ (by
          dsimp only
          omega)

theorem Valid.instruction_span {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    (index : graph.Index) :
    (graph.node index).offset + (graph.node index).instruction.length ≤ bytes.length :=
  (linearFrom_bounds valid.linear index).2

theorem Valid.offset_injective {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {left right : graph.Index} (same : (graph.node left).offset = (graph.node right).offset) :
    left = right := by
  have notLess : ¬left.val < right.val := by
    intro ordered
    have strict := linearFrom_strict valid.linear left right ordered
    change (graph.node left).offset < (graph.node right).offset at strict
    omega
  have notGreater : ¬right.val < left.val := by
    intro ordered
    have strict := linearFrom_strict valid.linear right left ordered
    change (graph.node right).offset < (graph.node left).offset at strict
    omega
  apply Fin.ext
  omega

theorem Valid.wordOffset_injective {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {left right : graph.Index}
    (same : BitVec.ofNat 64 (graph.node left).offset = BitVec.ofNat 64 (graph.node right).offset) :
    left = right := by
  apply valid.offset_injective
  have leftSmall : (graph.node left).offset < 2^64 := by
    have bound := (valid.nodes left).1
    have size := valid.fetchNoWrap
    omega
  have rightSmall : (graph.node right).offset < 2^64 := by
    have bound := (valid.nodes right).1
    have size := valid.fetchNoWrap
    omega
  have natural := congrArg BitVec.toNat same
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftSmall,
    Nat.mod_eq_of_lt rightSmall] using natural

theorem linearFrom_covers {nodes : List Node} {start finish position : Nat}
    (linear : linearFrom start nodes finish = true) (lower : start ≤ position)
    (upper : position < finish) :
    ∃ index : Fin nodes.length, nodes[index.val].offset ≤ position ∧
      position < nodes[index.val].offset + nodes[index.val].instruction.length := by
  induction nodes generalizing start with
  | nil =>
    have same : start = finish := of_decide_eq_true linear
    omega
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + node.instruction.length) rest finish = true := by
      simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear
    by_cases inside : position < start + node.instruction.length
    · refine ⟨⟨0, by simp⟩, ?_⟩
      simpa only [Fin.val_mk, List.getElem_cons_zero, parts.1] using And.intro lower inside
    · obtain ⟨index, begin, finish⟩ := induction parts.2 (by omega)
      refine ⟨⟨index.val + 1, by simp⟩, ?_⟩
      simpa only [Fin.val_mk, List.getElem_cons_succ] using And.intro begin finish

/-- Every selected byte lies in one of the checked positive-length instruction
spans. The checker therefore neither skips bytes nor silently ignores suffixes. -/
theorem Valid.covers {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    (position : Nat) (inside : position < bytes.length) :
    ∃ index : graph.Index, (graph.node index).offset ≤ position ∧
      position < (graph.node index).offset + (graph.node index).instruction.length :=
  linearFrom_covers valid.linear (Nat.zero_le position) inside

end EDSL.X86.Sequential.CFG
