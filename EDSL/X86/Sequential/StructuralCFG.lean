/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit
import EDSL.X86.Sequential.CFG

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Structural admission of an exact selected byte window, independent of instruction
effect policy. This module reuses the production CFG data, partition checker,
decoder authentication, and fetch transport. It proves only structure and decoding
in current executable memory; it establishes no execution, OS, weakest-precondition,
store, or atomic behavior, and makes no public coverage claim.

Future consumers must preserve the current executable text and satisfy the actual
resource, instruction-effect, scheduler, ownership, and synchronization semantics.
Structural admission alone discharges none of those obligations. A failed check
rejects this certificate; it does not establish a defect in the selected program.
-/

namespace EDSL.X86.Sequential.CFG.Structural

/-- Cap-independent structural facts. Every node is authenticated by the existing
decoder, but no instruction-effect policy is imposed here. -/
private def Facts (bytes : List Byte) (graph : Graph) : Prop :=
  0 < graph.nodes.length ∧
  linearFrom 0 graph.nodes bytes.length = true ∧
  (∀ i : graph.Index, i.val = 0 → graph.cutpoint i = true) ∧
  (∀ i : graph.Index, (graph.node i).offset < bytes.length ∧
    nodeMatches bytes (graph.node i) = true ∧ graph.depth i ≤ graph.maxDepth) ∧
  (∀ i : graph.Index, (graph.node i).successors.all (fun target =>
    decide (∃ j : graph.Index, BitVec.ofNat 64 (graph.node j).offset = target)) = true) ∧
  (∀ i j : graph.Index, graph.Edge i j → graph.cutpoint j = false → graph.depth j < graph.depth i)

private instance (bytes : List Byte) (graph : Graph) : Decidable (Facts bytes graph) := by
  unfold Facts
  infer_instance

/-- Check the entire exact selected byte partition with explicit static caps,
entry cutpoint, successor closure, and strict depth decrease outside cutpoints.
Instruction annotations never select the opcodes used by the decoder. -/
def checkWith (profile : Profile) (bytes : List Byte) (graph : Graph) : Bool :=
  decide (bytes.length ≤ profile.maxBytes ∧ graph.nodes.length ≤ profile.maxNodes ∧
    Facts bytes graph)

/-- Structural admission under the existing fixed 64-byte/32-node default. -/
def check (bytes : List Byte) (graph : Graph) : Bool := checkWith defaultProfile bytes graph

/-- The existing CFG validity fields and order, with only the `readOnly` conjunct
removed from `nodes`. The profile remains part of the proposition's type.
Neither structural validity nor decoder authentication proves effect behavior. -/
structure Valid (bytes : List Byte) (graph : Graph) (profile : Profile := defaultProfile) : Prop where
  byteBound : bytes.length ≤ profile.maxBytes
  instructionBound : graph.nodes.length ≤ profile.maxNodes
  nonempty : 0 < graph.nodes.length
  linear : linearFrom 0 graph.nodes bytes.length = true
  entryCutpoint : ∀ i : graph.Index, i.val = 0 → graph.cutpoint i = true
  nodes : ∀ i : graph.Index, (graph.node i).offset < bytes.length ∧
    decodeAt (codeState bytes (graph.node i).offset) = .ok (graph.node i).instruction ∧
    graph.depth i ≤ graph.maxDepth
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

theorem check_complete {bytes : List Byte} {graph : Graph}
    (valid : Valid bytes graph) : check bytes graph = true := checkWith_complete valid

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

/-- Authenticate a node against actual current executable RAM and runtime RIP.
This transports decoding only; it assumes no instruction-effect policy and
establishes no behavior of the authenticated instruction. -/
theorem Valid.decoded {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {memory : Memory} {base : Word} (code : CodeAt memory base bytes)
    (index : graph.Index) (state : State) (currentMemory : state.memory = memory)
    (currentPC : state.rip = base + BitVec.ofNat 64 (graph.node index).offset) :
    decodeAt state = .ok (graph.node index).instruction :=
  decodeAt_transport
    (code_fetch_transport_of_bound code valid.fetchNoWrap (graph.node index).offset
      (valid.nodes index).1 state currentMemory currentPC) (valid.nodes index).2.1

/-- Forget the existing read-only admission policy, preserving all structure. -/
theorem Valid.ofReadOnly {bytes : List Byte} {graph : Graph}
    (valid : CFG.Valid bytes graph profile) : Valid bytes graph profile := by
  refine ⟨valid.byteBound, valid.instructionBound, valid.nonempty, valid.linear,
    valid.entryCutpoint, ?_, valid.closed, valid.decreases⟩
  intro i
  have node := valid.nodes i
  exact ⟨node.1, node.2.1, node.2.2.2⟩

/-- Recover the unchanged existing validity proposition when every node also
satisfies its read-only admission policy. This introduces no effect theorem. -/
theorem Valid.toReadOnly {bytes : List Byte} {graph : Graph}
    (valid : Valid bytes graph profile)
    (allowed : ∀ i : graph.Index, CFG.readOnly (graph.node i).instruction = true) :
    CFG.Valid bytes graph profile := by
  refine ⟨valid.byteBound, valid.instructionBound, valid.nonempty, valid.linear,
    valid.entryCutpoint, ?_, valid.closed, valid.decreases⟩
  intro i
  have node := valid.nodes i
  exact ⟨node.1, node.2.1, allowed i, node.2.2⟩

/-- The old checker is exactly structural admission plus its existing per-node
read-only predicate, for the same explicit profile and exact selected bytes. -/
theorem checkWith_readOnly_iff {bytes : List Byte} {graph : Graph} :
    CFG.checkWith profile bytes graph = true ↔
      checkWith profile bytes graph = true ∧
      (∀ i : graph.Index, CFG.readOnly (graph.node i).instruction = true) := by
  constructor
  · intro checked
    have valid := CFG.checkWith_sound checked
    exact ⟨checkWith_complete (Valid.ofReadOnly valid), fun i => (valid.nodes i).2.2.1⟩
  · rintro ⟨checked, allowed⟩
    exact CFG.checkWith_complete ((checkWith_sound checked).toReadOnly allowed)

#print axioms checkWith_sound
#print axioms checkWith_complete
#print axioms checkWith_iff
#print axioms check_iff
#print axioms Valid.fetchNoWrap
#print axioms Valid.entry_cutpoint
#print axioms Valid.entry_offset
#print axioms Valid.decoded
#print axioms Valid.ofReadOnly
#print axioms Valid.toReadOnly
#print axioms checkWith_readOnly_iff

end EDSL.X86.Sequential.CFG.Structural

#audit_edsl
