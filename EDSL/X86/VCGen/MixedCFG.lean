/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Model
import EDSL.X86.Sequential.CFG
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Finite structural certificates for exact byte windows decoded by the existing
TSO64 decoder. RMW family and static caps are independent, explicit admission
inputs. The certificate authenticates the entire instruction partition, entry,
successor closure, and decreasing depths between cutpoints.

A locked successor describes its retired control continuation. This static
certificate supplies no execution, resource authority, progress, count, ABI, or
return-target contract. RET has no static successors. A failed check rejects the
certificate and does not establish a defect in the selected program.
-/

namespace EDSL.X86.VCGen.MixedCFG
open OS OS.TSO64

abbrev Caps := Sequential.CFG.Profile

/-- One actual decoded instruction and its static partition annotations. -/
structure Node (family : RMWFamily) where
  offset : Nat
  instruction : OS.TSO64.Decoded family
  cutpoint : Bool
  depth : Nat

structure Graph (family : RMWFamily) where
  nodes : List (Node family)
  maxDepth : Nat

abbrev Graph.Index {family : RMWFamily} (graph : Graph family) :=
  Fin graph.nodes.length

def Graph.node {family : RMWFamily} (graph : Graph family)
    (index : graph.Index) : Node family := graph.nodes[index.val]

def instructionLength {family : RMWFamily} : OS.TSO64.Decoded family → Nat
  | .ordinary instruction => instruction.length
  | .locked instruction => (family.embed instruction).length

/-- Tagged equality uses the existing leaf instances, without an instance for
mixed decoded instructions or whole graphs. -/
def decodedEq {family : RMWFamily} :
    OS.TSO64.Decoded family → OS.TSO64.Decoded family → Bool
  | .ordinary a, .ordinary b => decide (a = b)
  | .locked a, .locked b => decide (a = b)
  | _, _ => false

theorem instructionLength_pos {family : RMWFamily}
    (instruction : OS.TSO64.Decoded family) : 0 < instructionLength instruction := by
  cases instruction with
  | ordinary instruction => exact instruction.length_pos
  | locked instruction =>
    cases family with
    | xaddOnly => change 0 < 5; decide
    | arithmetic =>
      cases instruction with
      | xadd old => change 0 < 5; decide
      | addImm8 encoding => change 0 < 5; decide
      | inc encoding => change 0 < 4; decide

theorem decodedEq_eq_true_iff {family : RMWFamily} (a b : OS.TSO64.Decoded family) :
    decodedEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [decodedEq]

/-- Ordinary edges retain the production branch classifier and word arithmetic.
Locked edges retain the exact tagged instruction length. A final INC therefore
has an outside-window successor and cannot satisfy graph closure. -/
def Node.successors {family : RMWFamily} (node : Node family) : List Word :=
  match node.instruction with
  | .ordinary instruction =>
      (Sequential.CFG.Node.mk node.offset instruction node.cutpoint node.depth).successors
  | .locked instruction =>
      [BitVec.ofNat 64 (node.offset + (family.embed instruction).length)]

def Graph.Edge {family : RMWFamily} (graph : Graph family)
    (source destination : graph.Index) : Prop :=
  BitVec.ofNat 64 (graph.node destination).offset ∈ (graph.node source).successors

local instance {family : RMWFamily} (graph : Graph family)
    (source destination : graph.Index) : Decidable (graph.Edge source destination) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Partition every byte of the selected window, including all suffix bytes. -/
def linearFrom {family : RMWFamily} (start : Nat) :
    List (Node family) → Nat → Bool
  | [], finish => decide (start = finish)
  | node :: rest, finish =>
      decide (node.offset = start) &&
        linearFrom (start + instructionLength node.instruction) rest finish

def nodeMatches {family : RMWFamily} (bytes : List Byte) (node : Node family) : Bool :=
  match OS.TSO64.decode (Sequential.codeState bytes node.offset) family with
  | .ok actual => decodedEq actual node.instruction
  | .error _ => false

private def Facts {family : RMWFamily} (bytes : List Byte) (graph : Graph family) : Prop :=
  0 < graph.nodes.length ∧
  linearFrom 0 graph.nodes bytes.length = true ∧
  (∀ i : graph.Index, i.val = 0 → (graph.node i).cutpoint = true) ∧
  (∀ i : graph.Index, (graph.node i).offset < bytes.length ∧
    nodeMatches bytes (graph.node i) = true ∧ (graph.node i).depth ≤ graph.maxDepth) ∧
  (∀ i : graph.Index, (graph.node i).successors.all (fun target =>
    decide (∃ j : graph.Index, BitVec.ofNat 64 (graph.node j).offset = target)) = true) ∧
  (∀ i j : graph.Index, graph.Edge i j → (graph.node j).cutpoint = false →
    (graph.node j).depth < (graph.node i).depth)

local instance {family : RMWFamily} (bytes : List Byte) (graph : Graph family) :
    Decidable (Facts bytes graph) := by
  unfold Facts
  infer_instance

/-- Finite admission with explicit family and caps. Annotation data never
selects an opcode in place of the production decoder. -/
def checkWith (family : RMWFamily) (caps : Caps) (bytes : List Byte)
    (graph : Graph family) : Bool :=
  decide (bytes.length ≤ caps.maxBytes ∧ graph.nodes.length ≤ caps.maxNodes ∧
    Facts bytes graph)

/-- Static whole-window validity, indexed by the selected family and caps.
Current executable code and runtime resources remain separate obligations. -/
structure Valid (family : RMWFamily) (caps : Caps) (bytes : List Byte)
    (graph : Graph family) : Prop where
  byteBound : bytes.length ≤ caps.maxBytes
  instructionBound : graph.nodes.length ≤ caps.maxNodes
  nonempty : 0 < graph.nodes.length
  linear : linearFrom 0 graph.nodes bytes.length = true
  entryCutpoint : ∀ i : graph.Index, i.val = 0 → (graph.node i).cutpoint = true
  nodes : ∀ i : graph.Index, (graph.node i).offset < bytes.length ∧
    OS.TSO64.decode (Sequential.codeState bytes (graph.node i).offset) family =
      .ok (graph.node i).instruction ∧ (graph.node i).depth ≤ graph.maxDepth
  closed : ∀ i : graph.Index, ∀ target ∈ (graph.node i).successors,
    ∃ j : graph.Index, BitVec.ofNat 64 (graph.node j).offset = target
  decreases : ∀ i j : graph.Index, graph.Edge i j → (graph.node j).cutpoint = false →
    (graph.node j).depth < (graph.node i).depth

variable {family : RMWFamily} {caps : Caps} {bytes : List Byte} {graph : Graph family}

theorem checkWith_sound (checked : checkWith family caps bytes graph = true) :
    Valid family caps bytes graph := by
  have facts : bytes.length ≤ caps.maxBytes ∧ graph.nodes.length ≤ caps.maxNodes ∧
      Facts bytes graph := of_decide_eq_true checked
  rcases facts with ⟨size, count, nonempty, linear, entry, nodes, closed, decreases⟩
  refine ⟨size, count, nonempty, linear, entry, ?_, ?_, decreases⟩
  · intro i
    have node := nodes i
    refine ⟨node.1, ?_, node.2.2⟩
    cases decoded : OS.TSO64.decode (Sequential.codeState bytes (graph.node i).offset) family with
    | error fault => simp [nodeMatches, decoded] at node
    | ok actual =>
      have matched : decodedEq actual (graph.node i).instruction = true := by
        simpa only [nodeMatches, decoded] using node.2.1
      exact congrArg Except.ok ((decodedEq_eq_true_iff actual (graph.node i).instruction).mp matched)
  · intro i target member
    exact of_decide_eq_true (List.all_eq_true.mp (closed i) target member)

theorem checkWith_complete (valid : Valid family caps bytes graph) :
    checkWith family caps bytes graph = true := by
  have facts : Facts bytes graph := by
    refine ⟨valid.nonempty, valid.linear, valid.entryCutpoint, ?_, ?_, valid.decreases⟩
    · intro i
      have node := valid.nodes i
      refine ⟨node.1, ?_, node.2.2⟩
      simp only [nodeMatches, node.2.1, decodedEq_eq_true_iff]
    · intro i
      apply List.all_eq_true.mpr
      intro target member
      exact decide_eq_true (valid.closed i target member)
  exact decide_eq_true ⟨valid.byteBound, valid.instructionBound, facts⟩

theorem checkWith_iff :
    checkWith family caps bytes graph = true ↔ Valid family caps bytes graph :=
  ⟨checkWith_sound, checkWith_complete⟩

theorem Valid.fetchNoWrap (valid : Valid family caps bytes graph) :
    bytes.length + 15 ≤ 2^64 := by
  have := valid.byteBound
  have := caps.fetchNoWrap
  omega

private theorem linearFrom_start_le_finish {nodes : List (Node family)} {start finish : Nat}
    (linear : linearFrom start nodes finish = true) : start ≤ finish := by
  induction nodes generalizing start with
  | nil =>
    have same : start = finish := of_decide_eq_true linear
    omega
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + instructionLength node.instruction) rest finish = true := by
      simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear
    have bound := induction parts.2
    omega

private theorem linearFrom_bounds {nodes : List (Node family)} {start finish : Nat}
    (linear : linearFrom start nodes finish = true) (index : Fin nodes.length) :
    start ≤ nodes[index.val].offset ∧
      nodes[index.val].offset + instructionLength nodes[index.val].instruction ≤ finish := by
  induction nodes generalizing start with
  | nil => exact False.elim (by have bound := index.isLt; simp at bound)
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + instructionLength node.instruction) rest finish = true := by
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

private theorem linearFrom_strict {nodes : List (Node family)} {start finish : Nat}
    (linear : linearFrom start nodes finish = true) (left right : Fin nodes.length)
    (ordered : left.val < right.val) : nodes[left.val].offset < nodes[right.val].offset := by
  induction nodes generalizing start with
  | nil => exact False.elim (by have bound := left.isLt; simp at bound)
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + instructionLength node.instruction) rest finish = true := by
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
        have positive := instructionLength_pos node.instruction
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

private theorem linearFrom_covers {nodes : List (Node family)} {start finish position : Nat}
    (linear : linearFrom start nodes finish = true) (lower : start ≤ position)
    (upper : position < finish) :
    ∃ index : Fin nodes.length, nodes[index.val].offset ≤ position ∧
      position < nodes[index.val].offset + instructionLength nodes[index.val].instruction := by
  induction nodes generalizing start with
  | nil =>
    have same : start = finish := of_decide_eq_true linear
    omega
  | cons node rest induction =>
    have parts : node.offset = start ∧
        linearFrom (start + instructionLength node.instruction) rest finish = true := by
      simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear
    by_cases inside : position < start + instructionLength node.instruction
    · refine ⟨⟨0, by simp⟩, ?_⟩
      simpa only [Fin.val_mk, List.getElem_cons_zero, parts.1] using And.intro lower inside
    · obtain ⟨index, begins, ends⟩ := induction parts.2 (by omega)
      refine ⟨⟨index.val + 1, by simp⟩, ?_⟩
      simpa only [Fin.val_mk, List.getElem_cons_succ] using And.intro begins ends

/-- Each authenticated instruction ends within the exact selected window. -/
theorem Valid.instruction_span (valid : Valid family caps bytes graph) (i : graph.Index) :
    (graph.node i).offset + instructionLength (graph.node i).instruction ≤ bytes.length :=
  (linearFrom_bounds valid.linear i).2

/-- Every byte belongs to an instruction span of the complete partition. -/
theorem Valid.covers (valid : Valid family caps bytes graph)
    (position : Nat) (inside : position < bytes.length) :
    ∃ i : graph.Index, (graph.node i).offset ≤ position ∧
      position < (graph.node i).offset + instructionLength (graph.node i).instruction :=
  linearFrom_covers valid.linear (Nat.zero_le position) inside

theorem Valid.offset_injective (valid : Valid family caps bytes graph)
    {i j : graph.Index} (same : (graph.node i).offset = (graph.node j).offset) : i = j := by
  have notLess : ¬i.val < j.val := by
    intro ordered
    have strict := linearFrom_strict valid.linear i j ordered
    change (graph.node i).offset < (graph.node j).offset at strict
    omega
  have notGreater : ¬j.val < i.val := by
    intro ordered
    have strict := linearFrom_strict valid.linear j i ordered
    change (graph.node j).offset < (graph.node i).offset at strict
    omega
  apply Fin.ext
  omega

def Valid.entry (valid : Valid family caps bytes graph) : graph.Index :=
  ⟨0, valid.nonempty⟩

theorem Valid.entry_offset (valid : Valid family caps bytes graph) :
    (graph.node valid.entry).offset = 0 := by
  cases nodes : graph.nodes with
  | nil => have nonempty := valid.nonempty; simp [nodes] at nonempty
  | cons node rest =>
    have linear := valid.linear
    simp only [nodes, linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] at linear
    simpa only [Graph.node, Valid.entry, nodes, List.getElem_cons_zero] using linear.1

theorem Valid.entry_cutpoint (valid : Valid family caps bytes graph) :
    (graph.node valid.entry).cutpoint = true := valid.entryCutpoint valid.entry rfl

end EDSL.X86.VCGen.MixedCFG

#audit_edsl
