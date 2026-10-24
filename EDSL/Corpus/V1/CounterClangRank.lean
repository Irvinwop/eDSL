/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterClang
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
An independent rank certificate for the existing complete Clang counter graph.
The requested count is the call's uint32 argument; the tally is the exact Nat
count of own RMW observations in the entire history. Bounds follow from the
existing every-node invariant, with no new admission or execution hypothesis.

Stages are checked against the checked graph's production successor relation.
They decrease across every ordinary edge, including both loop backedges, and
the remaining Nat budget pays for a stage reset after an own RMW. This module
does not construct a scheduler or reprove any instruction continuation.
-/

namespace EDSL.Corpus.V1.CounterClangRank
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon CounterClang

abbrev Index := CounterClang.Index

abbrev graph := CounterMixedGraphs.graph .defaultClang

local instance (source destination : Index) : Decidable (graph.Edge source destination) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Pure arithmetic projection of the already established local invariant. -/
theorem local_count_le_requested {call : Call} {node : Index} {context : Context}
    {count : Nat} (prior : localInvariant call node context count) :
    count ≤ call.iterations.toNat := by
  have remainderBound := remainder_le call
  have nodeBound := node.isLt
  unfold localInvariant at prior
  obtain ⟨_rsi, arithmetic⟩ := prior
  split at arithmetic <;>
    (try simp only [RemainderHead, RemainderIssued, RemainderCompared, PrologueDone,
      MainHead] at arithmetic) <;> omega

/-- Every running node bounds the exact entire-history Nat tally by the
independently requested count, including node25's exhausted-count tail. -/
theorem count_le_requested {site : Site .defaultClang} {call : Call} {node : Index}
    {state : S} {history : Log} (prior : invariant site call node state history) :
    Mixed.Counts.logRMW site.tid history ≤ call.iterations.toNat := by
  obtain ⟨_worker, _binding, _data, _increments, arithmetic⟩ := prior
  exact local_count_le_requested arithmetic

/-- Locked classification reads the actual tagged graph. -/
def isLocked (node : Index) : Bool :=
  match (graph.node node).instruction with
  | .ordinary _ => false
  | .locked _ => true

/-- This finite certificate recognizes locked sites from the actual tagged
graph, rather than trusting a separately supplied list of RMW edges. -/
theorem locked_sites (node : Index) :
    isLocked node = true ↔
    (node.val = 8 ∨ (17 ≤ node.val ∧ node.val ≤ 24)) := by
  have certificate : ∀ node : Index,
      isLocked node = true ↔
      (node.val = 8 ∨ (17 ≤ node.val ∧ node.val ≤ 24)) := by decide +kernel
  exact certificate node

/-- Before each actual locked INC the remaining Nat budget is nonzero. -/
theorem local_locked_count_lt_requested {call : Call} {node : Index} {context : Context}
    {count : Nat} {instruction : RMWFamily.Instruction .arithmetic}
    (prior : localInvariant call node context count)
    (locked : (graph.node node).instruction = .locked instruction) :
    count < call.iterations.toNat := by
  have sites : node.val = 8 ∨ (17 ≤ node.val ∧ node.val ≤ 24) := by
    apply (locked_sites node).mp
    simp only [isLocked, locked]
  have remainderBound := remainder_le call
  unfold localInvariant at prior
  obtain ⟨_rsi, arithmetic⟩ := prior
  split at arithmetic <;>
    (try simp only [RemainderHead, RemainderIssued, RemainderCompared, PrologueDone,
      MainHead] at arithmetic) <;> omega

theorem locked_count_lt_requested {site : Site .defaultClang} {call : Call} {node : Index}
    {state : S} {history : Log} {instruction : RMWFamily.Instruction .arithmetic}
    (prior : invariant site call node state history)
    (locked : ((descriptor site call).graph.node node).instruction = .locked instruction) :
    Mixed.Counts.logRMW site.tid history < call.iterations.toNat := by
  obtain ⟨_worker, _binding, _data, _increments, arithmetic⟩ := prior
  exact local_locked_count_lt_requested arithmetic locked

/-- Small untrusted stage proposal. The laws below check it against graph
edges, independently of these assigned values and of the graph's cut depths. -/
def stage (node : Index) : Nat :=
  match node.val with
  | 0 => 10
  | 1 | 9 => 9
  | 2 | 10 => 8
  | 3 | 11 => 7
  | 4 | 12 => 6
  | 5 | 13 => 5
  | 14 => 4
  | 6 | 15 | 25 => 3
  | 7 | 16 | 26 => 2
  | _ => 1

/-- Reversed ordinary successor relation, so accessibility means there is no
infinite forward path after outgoing locked edges are removed. -/
def OrdinaryEdge (destination source : Index) : Prop :=
  match (graph.node source).instruction with
  | .ordinary _ => graph.Edge source destination
  | .locked _ => False

local instance (destination source : Index) : Decidable (OrdinaryEdge destination source) := by
  unfold OrdinaryEdge
  split <;> infer_instance

/-- A finite proof over every actual graph edge, not a test of assigned stages. -/
theorem stage_certificate :
    (∀ node : Index, 0 < stage node ∧ stage node < 16) ∧
    (∀ source destination : Index, OrdinaryEdge destination source →
      stage destination < stage source) := by
  decide +kernel

theorem stage_bounds (node : Index) : 0 < stage node ∧ stage node < 16 :=
  stage_certificate.1 node

theorem ordinary_edge_stage {source destination : Index}
    (edge : OrdinaryEdge destination source) : stage destination < stage source :=
  stage_certificate.2 source destination edge

theorem ordinary_stage_decreases {source destination : Index}
    {instruction : Sequential.Instruction}
    (ordinary : (graph.node source).instruction = .ordinary instruction)
    (edge : graph.Edge source destination) : stage destination < stage source := by
  apply ordinary_edge_stage
  unfold OrdinaryEdge
  rw [ordinary]
  exact edge

theorem ordinary_edges_wellFounded : WellFounded OrdinaryEdge :=
  Subrelation.wf (fun edge => ordinary_edge_stage edge)
    (InvImage.wf stage Nat.lt_wfRel.wf)

/-- Production decode authentication accompanies the stage certificate.
No byte window or successor relation is reconstructed for this module. -/
theorem decoded_stage_certificate :
    X86.VCGen.MixedCFG.Valid .arithmetic (CounterMixedGraphs.caps .defaultClang)
      (CounterMixedGraphs.bytes .defaultClang) graph ∧
    (∀ node : Index, 0 < stage node ∧ stage node < 16) ∧
    (∀ source destination : Index, OrdinaryEdge destination source →
      stage destination < stage source) :=
  ⟨CounterMixedGraphs.structural .defaultClang, stage_certificate⟩

/-- Rank of a running node, based only on the requested count and own history. -/
def rank (site : Site .defaultClang) (call : Call) (node : Index)
    (_state : S) (history : Log) : Nat :=
  16 * (call.iterations.toNat - Mixed.Counts.logRMW site.tid history) + stage node

theorem rank_positive (site : Site .defaultClang) (call : Call) (node : Index)
    (state : S) (history : Log) : 0 < rank site call node state history := by
  have positive := (stage_bounds node).1
  unfold rank
  omega

theorem rank_idle {site : Site .defaultClang} {call : Call} {node : Index}
    {before after : S} {history extended : Log}
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic) :
    rank site call node after extended = rank site call node before history := by
  unfold rank
  rw [Mixed.Counts.logRMW_idle idle]

/-- At unit-increment sites an arbitrary stage reset below sixteen is paid
for by the remaining Nat budget; the strict count bound prevents truncation. -/
theorem unit_increment_decreases {requested count beforeStage afterStage : Nat}
    (below : count < requested) (positive : 0 < beforeStage) (small : afterStage < 16) :
    16 * (requested - (count + 1)) + afterStage <
      16 * (requested - count) + beforeStage := by
  omega

theorem rank_ordinary_decreases {site : Site .defaultClang} {call : Call}
    {source destination : Index} {before after : S} {history extended : Log}
    {instruction : Sequential.Instruction}
    (ordinary : (graph.node source).instruction = .ordinary instruction)
    (edge : graph.Edge source destination)
    (sameCount : Mixed.Counts.logRMW site.tid extended = Mixed.Counts.logRMW site.tid history) :
    rank site call destination after extended < rank site call source before history := by
  have stages := ordinary_stage_decreases ordinary edge
  unfold rank
  rw [sameCount]
  omega

theorem rank_locked_decreases {site : Site .defaultClang} {call : Call}
    {source destination : Index} {before after : S} {history extended : Log}
    {instruction : RMWFamily.Instruction .arithmetic}
    (prior : invariant site call source before history)
    (locked : (graph.node source).instruction = .locked instruction)
    (increment : Mixed.Counts.logRMW site.tid extended = Mixed.Counts.logRMW site.tid history + 1) :
    rank site call destination after extended < rank site call source before history := by
  have below := locked_count_lt_requested prior locked
  unfold rank
  rw [increment]
  exact unit_increment_decreases below (stage_bounds source).1 (stage_bounds destination).2

/-- Strengthen both cut and interior arrivals using their existing edge. -/
private theorem jump_with_rank {site : Site .defaultClang} {call : Call}
    {source : Index} {before after : S} {history extended : Log} {rip : Word}
    (decreases : ∀ destination, graph.Edge source destination →
      rank site call destination after extended < rank site call source before history)
    (follows : Mixed.jump (descriptor site call) (invariant site call) (invariant site call)
      source rip after extended) :
    Mixed.jump (descriptor site call)
      (fun node state past => invariant site call node state past ∧
        rank site call node state past < rank site call source before history)
      (fun node state past => invariant site call node state past ∧
        rank site call node state past < rank site call source before history)
      source rip after extended := by
  obtain ⟨destination, edge, pc, next⟩ := follows
  refine ⟨destination, edge, pc, ?_⟩
  have nextInvariant : invariant site call destination after extended := by
    split at next <;> exact next
  split <;> exact ⟨nextInvariant, decreases destination edge⟩

/-- The rank adapter consumes the existing actual retirement and compiler
continuation. Ordinary labels preserve k; locked labels increment it exactly.
Actual RET keeps its original Post, for a parent engine's done rank of zero. -/
theorem follow_rank_decreases {site : Site .defaultClang} {call : Call} {node : Index}
    {before : S} {history : Log} {af : Bool} {result : S × O} {retirement : Mixed.Retirement}
    (prior : invariant site call node before history)
    (issued : Mixed.RetiredEvidence (descriptor site call) node before af result retirement)
    (follows : Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
      (invariant site call) (invariant site call) node before history af result retirement) :
    Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
      (fun destination state past => invariant site call destination state past ∧
        rank site call destination state past < rank site call node before history)
      (fun destination state past => invariant site call destination state past ∧
        rank site call destination state past < rank site call node before history)
      node before history af result retirement := by
  cases issued with
  | @ordinary observation evidence =>
    obtain ⟨_worker, _instruction, _update, _binding, selected, _ready, _head, _queue, _finish⟩ :=
      evidence.witnesses
    cases outcome : observation.result with
    | next output =>
      obtain ⟨_current, _live, reified⟩ := evidence.reifies
      have label : result.2 = .ordinary site.tid := by
        simp only [outcome] at reified
        exact reified.1
      have sameCount : Mixed.Counts.logRMW site.tid
          (Mixed.issueLog (descriptor site call) before history af result) =
          Mixed.Counts.logRMW site.tid history := by
        unfold Mixed.issueLog
        rw [Mixed.Counts.logRMW_snoc]
        simp only [label, Mixed.Counts.ownRMW_ordinary, Nat.add_zero]
      simp only [Mixed.Follow, outcome] at follows ⊢
      apply jump_with_rank (follows := follows)
      intro destination edge
      exact rank_ordinary_decreases selected edge sameCount
    | returned output => simpa only [Mixed.Follow, outcome] using follows
    | atomic event output => simp only [Mixed.Follow, outcome] at follows
    | syscall request => simp only [Mixed.Follow, outcome] at follows
  | @rmw output machine evidence =>
    obtain ⟨_worker, _instruction, _identifier, _handle, _cell, _binding, selected,
      _empty, _decoded, _chosen, _changed, _executed, _effect, installed⟩ := evidence.witnesses
    have label : result.2 = .rmw site.tid output.2 := congrArg Prod.snd installed
    have increment : Mixed.Counts.logRMW site.tid
        (Mixed.issueLog (descriptor site call) before history af result) =
        Mixed.Counts.logRMW site.tid history + 1 := by
      unfold Mixed.issueLog
      rw [Mixed.Counts.logRMW_snoc, label, Mixed.Counts.ownRMW_rmw, ite_eq_left rfl]
    simp only [Mixed.Follow] at follows ⊢
    apply jump_with_rank (follows := follows)
    intro destination _edge
    exact rank_locked_decreases prior selected increment

#print axioms Index
#print axioms graph
#print axioms local_count_le_requested
#print axioms count_le_requested
#print axioms isLocked
#print axioms locked_sites
#print axioms local_locked_count_lt_requested
#print axioms locked_count_lt_requested
#print axioms stage
#print axioms OrdinaryEdge
#print axioms stage_certificate
#print axioms stage_bounds
#print axioms ordinary_edge_stage
#print axioms ordinary_stage_decreases
#print axioms ordinary_edges_wellFounded
#print axioms decoded_stage_certificate
#print axioms rank
#print axioms rank_positive
#print axioms rank_idle
#print axioms unit_increment_decreases
#print axioms rank_ordinary_decreases
#print axioms rank_locked_decreases
#print axioms jump_with_rank
#print axioms follow_rank_decreases

end EDSL.Corpus.V1.CounterClangRank

#audit_edsl
