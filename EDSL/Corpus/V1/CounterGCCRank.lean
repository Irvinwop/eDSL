/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterGCC
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
A local termination-rank certificate for the existing complete GCC graph.
The requested count is the independent call input; the current count is the
own-RMW Nat count of the full history. Bounds are consequences of the existing
every-node invariant, without additional admission or future-run hypotheses.

The finite stage certificate quantifies over the actual graph's instruction
tags and successor relation, already authenticated by CounterMixedGraphs.
It includes ordinary backedges into cutpoints and the tails after the last
RMW. It supplies local rank laws, not a scheduler, a completed execution,
fairness, a compiler refinement, or corpus/progress credit. All imported
target, resource, lifetime and memory-model assumptions remain in force.
-/

namespace EDSL.Corpus.V1.CounterGCC.TerminationRank
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon

private theorem index_values (node : Index) :
    node.val = 0 ∨ node.val = 1 ∨ node.val = 2 ∨ node.val = 3 ∨
    node.val = 4 ∨ node.val = 5 ∨ node.val = 6 ∨ node.val = 7 ∨
    node.val = 8 ∨ node.val = 9 ∨ node.val = 10 ∨ node.val = 11 ∨
    node.val = 12 ∨ node.val = 13 ∨ node.val = 14 ∨ node.val = 15 ∨ node.val = 16 := by
  have bound : node.val < 17 := node.isLt
  omega

private theorem arithmetic_count_le_requested {call : Call} {node : Index}
    {context : Context} {count : Nat}
    (prior : arithmetic call node context count) : count ≤ call.iterations.toNat := by
  rcases index_values node with atNode | atNode | atNode | atNode | atNode |
    atNode | atNode | atNode | atNode | atNode | atNode | atNode | atNode |
    atNode | atNode | atNode | atNode <;>
    simp only [arithmetic, atNode] at prior <;> omega

/-- Every current GCC invariant bounds the own count by the independent input,
including node 13, where the final RMW may already have exhausted the count. -/
theorem count_le_requested {site : Site .defaultGCC} {call : Call} {node : Index}
    {state : S} {history : Log} (prior : invariant site call node state history) :
    Mixed.Counts.logRMW site.tid history ≤ call.iterations.toNat := by
  obtain ⟨_worker, _binding, _data, _increments, localFact⟩ := prior
  exact arithmetic_count_le_requested localFact.2

private theorem locked_node_certificate : ∀ node : Index,
    (match ((CounterMixedGraphs.graph .defaultGCC).node node).instruction with
    | .ordinary _ => false
    | .locked _ => true) = true →
      node.val = 6 ∨ node.val = 11 ∨ node.val = 12 := by
  decide +kernel

/-- Classification uses the existing graph's actual locked instruction tag. -/
theorem locked_nodes {node : Index} {instruction : AddRMW64.Instruction}
    (locked : ((CounterMixedGraphs.graph .defaultGCC).node node).instruction =
      .locked instruction) : node.val = 6 ∨ node.val = 11 ∨ node.val = 12 := by
  exact locked_node_certificate node (by simp only [locked])

/-- There is remaining budget at each actual locked node: 6, 11 and 12.
No register-width assumption beyond the existing low32 invariant is added. -/
theorem locked_count_lt_requested {site : Site .defaultGCC} {call : Call} {node : Index}
    {state : S} {history : Log} {instruction : AddRMW64.Instruction}
    (prior : invariant site call node state history)
    (locked : ((descriptor site call).graph.node node).instruction = .locked instruction) :
    Mixed.Counts.logRMW site.tid history < call.iterations.toNat := by
  obtain ⟨_worker, _binding, _data, _increments, localFact⟩ := prior
  have arithmeticFact := localFact.2
  rcases locked_nodes locked with atNode | atNode | atNode <;>
    simp only [arithmetic, atNode] at arithmeticFact <;> omega

/-- Small positive stages for all seventeen actual GCC instruction nodes. -/
def stage (node : Index) : Nat :=
  match node.val with
  | 0 => 7
  | 1 => 6
  | 2 => 5
  | 3 => 4
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | 7 => 5
  | 8 => 4
  | 9 => 3
  | 10 => 2
  | 11 => 1
  | 12 => 1
  | 13 => 3
  | 14 => 2
  | 15 => 1
  | 16 => 1
  | _ => 1

private theorem stage_certificate : ∀ node : Index, 0 < stage node ∧ stage node < 16 := by
  decide +kernel

theorem stage_positive (node : Index) : 0 < stage node := (stage_certificate node).1

theorem stage_lt_sixteen (node : Index) : stage node < 16 := (stage_certificate node).2

private theorem ordinary_edge_certificate : ∀ source destination : Index,
    (match ((CounterMixedGraphs.graph .defaultGCC).node source).instruction with
    | .ordinary _ => true
    | .locked _ => false) = true →
      (CounterMixedGraphs.graph .defaultGCC).Edge source destination →
        stage destination < stage source := by
  unfold VCGen.MixedCFG.Graph.Edge
  decide +kernel

/-- Every ordinary successor strictly decreases stage, including the genuine
14 → 11 loop edge. RET has no graph successors. Locked edges may reset stage. -/
theorem ordinary_stage_decreases {source destination : Index}
    {instruction : Sequential.Instruction}
    (ordinary : ((CounterMixedGraphs.graph .defaultGCC).node source).instruction =
      .ordinary instruction)
    (edge : (CounterMixedGraphs.graph .defaultGCC).Edge source destination) :
    stage destination < stage source := by
  exact ordinary_edge_certificate source destination (by simp only [ordinary]) edge

/-- A unit own RMW spends exactly one unit of remaining Nat budget. -/
theorem remaining_unit {requested count : Nat} (room : count < requested) :
    requested - (count + 1) + 1 = requested - count := by
  omega

/-- One budget unit pays for every destination stage below sixteen. This
algebra requires the pre-increment bound before using truncated subtraction. -/
theorem unit_rank_decreases {requested count beforeStage afterStage : Nat}
    (room : count < requested) (boundedStage : afterStage < 16) :
    16 * (requested - (count + 1)) + afterStage <
      16 * (requested - count) + beforeStage := by
  have remaining := remaining_unit room
  omega

/-- State is explicit for use by a later generic rank adapter; the measure
depends only on the independent request, the full history count and the node. -/
def rank (site : Site .defaultGCC) (call : Call) (node : Index)
    (_state : S) (history : Log) : Nat :=
  16 * (call.iterations.toNat - Mixed.Counts.logRMW site.tid history) + stage node

/-- Positive even at zero remaining count, so the actual RET still has work. -/
theorem rank_positive (site : Site .defaultGCC) (call : Call) (node : Index)
    (state : S) (history : Log) : 0 < rank site call node state history := by
  have positive := stage_positive node
  unfold rank
  omega

/-- Authenticated idle extensions preserve the exact own count and rank. -/
theorem rank_idle_eq {site : Site .defaultGCC} {call : Call} {node : Index}
    {before after : S} {history extended : Log}
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic) :
    rank site call node after extended = rank site call node before history := by
  simp only [rank, Mixed.Counts.logRMW_idle idle]

/-- Ordinary graph edges decrease rank whenever the own count is unchanged. -/
theorem ordinary_rank_decreases {site : Site .defaultGCC} {call : Call}
    {source destination : Index} {before after : S} {history extended : Log}
    {instruction : Sequential.Instruction}
    (ordinary : ((descriptor site call).graph.node source).instruction = .ordinary instruction)
    (edge : (descriptor site call).graph.Edge source destination)
    (sameCount : Mixed.Counts.logRMW site.tid extended = Mixed.Counts.logRMW site.tid history) :
    rank site call destination after extended < rank site call source before history := by
  have smaller := ordinary_stage_decreases ordinary edge
  simp only [rank, sameCount]
  omega

/-- At an actual locked node, a unit own-count increment decreases rank for
any destination stage. No desired final count or RAM reconstruction is assumed. -/
theorem rmw_rank_decreases {site : Site .defaultGCC} {call : Call}
    {source destination : Index} {before after : S} {history extended : Log}
    {instruction : AddRMW64.Instruction}
    (prior : invariant site call source before history)
    (locked : ((descriptor site call).graph.node source).instruction = .locked instruction)
    (unitCount : Mixed.Counts.logRMW site.tid extended =
      Mixed.Counts.logRMW site.tid history + 1) :
    rank site call destination after extended < rank site call source before history := by
  have room := locked_count_lt_requested prior locked
  simp only [rank, unitCount]
  exact unit_rank_decreases room (stage_lt_sixteen destination)

/-- Strengthen both cut and interior arrivals using their existing edge. -/
private theorem jump_with_rank {site : Site .defaultGCC} {call : Call}
    {source : Index} {before after : S} {history extended : Log} {rip : Word}
    (decreases : ∀ destination, (descriptor site call).graph.Edge source destination →
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
theorem follow_rank_decreases {site : Site .defaultGCC} {call : Call} {node : Index}
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
      exact ordinary_rank_decreases selected edge sameCount
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
    exact rmw_rank_decreases prior selected increment

#print axioms index_values
#print axioms arithmetic_count_le_requested
#print axioms count_le_requested
#print axioms locked_node_certificate
#print axioms locked_nodes
#print axioms locked_count_lt_requested
#print axioms stage
#print axioms stage_certificate
#print axioms stage_positive
#print axioms stage_lt_sixteen
#print axioms ordinary_edge_certificate
#print axioms ordinary_stage_decreases
#print axioms remaining_unit
#print axioms unit_rank_decreases
#print axioms rank
#print axioms rank_positive
#print axioms rank_idle_eq
#print axioms ordinary_rank_decreases
#print axioms rmw_rank_decreases
#print axioms jump_with_rank
#print axioms follow_rank_decreases

end EDSL.Corpus.V1.CounterGCC.TerminationRank

#audit_edsl
