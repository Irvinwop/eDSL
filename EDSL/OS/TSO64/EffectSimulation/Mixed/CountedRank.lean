/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedLocal
import EDSL.OS.TSO64.EffectSimulation.Mixed.Counts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Reusable counted-stage ranks for arbitrary mixed local rules. The independent
request bounds the number of own RMW observations; a positive graph stage pays
for the ordinary instructions between them. Ordinary edges must decrease stage,
including edges into cutpoints. Strict room at locked nodes prevents truncated
Nat subtraction from hiding an extra RMW.

Retirement reads the actual ordinary or locked issued evidence, so providers do
not supply label/count correspondence. Both arrivals gain a strict decrease;
ordinary RET retains the original Post. This layer does not establish the RMW
payload, its target, the call's ABI, a scheduler, fairness, minimum cost, or a
physical hardware/OS refinement. The supplied local and environmental contracts
remain unchanged.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

namespace CountedRank

/-- State remains explicit for the existing rank interface. The measure uses
the independent request, the full own-RMW history count and the current node. -/
def rank {d : Descriptor} (requested stride : Nat) (stage : d.graph.Index → Nat)
    (node : d.graph.Index) (_state : S) (history : Log) : Nat :=
  stride * (requested - Counts.logRMW d.tid history) + stage node

/-- The positive stage leaves work even when no RMW budget remains. -/
theorem positive {d : Descriptor} (requested stride : Nat) (stage : d.graph.Index → Nat)
    (bounds : ∀ node, 0 < stage node ∧ stage node < stride)
    (node : d.graph.Index) (state : S) (history : Log) :
    0 < rank requested stride stage node state history := by
  have above := (bounds node).1
  unfold rank
  omega

/-- Authenticated idle extensions preserve the exact own count. -/
theorem idle {d : Descriptor} (requested stride : Nat) (stage : d.graph.Index → Nat)
    {node : d.graph.Index} {before after : S} {history extended : Log}
    (quiet : Idle d.profile d.tid (before, history) (after, extended) d.family) :
    rank requested stride stage node after extended =
      rank requested stride stage node before history := by
  simp only [rank, Counts.logRMW_idle quiet]

/-- Strict room is required before spending one unit of truncated Nat budget. -/
theorem remaining_unit {requested count : Nat} (room : count < requested) :
    requested - (count + 1) + 1 = requested - count := by
  omega

/-- One budget unit pays for any destination stage below the chosen stride. -/
theorem unit_decreases {requested count stride beforeStage afterStage : Nat}
    (room : count < requested) (bounded : afterStage < stride) :
    stride * (requested - (count + 1)) + afterStage <
      stride * (requested - count) + beforeStage := by
  rw [← remaining_unit room, Nat.mul_add, Nat.mul_one]
  omega

/-- Ordinary stage descent suffices whenever the full own count is retained. -/
theorem ordinary_decreases {d : Descriptor} (requested stride : Nat)
    (stage : d.graph.Index → Nat) {source destination : d.graph.Index}
    {before after : S} {history extended : Log}
    (smaller : stage destination < stage source)
    (same : Counts.logRMW d.tid extended = Counts.logRMW d.tid history) :
    rank requested stride stage destination after extended <
      rank requested stride stage source before history := by
  simp only [rank, same]
  exact Nat.add_lt_add_left smaller _

/-- A real locked issue spends exactly one own-count unit, independently of
its payload. The local invariant supplies room before that issue. -/
theorem locked_decreases {d : Descriptor} (requested stride : Nat)
    (stage : d.graph.Index → Nat) {source destination : d.graph.Index}
    {before after : S} {history extended : Log}
    (room : Counts.logRMW d.tid history < requested)
    (bounded : stage destination < stride)
    (increment : Counts.logRMW d.tid extended = Counts.logRMW d.tid history + 1) :
    rank requested stride stage destination after extended <
      rank requested stride stage source before history := by
  simp only [rank, increment]
  exact unit_decreases room bounded

/-- Strengthen both existing cut and interior arrivals along their real edge. -/
theorem jump_with_rank {d : Descriptor} {Inv : CutAssertion d}
    {rank : d.graph.Index → S → Log → Nat}
    {source : d.graph.Index} {before after : S} {history extended : Log} {rip : Word}
    (decreases : ∀ destination, d.graph.Edge source destination →
      rank destination after extended < rank source before history)
    (follows : jump d Inv Inv source rip after extended) :
    jump d
      (fun node state past => Inv node state past ∧
        rank node state past < rank source before history)
      (fun node state past => Inv node state past ∧
        rank node state past < rank source before history)
      source rip after extended := by
  obtain ⟨destination, edge, pc, next⟩ := follows
  refine ⟨destination, edge, pc, ?_⟩
  have invariant : Inv destination after extended := by
    split at next <;> exact next
  split <;> exact ⟨invariant, decreases destination edge⟩

/-- Actual issued labels determine count preservation or increment. RET keeps
the supplied historical Post; both successor kinds acquire strict decrease. -/
theorem retired {d : Descriptor} {Post : Assertion}
    (Inv : CutAssertion d) (requested stride : Nat)
    (stage : d.graph.Index → Nat)
    (bounds : ∀ node, 0 < stage node ∧ stage node < stride)
    (ordinary : ∀ source destination (instruction : Sequential.Instruction),
      (d.graph.node source).instruction = .ordinary instruction →
      d.graph.Edge source destination → stage destination < stage source)
    (room : ∀ node state history (instruction : RMWFamily.Instruction d.family),
      Inv node state history →
      (d.graph.node node).instruction = .locked instruction →
      Counts.logRMW d.tid history < requested)
    {node : d.graph.Index} {before : S} {history : Log} {af : Bool}
    {result : S × O} {retirement : Retirement}
    (prior : Inv node before history)
    (issued : RetiredEvidence d node before af result retirement)
    (follows : Follow d Post Inv Inv node before history af result retirement) :
    Follow d Post
      (fun destination state past => Inv destination state past ∧
        rank requested stride stage destination state past <
          rank requested stride stage node before history)
      (fun destination state past => Inv destination state past ∧
        rank requested stride stage destination state past <
          rank requested stride stage node before history)
      node before history af result retirement := by
  cases issued with
  | @ordinary observation evidence =>
    obtain ⟨_worker, instruction, _update, _binding, selected, _ready, _head, _queue, _finish⟩ :=
      evidence.witnesses
    cases outcome : observation.result with
    | next output =>
      obtain ⟨_current, _live, reified⟩ := evidence.reifies
      have label : result.2 = .ordinary d.tid := by
        simp only [outcome] at reified
        exact reified.1
      have sameCount : Counts.logRMW d.tid (issueLog d before history af result) =
          Counts.logRMW d.tid history := by
        unfold issueLog
        rw [Counts.logRMW_snoc]
        simp only [label, Counts.ownRMW_ordinary, Nat.add_zero]
      simp only [Follow, outcome] at follows ⊢
      apply jump_with_rank (follows := follows)
      intro destination edge
      exact ordinary_decreases requested stride stage
        (ordinary node destination instruction selected edge) sameCount
    | returned output => simpa only [Follow, outcome] using follows
    | atomic event output => simp only [Follow, outcome] at follows
    | syscall request => simp only [Follow, outcome] at follows
  | @rmw output machine evidence =>
    obtain ⟨_worker, instruction, _identifier, _handle, _cell, _binding, selected,
      _empty, _decoded, _chosen, _changed, _executed, _effect, installed⟩ := evidence.witnesses
    have label : result.2 = .rmw d.tid output.2 := congrArg Prod.snd installed
    have increment : Counts.logRMW d.tid (issueLog d before history af result) =
        Counts.logRMW d.tid history + 1 := by
      unfold issueLog
      rw [Counts.logRMW_snoc, label, Counts.ownRMW_rmw, ite_eq_left rfl]
    simp only [Follow] at follows ⊢
    apply jump_with_rank (follows := follows)
    intro destination _edge
    exact locked_decreases requested stride stage
      (room node before history instruction prior selected) (bounds destination).2 increment

end CountedRank

/-- Construct the existing local rank laws from a graph stage certificate and
strict room at actual locked nodes. The returned rank is definitionally
`stride * (requested - Counts.logRMW d.tid history) + stage node`. -/
def RankLaws.ofCountedStages {d : Descriptor} {Post : Assertion}
    (rules : LocalRules d Post) (requested stride : Nat)
    (stage : d.graph.Index → Nat)
    (bounds : ∀ node, 0 < stage node ∧ stage node < stride)
    (ordinary : ∀ source destination (instruction : Sequential.Instruction),
      (d.graph.node source).instruction = .ordinary instruction →
      d.graph.Edge source destination → stage destination < stage source)
    (room : ∀ node state history (instruction : RMWFamily.Instruction d.family),
      rules.Inv node state history →
      (d.graph.node node).instruction = .locked instruction →
      Counts.logRMW d.tid history < requested) : RankLaws rules where
  rank := CountedRank.rank requested stride stage
  positive := by
    intro node state history _prior
    exact CountedRank.positive requested stride stage bounds node state history
  idle := by
    intro node before after history extended quiet _prior
    exact CountedRank.idle requested stride stage quiet
  retired := CountedRank.retired rules.Inv requested stride stage bounds ordinary room

#print axioms CountedRank.rank
#print axioms CountedRank.positive
#print axioms CountedRank.idle
#print axioms CountedRank.remaining_unit
#print axioms CountedRank.unit_decreases
#print axioms CountedRank.ordinary_decreases
#print axioms CountedRank.locked_decreases
#print axioms CountedRank.jump_with_rank
#print axioms CountedRank.retired
#print axioms RankLaws.ofCountedStages

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
