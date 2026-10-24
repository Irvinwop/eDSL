/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.LocalInvariant

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Generic ranks for the existing every-node local rules and explicit mixed ghosts.
The laws concern the current invariant, authenticated idle extensions and the
existing actual retirement/Follow evidence. Both cut and interior arrivals
decrease; ordinary RET keeps its original historical Post.

The measure reads this ghost's exact current node, state and entire history.
Actual Advance preserves or lowers it, and an own unblocked issue lowers it
strictly. Present empty queues exclude blocking using the actual step's origin;
present running residuals enable one current issue. No future successful run,
final value, fairness, termination, native execution or cost claim is supplied.
All imported target, resource, lifetime and memory-model contracts remain.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Independent rank laws over the existing local invariant. Idle equality
requires that invariant; retirement strengthens both arrivals without changing
Post at RET or adding a current/future execution admission. -/
structure RankLaws {d : Descriptor} {Post : Assertion} (rules : LocalRules d Post) where
  rank : d.graph.Index → S → Log → Nat
  positive : ∀ {node : d.graph.Index} {state : S} {history : Log},
    rules.Inv node state history → 0 < rank node state history
  idle : ∀ {node : d.graph.Index} {before after : S} {history extended : Log},
    Idle d.profile d.tid (before, history) (after, extended) d.family →
    rules.Inv node before history → rank node after extended = rank node before history
  retired : ∀ {node : d.graph.Index} {before : S} {history : Log}
      {af : Bool} {result : S × O} {retirement : Retirement},
    rules.Inv node before history →
    RetiredEvidence d node before af result retirement →
    Follow d Post rules.Inv rules.Inv node before history af result retirement →
    Follow d Post
      (fun destination state past => rules.Inv destination state past ∧
        rank destination state past < rank node before history)
      (fun destination state past => rules.Inv destination state past ∧
        rank destination state past < rank node before history)
      node before history af result retirement

/-- Done has zero remaining measure. Running evaluates the supplied rank on
this explicit ghost's current node, current state and full connected history;
block fuel and projections of the history are not used. -/
def Ghost.measure {d : Descriptor} {initial : S} {Post : Assertion}
    (rank : d.graph.Index → S → Log → Nat) (ghost : Ghost d initial Post) : Nat :=
  match ghost.control with
  | .running node _ => rank node ghost.current ghost.history
  | .done _ => 0

/-- Specialize the independent local continuation to one actual unblocked
step, then align its destination with the actual still-running binding.
This uses checked resumption and forward reification, never an origin converse. -/
theorem RankLaws.rank_lt_of_step {d : Descriptor} {Post : Assertion}
    {rules : LocalRules d Post} (laws : RankLaws rules)
    {node destination : d.graph.Index} {before after : S} {history : Log}
    {af : Bool} {seen : O} {worker successor : Worker}
    (frame : Frame d before) (binding : Binding d node before worker)
    (invariant : rules.Inv node before history)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (after, seen))
    (unblocked : seen ≠ .blocked d.tid)
    (nextBinding : Binding d destination after successor) :
    laws.rank destination after (issueLog d before history af (after, seen)) <
      laws.rank node before history := by
  have one := rules.step node before history worker frame binding invariant
  rcases One.resume_of_step frame one actual with blocked | ⟨retirement, retired, follows⟩
  · exact False.elim (unblocked (congrArg Prod.snd blocked))
  · have strengthened := laws.retired invariant retired follows
    have afterFrame := frame.step actual
    cases retirement with
    | ordinary observation =>
      cases retired with
      | ordinary issued =>
        cases outcome : observation.result with
        | atomic event output => simp only [Follow, outcome] at strengthened
        | syscall request => simp only [Follow, outcome] at strengthened
        | returned output =>
          obtain ⟨current, live, coherence⟩ := issued.reifies
          rw [outcome] at coherence
          have same : current = successor := Option.some.inj (live.symm.trans nextBinding.live)
          have impossible : Phase.returned = .running := by
            exact coherence.2.1.symm.trans ((congrArg Worker.phase same).trans nextBinding.running)
          cases impossible
        | next output =>
          simp only [Follow, outcome] at strengthened
          obtain ⟨next, _edge, pc, retained⟩ := strengthened
          obtain ⟨current, currentBinding⟩ := afterFrame.next_binding issued.reifies outcome pc
          have nodeEq := Binding.node_eq afterFrame currentBinding nextBinding
          subst next
          have ranked : rules.Inv destination after
                (issueLog d before history af (after, seen)) ∧
              laws.rank destination after (issueLog d before history af (after, seen)) <
                laws.rank node before history := by
            simpa only [ite_self] using retained
          exact ranked.2
    | rmw output machine =>
      cases retired with
      | rmw issued =>
        change jump d
          (fun next state past => rules.Inv next state past ∧
            laws.rank next state past < laws.rank node before history)
          (fun next state past => rules.Inv next state past ∧
            laws.rank next state past < laws.rank node before history)
          node machine.state.rip after (issueLog d before history af (after, seen)) at strengthened
        obtain ⟨next, _edge, pc, retained⟩ := strengthened
        obtain ⟨current, currentBinding⟩ := afterFrame.atomic_next_binding issued pc
        have nodeEq := Binding.node_eq afterFrame currentBinding nextBinding
        subst next
        have ranked : rules.Inv destination after
              (issueLog d before history af (after, seen)) ∧
            laws.rank destination after (issueLog d before history af (after, seen)) <
              laws.rank node before history := by
          simpa only [ite_self] using retained
        exact ranked.2

/-- The actual own unblocked Advance strictly lowers this exact ghost's
measure. Ordinary/RMW successors use their real bindings; RET uses positivity
of the current local invariant and the existing done response's zero measure. -/
theorem RankLaws.measure_own_issue {d : Descriptor} {initial : S} {Post : Assertion}
    {rules : LocalRules d Post} (laws : RankLaws rules)
    {before after : Ghost d initial Post} {af : Bool} {seen : O}
    (related : rules.LocalRelated before.current before)
    (advanced : Advance d initial Post before (.issue d.tid af) seen after)
    (unblocked : seen ≠ .blocked d.tid) :
    after.measure laws.rank < before.measure laws.rank := by
  cases advanced with
  | passive quiet _origin => exact False.elim (quiet rfl)
  | blocked _actual => exact False.elim (unblocked rfl)
  | @next before after history af node destination fuel observation output issued outcome _edge pc =>
    have frame : Frame d before := related.1.frame
    obtain ⟨_worker, _instruction, _update, binding, _selected, _ready, _head, _queue, _finish⟩ :=
      issued.witnesses
    obtain ⟨successor, nextBinding⟩ :=
      (frame.step issued.actual).next_binding issued.reifies outcome pc
    exact laws.rank_lt_of_step frame binding related.2 issued.actual unblocked nextBinding
  | @rmw before after history af node destination fuel output machine issued _edge pc =>
    have frame : Frame d before := related.1.frame
    obtain ⟨_worker, _instruction, _identifier, _handle, _cell, binding, _selected,
      _empty, _decoded, _chosen, _changed, _executed, _effect, _installed⟩ := issued.witnesses
    obtain ⟨successor, nextBinding⟩ := (frame.step issued.actual).atomic_next_binding issued pc
    exact laws.rank_lt_of_step frame binding related.2 issued.actual unblocked nextBinding
  | returned response => exact laws.positive related.2

/-- Every existing Advance is nonincreasing from LocalRelated. Passive and
blocked positions append their exact ticks and use invariant-dependent idle
equality; all three retiring constructors use strict own-issue decrease. -/
theorem RankLaws.measure_advance {d : Descriptor} {initial : S} {Post : Assertion}
    {rules : LocalRules d Post} (laws : RankLaws rules)
    {before after : Ghost d initial Post} {action : Action} {seen : O}
    (related : rules.LocalRelated before.current before)
    (advanced : Advance d initial Post before action seen after) :
    after.measure laws.rank ≤ before.measure laws.rank := by
  cases advanced with
  | @passive before after history action seen control quiet origin =>
    cases control with
    | running node fuel =>
      exact Nat.le_of_eq (laws.idle (Idle.step quiet origin) related.2)
    | done response => exact Nat.le_refl 0
  | blocked actual =>
    exact Nat.le_of_eq (laws.idle (Idle.blocked_step actual) related.2)
  | next issued outcome edge pc =>
    exact Nat.le_of_lt (laws.measure_own_issue related (.next issued outcome edge pc) (by intro h; cases h))
  | rmw issued edge pc =>
    exact Nat.le_of_lt (laws.measure_own_issue related (.rmw issued edge pc) (by intro h; cases h))
  | returned response =>
    exact Nat.le_of_lt (laws.measure_own_issue related (.returned response) (by intro h; cases h))

/-- Current empty FIFOs rule out the blocked label for an actual own issue.
The contradiction reads the actual origin's live worker and current queue. -/
private theorem rank_unblocked_of_quiescent {d : Descriptor} {before after : S}
    {af : Bool} {seen : O} (empty : Quiescent before)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (after, seen)) :
    seen ≠ .blocked d.tid := by
  intro blocked
  subst seen
  cases step_origin actual with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _admitted _bounds _decoded _reads _queue _executed finish => cases finish
  | blocked live _running _code _caller _fetched _bounds nonempty =>
    exact nonempty (empty _ (List.mem_of_getElem? live))

/-- Lift one actual own issue from the current exact ghost with empty queues.
Both endpoint witnesses refer to the same supplied/chosen ghosts as LocalStep. -/
theorem RankLaws.own_step_from_current {d : Descriptor} {initial after : S}
    {Post : Assertion} {rules : LocalRules d Post} (laws : RankLaws rules)
    {ghost : Ghost d initial Post} {af : Bool} {seen : O}
    (related : rules.LocalRelated ghost.current ghost)
    (empty : Quiescent ghost.current)
    (actual : TSO64.step ghost.current (.issue d.tid af) d.profile d.family = .ok (after, seen)) :
    ∃ next, rules.LocalRelated after next ∧
      rules.LocalStep ghost (.issue d.tid af) seen next ∧
      next.measure laws.rank < ghost.measure laws.rank := by
  obtain ⟨next, advanced, nextRelated⟩ :=
    rules.localSimulation.lift related.1.frame.wellFormed related actual
  exact ⟨next, nextRelated, advanced,
    laws.measure_own_issue related advanced.2.1 (rank_unblocked_of_quiescent empty actual)⟩

/-- A present running residual enables either AF choice. With currently empty
queues its one actual issue has a strictly smaller exact successor measure.
This constructs only one current step, without assuming a future schedule. -/
theorem RankLaws.own_enabled_from_current {d : Descriptor} {initial : S}
    {Post : Assertion} {rules : LocalRules d Post} (laws : RankLaws rules)
    {ghost : Ghost d initial Post} {node : d.graph.Index} {fuel : Nat}
    (related : rules.LocalRelated ghost.current ghost)
    (running : ghost.control = .running node fuel)
    (empty : Quiescent ghost.current) (af : Bool) :
    ∃ (after : S) (seen : O) (next : Ghost d initial Post),
      TSO64.step ghost.current (.issue d.tid af) d.profile d.family = .ok (after, seen) ∧
      rules.LocalRelated after next ∧ rules.LocalStep ghost (.issue d.tid af) seen next ∧
      next.measure laws.rank < ghost.measure laws.rank := by
  have residual : Residual d initial Post rules.annotations.Inv fuel node ghost.current ghost.history := by
    have retained := related.1.2
    simpa only [running] using retained
  have enabled : ∃ result,
      TSO64.step ghost.current (.issue d.tid af) d.profile d.family = .ok result := by
    cases fuel with
    | zero => exact False.elim residual.generated
    | succ fuel => exact residual.enabled af
  obtain ⟨⟨after, seen⟩, actual⟩ := enabled
  obtain ⟨next, nextRelated, advanced, smaller⟩ := laws.own_step_from_current related empty actual
  exact ⟨after, seen, next, actual, nextRelated, advanced, smaller⟩

#print axioms RankLaws
#print axioms Ghost.measure
#print axioms RankLaws.rank_lt_of_step
#print axioms RankLaws.measure_own_issue
#print axioms RankLaws.measure_advance
#print axioms rank_unblocked_of_quiescent
#print axioms RankLaws.own_step_from_current
#print axioms RankLaws.own_enabled_from_current

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
