/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Local

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Every-node local invariant retention for the existing explicit mixed ghosts.
The checked current step and existing local rules determine the continuation;
independently obtained successor graph nodes are aligned through their actual
live worker bindings and the authenticated window's injective offsets. No
stateful ghost histories are identified from their projections. Finite folds
remain conditional on the supplied successful production schedule. This layer
adds no rank, scheduler, termination or new instruction semantics.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- The local invariant belongs to the exact current node, state and full log.
A completed response retains its existing historical Post through Related. -/
def LocalRules.LocalAt {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) (ghost : Ghost d initial Post) : Prop :=
  match ghost.control with
  | .running node _ => rules.Inv node ghost.current ghost.history
  | .done _ => True

/-- Retain both the existing generated residual/response and the every-node
local invariant on the very same explicit ghost. -/
def LocalRules.LocalRelated {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) (state : S) (ghost : Ghost d initial Post) : Prop :=
  Related rules.annotations state ghost ∧ rules.LocalAt ghost

/-- Two bindings to the same live scheduler slot identify graph nodes through
its current RIP and the authenticated, nonwrapping byte window. -/
theorem Binding.node_eq {d : Descriptor} {state : S}
    {left right : d.graph.Index} {first second : Worker}
    (frame : Frame d state) (a : Binding d left state first)
    (b : Binding d right state second) : left = right := by
  have workerEq : first = second := Option.some.inj (a.live.symm.trans b.live)
  have pc : d.base + BitVec.ofNat 64 (d.graph.node left).offset =
      d.base + BitVec.ofNat 64 (d.graph.node right).offset := by
    rw [← a.pc, workerEq, b.pc]
  have leftInside := (d.structural.nodes left).1
  have rightInside := (d.structural.nodes right).1
  have bounded := frame.code.1
  have leftSmall : (d.graph.node left).offset < 2^64 := by omega
  have rightSmall : (d.graph.node right).offset < 2^64 := by omega
  have leftSum : d.base.toNat + (d.graph.node left).offset < 2^64 := by omega
  have rightSum : d.base.toNat + (d.graph.node right).offset < 2^64 := by omega
  have natural := congrArg BitVec.toNat pc
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftSmall,
    Nat.mod_eq_of_lt rightSmall, Nat.mod_eq_of_lt leftSum,
    Nat.mod_eq_of_lt rightSum] at natural
  exact d.structural.offset_injective (by omega)

/-- Any still-running bound successor of the exact checked issue retains Inv.
Blocked issues use authenticated idle transport; retiring continuations use
Follow from the local rules. A returned worker cannot satisfy the running
successor binding. -/
theorem LocalRules.inv_of_step {d : Descriptor} {Post : Assertion}
    (rules : LocalRules d Post) {node destination : d.graph.Index}
    {before after : S} {history : Log} {af : Bool} {seen : O}
    {worker successor : Worker}
    (frame : Frame d before) (binding : Binding d node before worker)
    (invariant : rules.Inv node before history)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (after, seen))
    (nextBinding : Binding d destination after successor) :
    rules.Inv destination after (issueLog d before history af (after, seen)) := by
  have one := rules.step node before history worker frame binding invariant
  rcases One.resume_of_step frame one actual with blocked | ⟨retirement, retired, follows⟩
  · have stateEq : after = before := congrArg Prod.fst blocked
    have seenEq : seen = .blocked d.tid := congrArg Prod.snd blocked
    subst after
    subst seen
    have nodeEq := Binding.node_eq frame binding nextBinding
    subst destination
    exact rules.idle (Idle.blocked_step actual) invariant
  · have afterFrame := frame.step actual
    cases retirement with
    | ordinary observation =>
      cases retired with
      | ordinary issued =>
        cases outcome : observation.result with
        | atomic event output => simp only [Follow, outcome] at follows
        | syscall request => simp only [Follow, outcome] at follows
        | returned output =>
          obtain ⟨current, live, coherence⟩ := issued.reifies
          rw [outcome] at coherence
          have same : current = successor := Option.some.inj (live.symm.trans nextBinding.live)
          have impossible : Phase.returned = .running := by
            exact coherence.2.1.symm.trans ((congrArg Worker.phase same).trans nextBinding.running)
          cases impossible
        | next output =>
          simp only [Follow, outcome] at follows
          obtain ⟨next, _edge, pc, retained⟩ := follows
          obtain ⟨current, currentBinding⟩ := afterFrame.next_binding issued.reifies outcome pc
          have nodeEq := Binding.node_eq afterFrame currentBinding nextBinding
          subst next
          simpa only [ite_self] using retained
    | rmw output machine =>
      cases retired with
      | rmw issued =>
        change jump d rules.Inv rules.Inv node machine.state.rip after
          (issueLog d before history af (after, seen)) at follows
        obtain ⟨next, _edge, pc, retained⟩ := follows
        obtain ⟨current, currentBinding⟩ := afterFrame.atomic_next_binding issued pc
        have nodeEq := Binding.node_eq afterFrame currentBinding nextBinding
        subst next
        simpa only [ite_self] using retained

/-- Present Entry supplies the every-node invariant directly, independently of
its generated residual. No invariant is projected out of rwp.here. -/
theorem LocalRules.localAt_initial {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) {node : d.graph.Index}
    (entry : Entry rules.annotations initial node) :
    rules.LocalAt (initialGhost d initial Post node) :=
  entry.invariant

theorem LocalRules.localRelated_initial {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) {node : d.graph.Index}
    (entry : Entry rules.annotations initial node) :
    rules.LocalRelated initial (initialGhost d initial Post node) :=
  ⟨entry.related, rules.localAt_initial entry⟩

/-- Transport the local assertion along the supplied existing Advance, retaining
its exact destination ghost. Source Related supplies the protected frame. -/
theorem LocalRules.localAt_advance {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) {before after : Ghost d initial Post}
    {action : Action} {seen : O}
    (related : Related rules.annotations before.current before)
    (invariant : rules.LocalAt before)
    (advanced : Advance d initial Post before action seen after) : rules.LocalAt after := by
  cases advanced with
  | @passive before after history action seen control quiet origin =>
    cases control with
    | running node fuel => exact rules.idle (Idle.step quiet origin) invariant
    | done response => trivial
  | blocked actual => exact rules.idle (Idle.blocked_step actual) invariant
  | @next before after history af node destination fuel observation output issued outcome _edge pc =>
    have frame : Frame d before := related.frame
    obtain ⟨_worker, _instruction, _update, binding, _selected, _ready, _head, _queue, _finish⟩ :=
      issued.witnesses
    obtain ⟨successor, nextBinding⟩ :=
      (frame.step issued.actual).next_binding issued.reifies outcome pc
    exact rules.inv_of_step frame binding invariant issued.actual nextBinding
  | @rmw before after history af node destination fuel output machine issued _edge pc =>
    have frame : Frame d before := related.frame
    obtain ⟨_worker, _instruction, _identifier, _handle, _cell, binding, _selected,
      _empty, _decoded, _chosen, _changed, _executed, _effect, _installed⟩ := issued.witnesses
    obtain ⟨successor, nextBinding⟩ := (frame.step issued.actual).atomic_next_binding issued pc
    exact rules.inv_of_step frame binding invariant issued.actual nextBinding
  | returned response => trivial

/-- Enriched transitions retain old Advance and both exact endpoint witnesses.
A LiftTrace of these transitions exposes Inv at every running interior ghost. -/
def LocalRules.LocalStep {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) (before : Ghost d initial Post) (action : Action)
    (seen : O) (after : Ghost d initial Post) : Prop :=
  rules.LocalRelated before.current before ∧ Advance d initial Post before action seen after ∧
    rules.LocalRelated after.current after

/-- Existing checked lifting chooses the actual successor. Its exact Advance
then transports the independently retained local invariant. -/
theorem LocalRules.localSimulation {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) :
    EffectSimulation.CheckedSimulation d.profile (rules.LocalRelated (initial := initial))
      rules.LocalStep d.family := by
  constructor
  intro before after action seen ghost valid related actual
  obtain ⟨next, advanced, nextRelated⟩ :=
    rules.annotations.simulation.lift valid related.1 actual
  have atCurrent : Related rules.annotations ghost.current ghost := by
    simpa only [related.1.1] using related.1
  have nextLocal : rules.LocalRelated after next :=
    ⟨nextRelated, rules.localAt_advance atCurrent related.2 advanced⟩
  have nextAtCurrent : rules.LocalRelated next.current next := by
    simpa only [nextRelated.1] using nextLocal
  exact ⟨next, ⟨⟨atCurrent, related.2⟩, advanced, nextAtCurrent⟩, nextLocal⟩

/-- Forget enrichment without changing any explicit ghost, action or observation. -/
theorem LocalRules.localTrace_forget {d : Descriptor} {initial : S} {Post : Assertion}
    (rules : LocalRules d Post) {before after : Ghost d initial Post}
    {actions : List Action} {observations : List O}
    (trace : LiftTrace rules.LocalStep before actions observations after) :
    LiftTrace (Advance d initial Post) before actions observations after := by
  induction trace with
  | nil => exact .nil
  | cons head _tail ih => exact .cons head.2.1 ih

/-- Fold from a current independently authenticated ghost; each actual tick and
its same full stateful history remains in the enriched trace. -/
theorem LocalRules.localSchedule_from_current {d : Descriptor} {initial before final : S}
    {Post : Assertion} (rules : LocalRules d Post) {ghost : Ghost d initial Post}
    {actions : List Action} {observations : List O}
    (related : rules.LocalRelated before ghost)
    (actual : TSO64.schedule before actions d.profile d.family = .ok (final, observations)) :
    ∃ next, rules.LocalRelated final next ∧
      LiftTrace rules.LocalStep ghost actions observations next :=
  rules.localSimulation.schedule related.1.frame.wellFormed related actual

/-- Entry specialization initializes the invariant separately from Related. -/
theorem LocalRules.localSchedule {d : Descriptor} {initial final : S} {Post : Assertion}
    (rules : LocalRules d Post) {node : d.graph.Index}
    (entry : Entry rules.annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions d.profile d.family = .ok (final, observations)) :
    ∃ next, rules.LocalRelated final next ∧
      LiftTrace rules.LocalStep (initialGhost d initial Post node) actions observations next :=
  rules.localSchedule_from_current (rules.localRelated_initial entry) actual

#print axioms LocalRules.LocalAt
#print axioms LocalRules.LocalRelated
#print axioms Binding.node_eq
#print axioms LocalRules.inv_of_step
#print axioms LocalRules.localAt_initial
#print axioms LocalRules.localRelated_initial
#print axioms LocalRules.localAt_advance
#print axioms LocalRules.LocalStep
#print axioms LocalRules.localSimulation
#print axioms LocalRules.localTrace_forget
#print axioms LocalRules.localSchedule_from_current
#print axioms LocalRules.localSchedule

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
