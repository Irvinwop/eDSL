/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Block
import EDSL.OS.TSO64.EffectSimulation.CheckedLifting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Checked-step simulation for independently annotated mixed blocks. Entry admits
an actual running cutpoint with no future-run premise. Interior retirements
consume fuel; arrival at a cutpoint immediately regenerates its depth-plus-one
block at that exact state and history. Passive steps and exact own blocked
attempts keep control, node and fuel while appending their complete ticks.

Ordinary steps retain their fresh head and complete reification. Locked steps
retain `AtomicIssued`, including the actual selected handle and current coupled
primitive/machine effect. The local law consumes only one current checked step
and specializes the presently enabled residual through `resume_of_step`.
Native origins are derived forward; no origin-to-step converse is supplied.

A response records Post at its exact ordinary RET. Done retains that immutable
response as an exact history prefix and frames the current returned worker.
Idle transport can change RAM and pending queues; it does not transport the
historical Post to a later world. Finite schedule corollaries use the existing
checked fold and retain all original scheduler positions and observations.

The imported target, resource, synchronization, translation and protected-loan
contracts remain assumptions. No fairness, termination, hardware refinement,
counting, ABI, additional lifetime or global-progress theorem is asserted.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Independent cut assertions and generated blocks at their actual arrivals. -/
structure Annotations (d : Descriptor) (Post : Assertion) where
  Inv : CutAssertion d
  blocks : ∀ (cut : d.graph.Index) (state : S) (history : Log) (worker : Worker),
    (d.graph.node cut).cutpoint = true →
    Frame d state → Binding d cut state worker → Inv cut state history →
    rwp d Post Inv ((d.graph.node cut).depth + 1) cut state history

/-- Current admission, running binding and independent cut invariant only. -/
structure Entry {d : Descriptor} {Post : Assertion} (annotations : Annotations d Post)
    (initial : S) (node : d.graph.Index) : Prop where
  admitted : Admission d initial
  cutpoint : (d.graph.node node).cutpoint = true
  binding : Binding d node initial d.original
  invariant : annotations.Inv node initial []

/-- Immutable response from the exact authenticated ordinary return tick. -/
structure Response (d : Descriptor) (initial : S) (Post : Assertion) where
  priorLog : Log
  before : S
  af : Bool
  after : S
  node : d.graph.Index
  observation : Sequential.Observation
  output : X86.State
  issued : OrdinaryIssued d node before af (after, .returned d.tid) observation
  returned : observation.result = .returned output
  authentic : OriginTrace d.profile initial priorLog before d.family
  post : Post after (issueLog d before priorLog af (after, .returned d.tid))
  returnedWorker : Worker
  live : after.workers[d.tid]? = some returnedWorker
  phase : returnedWorker.phase = .returned

def Response.history {d : Descriptor} {initial : S} {Post : Assertion}
    (response : Response d initial Post) : Log :=
  issueLog d response.before response.priorLog response.af (response.after, .returned d.tid)

theorem Response.origin {d : Descriptor} {initial : S} {Post : Assertion}
    (response : Response d initial Post) :
    Origin response.before (.issue d.tid response.af) (response.after, .returned d.tid)
      d.profile d.family :=
  step_origin response.issued.actual

theorem Response.trace {d : Descriptor} {initial : S} {Post : Assertion}
    (response : Response d initial Post) :
    OriginTrace d.profile initial response.history response.after d.family :=
  response.authentic.snoc response.origin

/-- Current returned frame and exact historical response prefix. Pending
entries and current RAM are not equated with the response state. -/
structure Done (d : Descriptor) (initial : S) (Post : Assertion)
    (response : Response d initial Post) (state : S) (history : Log) : Prop where
  admitted : Admission d initial
  frame : Frame d state
  authentic : OriginTrace d.profile initial history state d.family
  extension : ∃ suffix, history = response.history ++ suffix
  saved : ∃ worker, state.workers[d.tid]? = some worker ∧
    SavedFrame response.returnedWorker worker

/-- Every authenticated idle position remains in the current log. The stored
Post is used only at the response, never as an assertion of the later RAM. -/
theorem Done.idle {d : Descriptor} {initial before after : S} {Post : Assertion}
    {response : Response d initial Post} {history extended : Log}
    (done : Done d initial Post response before history)
    (idle : Idle d.profile d.tid (before, history) (after, extended) d.family) :
    Done d initial Post response after extended := by
  obtain ⟨prior, live, saved⟩ := done.saved
  obtain ⟨current, currentLive, retained⟩ := idle.saved live
  have frame := done.frame.idle idle
  have authentic := idle.authentic done.authentic
  obtain ⟨past, extensionEq⟩ := done.extension
  obtain ⟨suffix, _trace, _allowed, appended⟩ := idle
  refine ⟨done.admitted, frame, authentic, ⟨past ++ suffix, ?_⟩,
    ⟨current, currentLive, saved.trans retained⟩⟩
  change extended = history ++ suffix at appended
  rw [appended, extensionEq, List.append_assoc]

theorem Done.pause {d : Descriptor} {initial before after : S} {Post : Assertion}
    {response : Response d initial Post} {history extended : Log}
    (done : Done d initial Post response before history)
    (paused : Pause d.profile d.tid (before, history) (after, extended) d.family) :
    Done d initial Post response after extended :=
  done.idle paused.toIdle

inductive Control (d : Descriptor) (initial : S) (Post : Assertion) where
  | running (node : d.graph.Index) (fuel : Nat)
  | done (response : Response d initial Post)

/-- The current state and entire connected past are retained as data. -/
structure Ghost (d : Descriptor) (initial : S) (Post : Assertion) where
  current : S
  history : Log
  control : Control d initial Post

def Related {d : Descriptor} {initial : S} {Post : Assertion}
    (annotations : Annotations d Post) (state : S) (ghost : Ghost d initial Post) : Prop :=
  state = ghost.current ∧
    match ghost.control with
    | .running node fuel =>
      Residual d initial Post annotations.Inv fuel node ghost.current ghost.history
    | .done response => Done d initial Post response ghost.current ghost.history

def initialGhost (d : Descriptor) (initial : S) (Post : Assertion)
    (node : d.graph.Index) : Ghost d initial Post :=
  ⟨initial, [], .running node ((d.graph.node node).depth + 1)⟩

theorem Entry.related {d : Descriptor} {initial : S} {Post : Assertion}
    {annotations : Annotations d Post} {node : d.graph.Index}
    (entry : Entry annotations initial node) :
    Related annotations initial (initialGhost d initial Post node) := by
  refine ⟨rfl, ?_⟩
  exact Residual.start entry.admitted
    (annotations.blocks node initial [] d.original entry.cutpoint
      entry.admitted.frame entry.binding entry.invariant)

/-- Present generated obligations enable either AF choice without assuming
that this or any future schedule was selected or succeeds. -/
theorem Residual.enabled {d : Descriptor} {initial state : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index} {history : Log}
    (residual : Residual d initial Post Exit (fuel + 1) node state history) (af : Bool) :
    ∃ result, TSO64.step state (.issue d.tid af) d.profile d.family = .ok result :=
  rwp.enabled residual.generated af

theorem Entry.enabled {d : Descriptor} {initial : S} {Post : Assertion}
    {annotations : Annotations d Post} {node : d.graph.Index}
    (entry : Entry annotations initial node) (af : Bool) :
    ∃ result, TSO64.step initial (.issue d.tid af) d.profile d.family = .ok result :=
  rwp.enabled (annotations.blocks node initial [] d.original entry.cutpoint
    entry.admitted.frame entry.binding entry.invariant) af

theorem Related.frame {d : Descriptor} {initial state : S} {Post : Assertion}
    {annotations : Annotations d Post} {ghost : Ghost d initial Post}
    (related : Related annotations state ghost) : Frame d state := by
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨same, retained⟩ := related
  change state = current at same
  subst current
  cases control with
  | running node fuel => exact retained.frame
  | done response => exact retained.frame

theorem Related.authentic {d : Descriptor} {initial state : S} {Post : Assertion}
    {annotations : Annotations d Post} {ghost : Ghost d initial Post}
    (related : Related annotations state ghost) :
    OriginTrace d.profile initial ghost.history state d.family := by
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨same, retained⟩ := related
  change state = current at same
  subst current
  cases control with
  | running node fuel => exact retained.authentic
  | done response => exact retained.authentic

/-- Only an actual destination cutpoint restarts the bounded block. -/
def arrivalFuel (d : Descriptor) (destination : d.graph.Index) (remaining : Nat) : Nat :=
  if (d.graph.node destination).cutpoint then (d.graph.node destination).depth + 1 else remaining

/-- Eagerly regenerate a cutpoint's block before admitting interference. -/
theorem Annotations.arrival {d : Descriptor} {initial state : S} {Post : Assertion}
    (annotations : Annotations d Post) {destination : d.graph.Index} {fuel : Nat}
    {history : Log} {worker : Worker}
    (admitted : Admission d initial)
    (authentic : OriginTrace d.profile initial history state d.family)
    (frame : Frame d state) (binding : Binding d destination state worker)
    (following : if (d.graph.node destination).cutpoint then annotations.Inv destination state history
      else Residual d initial Post annotations.Inv fuel destination state history) :
    Residual d initial Post annotations.Inv (arrivalFuel d destination fuel)
      destination state history := by
  unfold arrivalFuel
  by_cases cut : (d.graph.node destination).cutpoint = true
  · rw [ite_eq_left cut] at following ⊢
    exact ⟨admitted, authentic,
      annotations.blocks destination state history worker cut frame binding following⟩
  · rw [ite_eq_right cut] at following ⊢
    exact following

/-- One constructor per exact scheduler position. Blocking retains positive
fuel/node; ordinary and locked retirements retain their actual checked evidence. -/
inductive Advance (d : Descriptor) (initial : S) (Post : Assertion) :
    Ghost d initial Post → Action → O → Ghost d initial Post → Prop where
  | passive {before after : S} {history : Log} {action : Action} {seen : O}
      {control : Control d initial Post}
      (quiet : EffectSimulation.passive d.tid action)
      (origin : Origin before action (after, seen) d.profile d.family) :
      Advance d initial Post ⟨before, history, control⟩ action seen
        ⟨after, history ++ [⟨before, action, (after, seen)⟩], control⟩
  | blocked {before : S} {history : Log} {af : Bool}
      {node : d.graph.Index} {fuel : Nat}
      (actual : TSO64.step before (.issue d.tid af) d.profile d.family =
        .ok (before, .blocked d.tid)) :
      Advance d initial Post ⟨before, history, .running node (fuel + 1)⟩
        (.issue d.tid af) (.blocked d.tid)
        ⟨before, issueLog d before history af (before, .blocked d.tid),
          .running node (fuel + 1)⟩
  | next {before after : S} {history : Log} {af : Bool}
      {node destination : d.graph.Index} {fuel : Nat}
      {observation : Sequential.Observation} {output : X86.State}
      (issued : OrdinaryIssued d node before af (after, .ordinary d.tid) observation)
      (outcome : observation.result = .next output)
      (edge : d.graph.Edge node destination)
      (pc : output.rip = d.base + BitVec.ofNat 64 (d.graph.node destination).offset) :
      Advance d initial Post ⟨before, history, .running node (fuel + 1)⟩
        (.issue d.tid af) (.ordinary d.tid)
        ⟨after, issueLog d before history af (after, .ordinary d.tid),
          .running destination (arrivalFuel d destination fuel)⟩
  | rmw {before after : S} {history : Log} {af : Bool}
      {node destination : d.graph.Index} {fuel : Nat}
      {output : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
      (issued : AtomicIssued d node before af (after, .rmw d.tid output.2) output machine)
      (edge : d.graph.Edge node destination)
      (pc : machine.state.rip = d.base + BitVec.ofNat 64 (d.graph.node destination).offset) :
      Advance d initial Post ⟨before, history, .running node (fuel + 1)⟩
        (.issue d.tid af) (.rmw d.tid output.2)
        ⟨after, issueLog d before history af (after, .rmw d.tid output.2),
          .running destination (arrivalFuel d destination fuel)⟩
  | returned (response : Response d initial Post) {fuel : Nat} :
      Advance d initial Post
        ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩
        (.issue d.tid response.af) (.returned d.tid)
        ⟨response.after, response.history, .done response⟩

/-- An actual issue cannot succeed at a retained returned worker. This uses
only the forward origin theorem for the single current checked step. -/
private theorem returned_no_issue {state : S} {tid : Nat} {worker : Worker}
    {af : Bool} {result : S × O} {profile : Profile} {family : RMWFamily}
    (live : state.workers[tid]? = some worker) (returned : worker.phase = .returned)
    (actual : TSO64.step state (.issue tid af) profile family = .ok result) : False := by
  cases step_origin actual with
  | ordinary found running _code _caller _fetched _effect =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)
  | blocked found running _code _caller _fetched _bounds _nonempty =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)
  | rmw found running _code _caller _fetched _bounds _empty _grant _effect =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)

theorem Done.no_issue {d : Descriptor} {initial state : S} {Post : Assertion}
    {response : Response d initial Post} {history : Log} {af : Bool} {result : S × O}
    (done : Done d initial Post response state history)
    (actual : TSO64.step state (.issue d.tid af) d.profile d.family = .ok result) : False := by
  obtain ⟨worker, live, saved⟩ := done.saved
  exact returned_no_issue live (saved.phase.trans response.phase) actual

/-- Specialize present generated obligations to exactly one current checked
issue. Blocking preserves fuel/node; both retirement kinds restart cuts eagerly. -/
theorem Annotations.own {d : Descriptor} {initial before after : S} {Post : Assertion}
    (annotations : Annotations d Post) {node : d.graph.Index} {fuel : Nat}
    {history : Log} {af : Bool} {seen : O}
    (residual : Residual d initial Post annotations.Inv (fuel + 1) node before history)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (after, seen)) :
    ∃ next, Advance d initial Post ⟨before, history, .running node (fuel + 1)⟩
      (.issue d.tid af) seen next ∧ Related annotations after next := by
  rcases residual.resume_of_step actual with ⟨same, retained⟩ |
    ⟨retirement, issued, frame, authentic, follows⟩
  · have stateEq : after = before := congrArg Prod.fst same
    have seenEq : seen = .blocked d.tid := congrArg Prod.snd same
    subst after
    subst seen
    exact ⟨⟨before, issueLog d before history af (before, .blocked d.tid),
      .running node (fuel + 1)⟩, .blocked actual, rfl, retained⟩
  · cases retirement with
    | ordinary observation =>
      cases issued with
      | ordinary issued =>
        cases outcome : observation.result with
        | atomic event output => simp only [Follow, outcome] at follows
        | syscall request => simp only [Follow, outcome] at follows
        | returned output =>
          obtain ⟨returnedWorker, returnedLive, coherence⟩ := issued.reifies
          rw [outcome] at coherence
          obtain ⟨label, returnedPhase, _cpu⟩ := coherence
          change seen = .returned d.tid at label
          subst seen
          let response : Response d initial Post :=
            { priorLog := history
              before := before
              af := af
              after := after
              node := node
              observation := observation
              output := output
              issued := issued
              returned := outcome
              authentic := residual.authentic
              post := follows.returned outcome
              returnedWorker := returnedWorker
              live := returnedLive
              phase := returnedPhase }
          refine ⟨⟨after, response.history, .done response⟩, .returned response, rfl, ?_⟩
          refine ⟨residual.admitted, frame, authentic, ?_, ?_⟩
          · exact ⟨[], (List.append_nil response.history).symm⟩
          · exact ⟨returnedWorker, returnedLive, SavedFrame.refl returnedWorker⟩
        | next output =>
          simp only [Follow, outcome] at follows
          obtain ⟨destination, edge, pc, following⟩ := follows
          obtain ⟨successor, binding⟩ := frame.next_binding issued.reifies outcome pc
          obtain ⟨_worker, _live, coherence⟩ := issued.reifies
          rw [outcome] at coherence
          obtain ⟨label, _running, _cpu⟩ := coherence
          change seen = .ordinary d.tid at label
          subst seen
          have nextResidual := annotations.arrival (worker := successor) residual.admitted authentic frame binding following
          exact ⟨⟨after, issueLog d before history af (after, .ordinary d.tid),
            .running destination (arrivalFuel d destination fuel)⟩,
            .next issued outcome edge pc, rfl, nextResidual⟩
    | rmw output machine =>
      cases issued with
      | rmw issued =>
        change jump d annotations.Inv (Residual d initial Post annotations.Inv fuel)
          node machine.state.rip after (issueLog d before history af (after, seen)) at follows
        obtain ⟨destination, edge, pc, following⟩ := follows
        obtain ⟨successor, binding⟩ := frame.atomic_next_binding issued pc
        have label : seen = .rmw d.tid output.2 := by
          obtain ⟨_worker, _instruction, _identifier, _handle, _cell, _binding,
            _selected, _empty, _decoded, _chosen, _changed, _executed, _effect, installed⟩ :=
            issued.witnesses
          exact congrArg Prod.snd installed
        subst seen
        have nextResidual := annotations.arrival (worker := successor) residual.admitted authentic frame binding following
        exact ⟨⟨after, issueLog d before history af (after, .rmw d.tid output.2),
          .running destination (arrivalFuel d destination fuel)⟩,
          .rmw issued edge pc, rfl, nextResidual⟩

/-- Actual CheckedSimulation: the local law accepts only the single current
checked step. Passive origins are derived from that step, never conversely. -/
theorem Annotations.simulation {d : Descriptor} {initial : S} {Post : Assertion}
    (annotations : Annotations d Post) :
    EffectSimulation.CheckedSimulation d.profile (Related (initial := initial) annotations)
      (Advance d initial Post) d.family := by
  classical
  constructor
  intro before after action seen ghost _valid related actual
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨same, retained⟩ := related
  change before = current at same
  subst current
  by_cases quiet : EffectSimulation.passive d.tid action
  · have origin := step_origin actual
    have idle : Idle d.profile d.tid (before, history)
        (after, history ++ [⟨before, action, (after, seen)⟩]) d.family :=
      Idle.step quiet origin
    refine ⟨⟨after, history ++ [⟨before, action, (after, seen)⟩], control⟩,
      .passive quiet origin, rfl, ?_⟩
    cases control with
    | running node fuel => exact retained.idle idle
    | done response => exact retained.idle idle
  · cases action with
    | drain peer => exact False.elim (quiet trivial)
    | issue peer af =>
      have own : peer = d.tid := by
        by_cases same : peer = d.tid
        · exact same
        · exact False.elim (quiet same)
      subst peer
      cases control with
      | done response => exact False.elim (retained.no_issue actual)
      | running node fuel =>
        cases fuel with
        | zero => exact False.elim retained.generated
        | succ fuel => exact annotations.own retained actual

/-- Complete ticks, including unchanged-state blocked positions, are appended. -/
theorem Advance.tick {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {action : Action} {seen : O}
    (advanced : Advance d initial Post before action seen after) :
    after.history = before.history ++ [⟨before.current, action, (after.current, seen)⟩] := by
  cases advanced <;> rfl

/-- The ghost transition's native origin is always derived forward from its
retirement/blocked evidence or retained as the actual passive origin. -/
theorem Advance.origin {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {action : Action} {seen : O}
    (advanced : Advance d initial Post before action seen after) :
    Origin before.current action (after.current, seen) d.profile d.family := by
  cases advanced with
  | passive _quiet origin => exact origin
  | blocked actual => exact step_origin actual
  | next issued _outcome _edge _pc => exact issued.origin
  | rmw issued _edge _pc => exact issued.origin
  | returned response => exact response.origin

theorem Advance.logs {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {action : Action} {seen : O}
    (advanced : Advance d initial Post before action seen after) :
    after.history.map Tick.action = before.history.map Tick.action ++ [action] ∧
      after.history.map (fun tick => tick.result.2) =
        before.history.map (fun tick => tick.result.2) ++ [seen] := by
  simp [advanced.tick]

theorem liftTrace_logs {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {actions : List Action} {observations : List O}
    (trace : LiftTrace (Advance d initial Post) before actions observations after) :
    after.history.map Tick.action = before.history.map Tick.action ++ actions ∧
      after.history.map (fun tick => tick.result.2) =
        before.history.map (fun tick => tick.result.2) ++ observations := by
  induction trace with
  | nil => exact ⟨(List.append_nil _).symm, (List.append_nil _).symm⟩
  | cons head _ ih =>
    obtain ⟨actionsEq, observationsEq⟩ := head.logs
    constructor
    · rw [ih.1, actionsEq]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    · rw [ih.2, observationsEq]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Successful finite schedules are folded only after independent Entry and
annotations exist. The full connected log keeps every action and observation. -/
theorem Annotations.schedule {d : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations d Post) {node : d.graph.Index}
    (entry : Entry annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions d.profile d.family = .ok (final, observations)) :
    ∃ next, Related annotations final next ∧
      LiftTrace (Advance d initial Post) (initialGhost d initial Post node) actions observations next ∧
      OriginTrace d.profile initial next.history final d.family ∧
      next.history.map Tick.action = actions ∧
      next.history.map (fun tick => tick.result.2) = observations := by
  obtain ⟨next, related, lifted⟩ :=
    annotations.simulation.schedule entry.admitted.wellFormed entry.related actual
  obtain ⟨actionsEq, observationsEq⟩ := liftTrace_logs lifted
  refine ⟨next, related, lifted, related.authentic, ?_, ?_⟩
  · simpa only [initialGhost, List.map_nil, List.nil_append] using actionsEq
  · simpa only [initialGhost, List.map_nil, List.nil_append] using observationsEq

/-- Cuts preserve the same-family exact prefix and suffix runs and current
residual/done relatedness at the original unfiltered scheduler position. -/
theorem Annotations.schedule_cut {d : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations d Post) {node : d.graph.Index}
    (entry : Entry annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions d.profile d.family = .ok (final, observations))
    (index : Nat) :
    ∃ before next,
      TSO64.schedule initial (actions.take index) d.profile d.family =
        .ok (before, observations.take index) ∧
      TSO64.schedule before (actions.drop index) d.profile d.family =
        .ok (final, observations.drop index) ∧
      Related annotations before next ∧
      LiftTrace (Advance d initial Post) (initialGhost d initial Post node)
        (actions.take index) (observations.take index) next :=
  annotations.simulation.schedule_cut entry.admitted.wellFormed entry.related actual index

/-- A native returned observation identifies only its actual issuing action.
This extraction is not an executable converse for arbitrary native origins. -/
private theorem return_action {before after : S} {action : Action} {tid : Nat}
    {profile : Profile} {family : RMWFamily}
    (origin : Origin before action (after, .returned tid) profile family) :
    ∃ af, action = .issue tid af := by
  cases origin with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _admitted _bounds _decoded _reads _queue _stepped finish =>
      cases finish
      exact ⟨_, rfl⟩

/-- An actual own return creates precisely this immutable response. -/
theorem Advance.returned_response {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {af : Bool}
    (advanced : Advance d initial Post before (.issue d.tid af) (.returned d.tid) after) :
    ∃ (response : Response d initial Post) (fuel : Nat),
      before = ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩ ∧
      after = ⟨response.after, response.history, .done response⟩ ∧ response.af = af := by
  cases advanced with
  | passive quiet _origin => exact False.elim (quiet rfl)
  | returned response => exact ⟨response, _, rfl, rfl, rfl⟩

/-- Certify an actual returned position from Entry/annotations. Its response
contains Post at that exact issue; its complete prior log projects to the
original prefix. Later interference is handled by Done.idle. -/
theorem Annotations.returned_at {d : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations d Post) {node : d.graph.Index}
    (entry : Entry annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions d.profile d.family = .ok (final, observations))
    {index : Nat} (seen : observations[index]? = some (.returned d.tid)) :
    ∃ (response : Response d initial Post) (fuel : Nat),
      TSO64.schedule initial (actions.take index) d.profile d.family =
        .ok (response.before, observations.take index) ∧
      actions[index]? = some (.issue d.tid response.af) ∧
      LiftTrace (Advance d initial Post) (initialGhost d initial Post node)
        (actions.take index) (observations.take index)
        ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩ ∧
      response.priorLog.map Tick.action = actions.take index ∧
      response.priorLog.map (fun tick => tick.result.2) = observations.take index ∧
      Done d initial Post response response.after response.history := by
  obtain ⟨before, ghost, prefixRun, _suffixRun, related, lifted⟩ :=
    annotations.schedule_cut entry actual index
  obtain ⟨other, action, after, otherPrefix, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at actual seen
  have same : (before, observations.take index) = (other, observations.take index) :=
    Except.ok.inj (prefixRun.symm.trans otherPrefix)
  have stateEq : before = other := congrArg Prod.fst same
  subst other
  obtain ⟨af, actionEq⟩ := return_action (step_origin stepped)
  subst action
  obtain ⟨next, advanced, nextRelated⟩ :=
    annotations.simulation.lift related.frame.wellFormed related stepped
  obtain ⟨response, fuel, sourceEq, destinationEq, choiceEq⟩ := advanced.returned_response
  have beforeEq : before = response.before :=
    related.1.trans (congrArg Ghost.current sourceEq)
  have afterEq : after = response.after :=
    nextRelated.1.trans (congrArg Ghost.current destinationEq)
  rw [sourceEq] at lifted
  obtain ⟨actionsEq, observationsEq⟩ := liftTrace_logs lifted
  refine ⟨response, fuel, ?_, ?_, lifted, ?_, ?_, ?_⟩
  · simpa only [beforeEq] using prefixRun
  · simpa only [← choiceEq] using actionAt
  · simpa only [initialGhost, List.map_nil, List.nil_append] using actionsEq
  · simpa only [initialGhost, List.map_nil, List.nil_append] using observationsEq
  · rw [afterEq, destinationEq] at nextRelated
    exact nextRelated.2

#print axioms Annotations
#print axioms Entry
#print axioms Response
#print axioms Response.history
#print axioms Response.origin
#print axioms Response.trace
#print axioms Done
#print axioms Done.idle
#print axioms Done.pause
#print axioms Control
#print axioms Ghost
#print axioms Related
#print axioms initialGhost
#print axioms Entry.related
#print axioms Residual.enabled
#print axioms Entry.enabled
#print axioms Related.frame
#print axioms Related.authentic
#print axioms arrivalFuel
#print axioms Annotations.arrival
#print axioms Advance
#print axioms returned_no_issue
#print axioms Done.no_issue
#print axioms Annotations.own
#print axioms Annotations.simulation
#print axioms Advance.tick
#print axioms Advance.origin
#print axioms Advance.logs
#print axioms liftTrace_logs
#print axioms Annotations.schedule
#print axioms Annotations.schedule_cut
#print axioms return_action
#print axioms Advance.returned_response
#print axioms Annotations.returned_at

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
