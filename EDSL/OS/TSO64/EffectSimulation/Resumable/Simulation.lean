/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Resumable.Block

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Sparse-cutpoint partial correctness over the generated bounded ordinary rwp.
Annotations select Inv independently. At a real successor cutpoint the adapter
expands its block immediately, before exposing the next state to interference.
An interior issue consumes one fuel; passive origins preserve node and fuel.

Ghosts store the actual current state and an unfiltered connected Origin log.
Own issues retain fresh Issued/Head evidence; peer blocked/RMW issues and all
drains use native passive origins. Ordinary origins alone have a checked step
converse here. The conservative native RMW origin is never given such a converse.

A response stores its immutable actual issue, input history, output and Post.
Done separately frames the current returned worker and retains the response as
an exact prefix of the connected current history. Publication may change RAM,
pending entries and reconstructed CPUs; historical Post is never transported.

Entry admits only an independently admitted running worker at an actual cut.
The existing Simulation.schedule and schedule_cut fold successful schedules,
retaining every action and observation. No scheduler, evaluator, future-success
entry condition, whole-program rank, exact accounting, fairness, progress,
native-RMW boundary, corpus credit or physical refinement is added. Initial
queues retain the original descriptor boundary and need not be empty.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Resumable
open X86

/-- Clients choose cutpoint assertions from inputs/resources/history. Block
obligations hold at the actual arrival, not at a selected future world. -/
structure Annotations (descriptor : Descriptor) (Post : Assertion) where
  Inv : CutAssertion descriptor
  blocks : ∀ (cut : descriptor.graph.Index) (state : S) (history : Log) (worker : Worker),
    descriptor.graph.cutpoint cut = true →
    Frame descriptor state → Binding descriptor cut state worker → Inv cut state history →
    rwp descriptor Post Inv (descriptor.graph.depth cut + 1) cut state history

/-- Entry has no done alternative, response witness or successful-future-run
premise. The initial FIFO/occurrence boundary is descriptor.original itself. -/
structure Entry {descriptor : Descriptor} {Post : Assertion}
    (annotations : Annotations descriptor Post) (initial : S)
    (node : descriptor.graph.Index) : Prop where
  admitted : Admission descriptor initial
  cutpoint : descriptor.graph.cutpoint node = true
  binding : Binding descriptor node initial descriptor.original
  invariant : annotations.Inv node initial []

/-- Immutable historical response, including its exact native step and fresh
Head. Prefix authenticity is relative to the separately admitted initial state.
The saved output worker is used only through SavedFrame after this instant. -/
structure Response (descriptor : Descriptor) (initial : S) (Post : Assertion) where
  priorLog : Log
  before : S
  af : Bool
  after : S
  node : descriptor.graph.Index
  worker : Worker
  observation : Sequential.Observation
  update : Queue.Cursor
  output : X86.State
  issued : Issued descriptor node before af worker observation update (after, .returned descriptor.tid)
  returned : observation.result = .returned output
  authentic : OriginTrace descriptor.profile initial priorLog before
  post : Post after (issueLog descriptor.tid before priorLog af (after, .returned descriptor.tid))
  returnedWorker : Worker
  live : after.workers[descriptor.tid]? = some returnedWorker
  phase : returnedWorker.phase = .returned

def Response.history {descriptor : Descriptor} {initial : S} {Post : Assertion}
    (response : Response descriptor initial Post) : Log :=
  issueLog descriptor.tid response.before response.priorLog response.af
    (response.after, .returned descriptor.tid)

/-- This is the specific ordinary response's actual executable origin. It is
not an executable interpretation of arbitrary native Origin evidence. -/
theorem Response.origin {descriptor : Descriptor} {initial : S} {Post : Assertion}
    (response : Response descriptor initial Post) :
    Origin response.before (.issue descriptor.tid response.af)
      (response.after, .returned descriptor.tid) descriptor.profile :=
  step_origin response.issued.actual

theorem Response.trace {descriptor : Descriptor} {initial : S} {Post : Assertion}
    (response : Response descriptor initial Post) :
    OriginTrace descriptor.profile initial response.history response.after :=
  response.authentic.snoc response.origin

/-- Current done invariant. The full history contains the exact stored response
prefix, while the current worker retains only saved context/phase/resources/
nextStore. Neither pending entries nor localCPU/RAM are equated. -/
structure Done (descriptor : Descriptor) (initial : S) (Post : Assertion)
    (response : Response descriptor initial Post) (state : S) (history : Log) : Prop where
  admitted : Admission descriptor initial
  frame : Frame descriptor state
  authentic : OriginTrace descriptor.profile initial history state
  extension : ∃ suffix, history = response.history ++ suffix
  saved : ∃ worker, state.workers[descriptor.tid]? = some worker ∧
    SavedFrame response.returnedWorker worker

theorem Done.pause {descriptor : Descriptor} {initial before after : S} {Post : Assertion}
    {response : Response descriptor initial Post} {history extended : Log}
    (done : Done descriptor initial Post response before history)
    (paused : Pause descriptor.profile descriptor.tid (before, history) (after, extended)) :
    Done descriptor initial Post response after extended := by
  obtain ⟨prior, live, saved⟩ := done.saved
  obtain ⟨current, currentLive, retained⟩ := paused.saved live
  have frame := done.frame.pause paused
  have authentic := paused.authentic done.authentic
  obtain ⟨past, extensionEq⟩ := done.extension
  obtain ⟨suffix, _trace, _quiet, appended⟩ := paused
  refine ⟨done.admitted, frame, authentic, ⟨past ++ suffix, ?_⟩,
    ⟨current, currentLive, saved.trans retained⟩⟩
  change extended = history ++ suffix at appended
  rw [appended, extensionEq, List.append_assoc]

inductive Control (descriptor : Descriptor) (initial : S) (Post : Assertion) where
  | running (node : descriptor.graph.Index) (fuel : Nat)
  | done (response : Response descriptor initial Post)

/-- The actual current state is data, not an unconstrained successor witness;
Related equates it to the native scheduler state. -/
structure Ghost (descriptor : Descriptor) (initial : S) (Post : Assertion) where
  current : S
  history : Log
  control : Control descriptor initial Post

def Related {descriptor : Descriptor} {initial : S} {Post : Assertion}
    (annotations : Annotations descriptor Post) (state : S)
    (ghost : Ghost descriptor initial Post) : Prop :=
  state = ghost.current ∧
    match ghost.control with
    | .running node fuel =>
        Residual descriptor initial Post annotations.Inv fuel node ghost.current ghost.history
    | .done response => Done descriptor initial Post response ghost.current ghost.history

def initialGhost (descriptor : Descriptor) (initial : S) (Post : Assertion)
    (node : descriptor.graph.Index) : Ghost descriptor initial Post :=
  ⟨initial, [], .running node (descriptor.graph.depth node + 1)⟩

theorem Entry.related {descriptor : Descriptor} {initial : S} {Post : Assertion}
    {annotations : Annotations descriptor Post} {node : descriptor.graph.Index}
    (entry : Entry annotations initial node) :
    Related annotations initial (initialGhost descriptor initial Post node) := by
  refine ⟨rfl, ?_⟩
  exact Residual.start entry.admitted
    (annotations.blocks node initial [] descriptor.original entry.cutpoint
      entry.admitted.frame entry.binding entry.invariant)

theorem Related.frame {descriptor : Descriptor} {initial state : S} {Post : Assertion}
    {annotations : Annotations descriptor Post} {ghost : Ghost descriptor initial Post}
    (related : Related annotations state ghost) : Frame descriptor state := by
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨same, retained⟩ := related
  change state = current at same
  subst current
  cases control with
  | running node fuel => exact retained.frame
  | done response => exact retained.frame

theorem Related.authentic {descriptor : Descriptor} {initial state : S} {Post : Assertion}
    {annotations : Annotations descriptor Post} {ghost : Ghost descriptor initial Post}
    (related : Related annotations state ghost) :
    OriginTrace descriptor.profile initial ghost.history state := by
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨same, retained⟩ := related
  change state = current at same
  subst current
  cases control with
  | running node fuel => exact retained.authentic
  | done response => exact retained.authentic

/-- Only a declared cutpoint resets the segment's bounded residual. -/
def arrivalFuel (descriptor : Descriptor) (destination : descriptor.graph.Index) (remaining : Nat) :
    Nat :=
  if descriptor.graph.cutpoint destination then descriptor.graph.depth destination + 1 else remaining

/-- Every constructor appends the precise actual tick. Passive actions retain
all control data; continuing own issues consume one fuel and eagerly select the
arrival fuel. A return carries its actual Issued evidence through Response. -/
inductive Advance (descriptor : Descriptor) (initial : S) (Post : Assertion) :
    Ghost descriptor initial Post → Action → O → Ghost descriptor initial Post → Prop where
  | passive {before after : S} {history : Log} {action : Action} {seen : O}
      {control : Control descriptor initial Post}
      (quiet : EffectSimulation.passive descriptor.tid action)
      (origin : Origin before action (after, seen) descriptor.profile) :
      Advance descriptor initial Post ⟨before, history, control⟩ action seen
        ⟨after, history ++ [⟨before, action, (after, seen)⟩], control⟩
  | next {before after : S} {history : Log} {af : Bool}
      {node destination : descriptor.graph.Index} {fuel : Nat}
      {worker : Worker} {observation : Sequential.Observation} {update : Queue.Cursor}
      {output : X86.State}
      (issued : Issued descriptor node before af worker observation update
        (after, .ordinary descriptor.tid))
      (outcome : observation.result = .next output)
      (edge : descriptor.graph.Edge node destination)
      (pc : output.rip = descriptor.base + BitVec.ofNat 64 (descriptor.graph.node destination).offset) :
      Advance descriptor initial Post ⟨before, history, .running node (fuel + 1)⟩
        (.issue descriptor.tid af) (.ordinary descriptor.tid)
        ⟨after, issueLog descriptor.tid before history af (after, .ordinary descriptor.tid),
          .running destination (arrivalFuel descriptor destination fuel)⟩
  | returned (response : Response descriptor initial Post) {fuel : Nat} :
      Advance descriptor initial Post
        ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩
        (.issue descriptor.tid response.af) (.returned descriptor.tid)
        ⟨response.after, response.history, .done response⟩

/-- Narrow ordinary-origin converse. It uses the original Bool Sequential.step
and checked queue/finish relations directly; no RMW converse is asserted. -/
private theorem ordinary_step_of_fields {state : S} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : S × O} {profile : Profile}
    (live : state.workers[tid]? = some worker) (running : worker.phase ≠ .returned)
    (code : LeaseCurrent state.world worker.resources.actor worker.resources.code)
    (caller : LeaseCurrent state.world worker.resources.actor worker.resources.caller)
    (fetched : decode (fetchCPU state worker) = .ok (.ordinary instruction))
    (effect : OrdinaryEffect state tid worker instruction af result profile) :
    step state (.issue tid af) profile = .ok result := by
  cases effect with
  | intro admitted bounds decoded reads queue stepped finish =>
    rw [Sequential.step_eq_execute af decoded] at stepped
    obtain ⟨units, checked⟩ := reads
    change issue state tid af profile = .ok result
    simp [issue, live, running, code, caller, fetched, ordinary, admitted, bounds, decoded,
      checked, X86.VCGen.ManagedRules.queue_checked queue, stepped, Except.mapError,
      X86.VCGen.ManagedRules.finish_checked finish]

/-- Native locked origins at this live slot contradict the actual ordinary
dispatch. In particular, structural sequential decoding alone is not used as
an authorization to reinterpret a native RMW. -/
private theorem ready_origin_step {state : S} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : S × O} {profile : Profile}
    (ready : OrdinaryReady state tid worker instruction profile)
    (origin : Origin state (.issue tid af) result profile) :
    step state (.issue tid af) profile = .ok result := by
  cases origin with
  | ordinary live running code caller fetched effect =>
    exact ordinary_step_of_fields live running code caller fetched effect
  | blocked live _running _code _caller fetched _bounds _nonempty =>
    have same := Option.some.inj (ready.live.symm.trans live)
    cases same
    rw [ready.dispatch] at fetched
    cases fetched
  | rmw live _running _code _caller fetched _bounds _empty _grant _effect =>
    have same := Option.some.inj (ready.live.symm.trans live)
    cases same
    rw [ready.dispatch] at fetched
    cases fetched

private theorem returned_no_issue {state : S} {tid : Nat} {worker : Worker}
    {af : Bool} {result : S × O} {profile : Profile}
    (live : state.workers[tid]? = some worker) (returned : worker.phase = .returned)
    (origin : Origin state (.issue tid af) result profile) : False := by
  cases origin with
  | ordinary found running _code _caller _fetched _effect =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)
  | blocked found running _code _caller _fetched _bounds _nonempty =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)
  | rmw found running _code _caller _fetched _bounds _empty _grant _effect =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)

theorem Done.no_issue {descriptor : Descriptor} {initial state : S} {Post : Assertion}
    {response : Response descriptor initial Post} {history : Log} {af : Bool} {result : S × O}
    (done : Done descriptor initial Post response state history)
    (origin : Origin state (.issue descriptor.tid af) result descriptor.profile) : False := by
  obtain ⟨worker, live, saved⟩ := done.saved
  exact returned_no_issue live (saved.phase.trans response.phase) origin

/-- Consume exactly one own ordinary issue. A cutpoint is expanded here at
the exact authenticated arrival; a bare Inv is never stored while paused. -/
theorem Annotations.own {descriptor : Descriptor} {initial before after : S} {Post : Assertion}
    (annotations : Annotations descriptor Post) {node : descriptor.graph.Index} {fuel : Nat}
    {history : Log} {af : Bool} {seen : O}
    (residual : Residual descriptor initial Post annotations.Inv (fuel + 1) node before history)
    (origin : Origin before (.issue descriptor.tid af) (after, seen) descriptor.profile) :
    ∃ next,
      Advance descriptor initial Post ⟨before, history, .running node (fuel + 1)⟩
        (.issue descriptor.tid af) seen next ∧ Related annotations after next := by
  obtain ⟨worker, observation, update, result, issued, frame, authentic, follows⟩ :=
    residual.resume af
  have checked := ready_origin_step issued.ready origin
  have same : result = (after, seen) := Except.ok.inj (issued.actual.symm.trans checked)
  subst result
  cases outcome : observation.result with
  | atomic event output =>
    simp only [Follow, outcome] at follows
  | syscall request =>
    simp only [Follow, outcome] at follows
  | returned output =>
    obtain ⟨returnedWorker, returnedLive, coherence⟩ := issued.reifies
    rw [outcome] at coherence
    obtain ⟨label, returnedPhase, _cpu⟩ := coherence
    change seen = .returned descriptor.tid at label
    subst seen
    let response : Response descriptor initial Post :=
      { priorLog := history
        before := before
        af := af
        after := after
        node := node
        worker := worker
        observation := observation
        update := update
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
    obtain ⟨_retiredWorker, _retiredLive, coherence⟩ := issued.reifies
    rw [outcome] at coherence
    obtain ⟨label, _running, _cpu⟩ := coherence
    change seen = .ordinary descriptor.tid at label
    subst seen
    have nextResidual : Residual descriptor initial Post annotations.Inv
        (arrivalFuel descriptor destination fuel) destination after
        (issueLog descriptor.tid before history af (after, .ordinary descriptor.tid)) := by
      by_cases cut : descriptor.graph.cutpoint destination = true
      · simp only [arrivalFuel, cut, ↓reduceIte]
        refine ⟨residual.admitted, authentic, ?_⟩
        apply annotations.blocks destination after
          (issueLog descriptor.tid before history af (after, .ordinary descriptor.tid))
          successor cut frame binding
        simpa only [cut, ↓reduceIte] using following
      · simpa [arrivalFuel, cut] using following
    refine ⟨⟨after,
      issueLog descriptor.tid before history af (after, .ordinary descriptor.tid),
      .running destination (arrivalFuel descriptor destination fuel)⟩,
      .next issued outcome edge pc, rfl, nextResidual⟩

/-- Concrete law for the existing origin-indexed Simulation. Native passive
origins append their exact tick and preserve control. Own issues are regenerated
from the current residual; own issue after a retained return is impossible. -/
theorem Annotations.simulation {descriptor : Descriptor} {initial : S} {Post : Assertion}
    (annotations : Annotations descriptor Post) :
    EffectSimulation.Simulation descriptor.profile (Related (initial := initial) annotations)
      (Advance descriptor initial Post) := by
  classical
  constructor
  intro before after action seen ghost _valid related origin
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨same, retained⟩ := related
  change before = current at same
  subst current
  by_cases quiet : EffectSimulation.passive descriptor.tid action
  · have paused : Pause descriptor.profile descriptor.tid (before, history)
        (after, history ++ [⟨before, action, (after, seen)⟩]) :=
      Pause.step quiet origin
    refine ⟨⟨after, history ++ [⟨before, action, (after, seen)⟩], control⟩,
      .passive quiet origin, rfl, ?_⟩
    cases control with
    | running node fuel => exact retained.pause paused
    | done response => exact retained.pause paused
  · cases action with
    | drain peer => exact False.elim (quiet trivial)
    | issue peer af =>
      have own : peer = descriptor.tid := by
        by_cases same : peer = descriptor.tid
        · exact same
        · exact False.elim (quiet same)
      subst peer
      cases control with
      | done response => exact False.elim (retained.no_issue origin)
      | running node fuel =>
        cases fuel with
        | zero => exact False.elim retained.generated
        | succ fuel => exact annotations.own retained origin

/-- Ghost labels retain all native scheduler positions. This projection lemma
is about the existing LiftTrace, not a second scheduler fold or interpreter. -/
theorem Advance.logs {descriptor : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost descriptor initial Post} {action : Action} {seen : O}
    (advanced : Advance descriptor initial Post before action seen after) :
    after.history.map Tick.action = before.history.map Tick.action ++ [action] ∧
      after.history.map (fun tick => tick.result.2) =
        before.history.map (fun tick => tick.result.2) ++ [seen] := by
  cases advanced <;> simp [Response.history, issueLog]

theorem liftTrace_logs {descriptor : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost descriptor initial Post}
    {actions : List Action} {observations : List O}
    (trace : LiftTrace (Advance descriptor initial Post) before actions observations after) :
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

/-- Successful finite schedules use the existing Simulation fold. The result
has a connected native OriginTrace and exact projections to the full original
action/observation lists, including peer returns, blocks and publications. -/
theorem Annotations.schedule {descriptor : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations descriptor Post) {node : descriptor.graph.Index}
    (entry : Entry annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions descriptor.profile = .ok (final, observations)) :
    ∃ next,
      Related annotations final next ∧
      LiftTrace (Advance descriptor initial Post)
        (initialGhost descriptor initial Post node) actions observations next ∧
      OriginTrace descriptor.profile initial next.history final ∧
      next.history.map Tick.action = actions ∧
      next.history.map (fun tick => tick.result.2) = observations := by
  obtain ⟨next, related, lifted⟩ :=
    annotations.simulation.schedule entry.admitted.wellFormed entry.related actual
  obtain ⟨actionsEq, observationsEq⟩ := liftTrace_logs lifted
  refine ⟨next, related, lifted, related.authentic, ?_, ?_⟩
  · simpa only [initialGhost, List.map_nil, List.nil_append] using actionsEq
  · simpa only [initialGhost, List.map_nil, List.nil_append] using observationsEq

/-- Existing successful-schedule cuts retain exact prefix and suffix runs and
a generated residual or immutable response at the actual intermediate state. -/
theorem Annotations.schedule_cut {descriptor : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations descriptor Post) {node : descriptor.graph.Index}
    (entry : Entry annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions descriptor.profile = .ok (final, observations))
    (index : Nat) :
    ∃ before next,
      TSO64.schedule initial (actions.take index) descriptor.profile =
        .ok (before, observations.take index) ∧
      TSO64.schedule before (actions.drop index) descriptor.profile =
        .ok (final, observations.drop index) ∧
      Related annotations before next ∧
      LiftTrace (Advance descriptor initial Post) (initialGhost descriptor initial Post node)
        (actions.take index) (observations.take index) next :=
  annotations.simulation.schedule_cut entry.admitted.wellFormed entry.related actual index

/-- A native returned observation is necessarily an issue by that worker.
This extracts its action only; it does not assert an Origin-to-step converse. -/
private theorem return_action {before after : S} {action : Action} {tid : Nat} {profile : Profile}
    (origin : Origin before action (after, .returned tid) profile) :
    ∃ af, action = .issue tid af := by
  cases origin with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _admitted _bounds _decoded _reads _queue _stepped finish =>
      cases finish
      exact ⟨_, rfl⟩

/-- An actual own return transition creates this exact response from running
control. Passive transitions cannot stand in for own return. -/
theorem Advance.returned_response {descriptor : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost descriptor initial Post} {af : Bool}
    (advanced : Advance descriptor initial Post before (.issue descriptor.tid af)
      (.returned descriptor.tid) after) :
    ∃ (response : Response descriptor initial Post) (fuel : Nat),
      before = ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩ ∧
      after = ⟨response.after, response.history, .done response⟩ ∧ response.af = af := by
  cases advanced with
  | passive quiet _origin => exact False.elim (quiet rfl)
  | returned response => exact ⟨response, _, rfl, rfl, rfl⟩

/-- Certify every actual returned position from independent Entry and blocks,
without assuming Done. The response contains Post at its exact issue tick; the
LiftTrace identifies its entire prefix at original scheduler positions. Current
done relatedness is established at the response, and Done.pause permits later
publication without transporting historical Post to the later world. -/
theorem Annotations.returned_at {descriptor : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations descriptor Post) {node : descriptor.graph.Index}
    (entry : Entry annotations initial node) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions descriptor.profile = .ok (final, observations))
    {index : Nat} (seen : observations[index]? = some (.returned descriptor.tid)) :
    ∃ (response : Response descriptor initial Post) (fuel : Nat),
      TSO64.schedule initial (actions.take index) descriptor.profile =
        .ok (response.before, observations.take index) ∧
      actions[index]? = some (.issue descriptor.tid response.af) ∧
      LiftTrace (Advance descriptor initial Post) (initialGhost descriptor initial Post node)
        (actions.take index) (observations.take index)
        ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩ ∧
      Related annotations response.after ⟨response.after, response.history, .done response⟩ := by
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
    annotations.simulation.lift related.frame.wellFormed related (step_origin stepped)
  obtain ⟨response, fuel, sourceEq, destinationEq, choiceEq⟩ := advanced.returned_response
  have beforeEq : before = response.before :=
    related.1.trans (congrArg Ghost.current sourceEq)
  have afterEq : after = response.after :=
    nextRelated.1.trans (congrArg Ghost.current destinationEq)
  refine ⟨response, fuel, ?_, ?_, ?_, ?_⟩
  · simpa only [beforeEq] using prefixRun
  · simpa only [← choiceEq] using actionAt
  · rw [sourceEq] at lifted
    exact lifted
  · rw [afterEq, destinationEq] at nextRelated
    exact nextRelated

#print axioms Annotations
#print axioms Entry
#print axioms Response.origin
#print axioms Response.trace
#print axioms Done.pause
#print axioms Related
#print axioms Entry.related
#print axioms Related.frame
#print axioms Related.authentic
#print axioms Advance
#print axioms Done.no_issue
#print axioms Annotations.own
#print axioms Annotations.simulation
#print axioms Advance.logs
#print axioms liftTrace_logs
#print axioms Annotations.schedule
#print axioms Annotations.schedule_cut
#print axioms Advance.returned_response
#print axioms Annotations.returned_at

end EDSL.OS.TSO64.EffectSimulation.Resumable

#audit_edsl
