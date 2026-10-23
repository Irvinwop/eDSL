/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Head
import EDSL.OS.TSO64.EffectSimulation.Mixed.Idle

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Bounded generated mixed blocks at actual TSO64 instruction boundaries.
Every positive residual is closed under authenticated idle extensions, including
peer issues, all drains and exact own blocked attempts. These positions remain
in the log without consuming fuel or changing the residual node. Obligations
are regenerated from the current state and policy; the current locked selector,
RAM and resources are supplied by `Mixed.Head`, not a future execution premise.

An actual retirement consumes one fuel at an interior successor or exposes
`Exit` at the destination node's declared cutpoint. Ordinary next and locked
next use their exact output RIP; ordinary return checks `Post` at this issue's
installed state and appended tick. A bare exit need not be idle closed: a later
adapter must restart its block before interference. Zero fuel fails closed.

`Residual` keeps independent initial admission, an authenticated connected past
and the generated obligations as separate fields. Resumption derives the
successor frame and extends that actual past; it never converts an arbitrary
native origin into a checked step. Shared RAM and pending queues are not frozen.
Theorems inherit the native target, resource, lifetime and memory-model contracts
of the imported head and idle modules; no fairness or termination is asserted.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Frame transport uses the actual authenticated origin suffix of an idle
extension. The admissibility labels alone do not supply a protected frame. -/
theorem Frame.idle {d : Descriptor} {before after : S} {history extended : Log}
    (frame : Frame d before)
    (idle : Idle d.profile d.tid (before, history) (after, extended) d.family) :
    Frame d after := by
  obtain ⟨_suffix, trace, _allowed, _appended⟩ := idle
  exact Frame.along trace frame

/-- Retain every scheduler position, including an own issue that only blocks. -/
def issueLog (d : Descriptor) (before : S) (history : Log) (af : Bool)
    (result : S × O) : Log :=
  history ++ [⟨before, .issue d.tid af, result⟩]

/-- Successor selection follows an authenticated edge and exact output RIP.
The marker is the mixed node's own `cutpoint` field. -/
def jump (d : Descriptor) (Exit Tail : CutAssertion d) (node : d.graph.Index)
    (rip : Word) (state : S) (history : Log) : Prop :=
  ∃ destination : d.graph.Index, d.graph.Edge node destination ∧
    rip = d.base + BitVec.ofNat 64 (d.graph.node destination).offset ∧
    if (d.graph.node destination).cutpoint then Exit destination state history
    else Tail destination state history

theorem jump.mono {d : Descriptor} {Exit Tail Next : CutAssertion d}
    {node : d.graph.Index} {rip : Word} {state : S} {history : Log}
    (implies : ∀ destination, Tail destination state history → Next destination state history)
    (follows : jump d Exit Tail node rip state history) :
    jump d Exit Next node rip state history := by
  obtain ⟨destination, edge, pc, after⟩ := follows
  refine ⟨destination, edge, pc, ?_⟩
  by_cases isCut : (d.graph.node destination).cutpoint = true
  · simpa [isCut] using after
  · simp only [isCut] at after ⊢
    exact implies destination after

/-- Continuation for the exact native issue and its complete retirement tag.
Atomic and syscall sequential outcomes cannot discharge ordinary obligations. -/
def Follow (d : Descriptor) (Post : Assertion) (Exit Tail : CutAssertion d)
    (node : d.graph.Index) (before : S) (history : Log) (af : Bool)
    (result : S × O) (retirement : Retirement) : Prop :=
  let extended := issueLog d before history af result
  match retirement with
  | .ordinary observation => match observation.result with
    | .returned _ => Post result.1 extended
    | .next output => jump d Exit Tail node output.rip result.1 extended
    | .atomic _ _ | .syscall _ => False
  | .rmw _ machine => jump d Exit Tail node machine.state.rip result.1 extended

theorem Follow.mono {d : Descriptor} {Post : Assertion}
    {Exit Tail Next : CutAssertion d} {node : d.graph.Index}
    {before : S} {history : Log} {af : Bool} {result : S × O}
    {retirement : Retirement}
    (implies : ∀ destination,
      Tail destination result.1 (issueLog d before history af result) →
      Next destination result.1 (issueLog d before history af result))
    (follows : Follow d Post Exit Tail node before history af result retirement) :
    Follow d Post Exit Next node before history af result retirement := by
  cases retirement with
  | ordinary observation =>
    cases outcome : observation.result with
    | returned output => simpa only [Follow, outcome] using follows
    | atomic event output => simp only [Follow, outcome] at follows
    | syscall request => simp only [Follow, outcome] at follows
    | next output =>
      simp only [Follow, outcome] at follows ⊢
      exact jump.mono implies follows
  | rmw output machine =>
    change jump d Exit Tail node machine.state.rip result.1
      (issueLog d before history af result) at follows
    change jump d Exit Next node machine.state.rip result.1
      (issueLog d before history af result)
    exact jump.mono implies follows

/-- The return assertion belongs to this precise installed state and log,
without any claim that it survives a later publication or peer issue. -/
theorem Follow.returned {d : Descriptor} {Post : Assertion}
    {Exit Tail : CutAssertion d} {node : d.graph.Index}
    {before : S} {history : Log} {af : Bool} {result : S × O}
    {observation : Sequential.Observation} {output : X86.State}
    (follows : Follow d Post Exit Tail node before history af result (.ordinary observation))
    (returned : observation.result = .returned output) :
    Post result.1 (issueLog d before history af result) := by
  simpa only [Follow, returned] using follows

/-- Universal idle closure is regenerated at every positive boundary. A held
locked instruction requires no atomic grant, primitive result or fuel decrease. -/
def rwp (d : Descriptor) (Post : Assertion) (Exit : CutAssertion d) :
    Nat → d.graph.Index → S → Log → Prop
  | 0, _, _, _ => False
  | fuel + 1, node, state, history =>
    IdleBox d.profile d.tid (fun current past => Frame d current ∧
      One d node current (Follow d Post Exit (rwp d Post Exit fuel) node current past))
      state history d.family

theorem rwp.here {d : Descriptor} {Post : Assertion} {Exit : CutAssertion d}
    {fuel : Nat} {node : d.graph.Index} {state : S} {history : Log}
    (vc : rwp d Post Exit (fuel + 1) node state history) :
    Frame d state ∧ One d node state
      (Follow d Post Exit (rwp d Post Exit fuel) node state history) :=
  IdleBox.here vc

/-- All authenticated idle positions preserve both node and fuel. -/
theorem rwp.idle {d : Descriptor} {Post : Assertion} {Exit : CutAssertion d}
    {fuel : Nat} {node : d.graph.Index} {before after : S} {history extended : Log}
    (vc : rwp d Post Exit fuel node before history)
    (idle : Idle d.profile d.tid (before, history) (after, extended) d.family) :
    rwp d Post Exit fuel node after extended := by
  cases fuel with
  | zero => exact False.elim vc
  | succ fuel => exact IdleBox.stable vc idle

theorem rwp.pause {d : Descriptor} {Post : Assertion} {Exit : CutAssertion d}
    {fuel : Nat} {node : d.graph.Index} {before after : S} {history extended : Log}
    (vc : rwp d Post Exit fuel node before history)
    (paused : Pause d.profile d.tid (before, history) (after, extended) d.family) :
    rwp d Post Exit fuel node after extended :=
  rwp.idle vc paused.toIdle

/-- Present generated obligations enable either AF valuation independently of
any future schedule, including the native whole-state blocked case. -/
theorem rwp.enabled {d : Descriptor} {Post : Assertion} {Exit : CutAssertion d}
    {fuel : Nat} {node : d.graph.Index} {before : S} {history : Log}
    (vc : rwp d Post Exit (fuel + 1) node before history) (af : Bool) :
    ∃ result, TSO64.step before (.issue d.tid af) d.profile d.family = .ok result := by
  obtain ⟨frame, one⟩ := rwp.here vc
  exact One.enabled frame one af

/-- A blocked attempt appends its exact tick at unchanged state/node/positive
fuel. A retirement derives the successor frame and its fuel-minus-one
continuation from the real head evidence. No arbitrary log is authenticated. -/
theorem rwp.resume {d : Descriptor} {Post : Assertion} {Exit : CutAssertion d}
    {fuel : Nat} {node : d.graph.Index} {before : S} {history : Log}
    (vc : rwp d Post Exit (fuel + 1) node before history) (af : Bool) :
    (TSO64.step before (.issue d.tid af) d.profile d.family = .ok (before, .blocked d.tid) ∧
      rwp d Post Exit (fuel + 1) node before
        (issueLog d before history af (before, .blocked d.tid))) ∨
    ∃ result retirement, RetiredEvidence d node before af result retirement ∧
      Frame d result.1 ∧
      Follow d Post Exit (rwp d Post Exit fuel) node before history af result retirement := by
  obtain ⟨frame, one⟩ := rwp.here vc
  rcases One.resume frame one af with blocked | ⟨result, retirement, issued, follows⟩
  · have idle : Idle d.profile d.tid (before, history)
        (before, issueLog d before history af (before, .blocked d.tid)) d.family :=
      Idle.blocked_step blocked
    exact .inl ⟨blocked, rwp.idle vc idle⟩
  · exact .inr ⟨result, retirement, issued, issued.frame frame, follows⟩

/-- Complete ordinary reification binds the installed successor at its actual
RIP, retaining the current frame's original resource identities. -/
theorem Frame.next_binding {d : Descriptor} {destination : d.graph.Index}
    {result : S × O} {observation : Sequential.Observation} {output : X86.State}
    (frame : Frame d result.1) (reified : Reifies d.tid result observation)
    (next : observation.result = .next output)
    (pc : output.rip = d.base + BitVec.ofNat 64 (d.graph.node destination).offset) :
    ∃ worker, Binding d destination result.1 worker := by
  obtain ⟨worker, live, coherence⟩ := reified
  rw [next] at coherence
  obtain ⟨_label, running, cpu⟩ := coherence
  obtain ⟨original, originalLive, resources⟩ := frame.worker
  have same : worker = original := Option.some.inj (live.symm.trans originalLive)
  refine ⟨worker, live, ?_, running, ?_⟩
  · exact (congrArg Worker.resources same).trans resources
  · exact (congrArg X86.State.rip cpu).trans pc

/-- Locked successor binding comes from the actual installed machine context.
Its current live worker and resources are identified in the derived frame;
no shared-memory or whole-worker equality with the prestate is assumed. -/
theorem Frame.atomic_next_binding {d : Descriptor} {node destination : d.graph.Index}
    {before : S} {af : Bool} {result : S × O}
    {output : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    (frame : Frame d result.1) (issued : AtomicIssued d node before af result output machine)
    (pc : machine.state.rip = d.base + BitVec.ofNat 64 (d.graph.node destination).offset) :
    ∃ worker, Binding d destination result.1 worker := by
  obtain ⟨prior, _instruction, _identifier, _handle, _cell, binding, _selected,
    _empty, _decoded, _chosen, _changed, _executed, _effect, installed⟩ := issued.witnesses
  have live : result.1.workers[d.tid]? =
      some { prior with context := .ofCPU machine.state } := by
    rw [installed]
    exact List.getElem?_set_self (List.getElem_of_getElem? binding.live).1
  obtain ⟨current, currentLive, resources⟩ := frame.worker
  have same : current = { prior with context := .ofCPU machine.state } :=
    Option.some.inj (currentLive.symm.trans live)
  refine ⟨current, currentLive, resources, ?_, ?_⟩
  · rw [same]
    exact binding.running
  · rw [same]
    exact pc

/-- Independent admission, a connected authentic history and generated
obligations. The current residual asserts no requested future result. -/
structure Residual (d : Descriptor) (initial : S) (Post : Assertion) (Exit : CutAssertion d)
    (fuel : Nat) (node : d.graph.Index) (state : S) (history : Log) : Prop where
  admitted : Admission d initial
  authentic : OriginTrace d.profile initial history state d.family
  generated : rwp d Post Exit fuel node state history

theorem Residual.start {d : Descriptor} {initial : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index}
    (admitted : Admission d initial) (generated : rwp d Post Exit fuel node initial []) :
    Residual d initial Post Exit fuel node initial [] :=
  ⟨admitted, .nil, generated⟩

theorem Residual.frame {d : Descriptor} {initial state : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index} {history : Log}
    (residual : Residual d initial Post Exit fuel node state history) : Frame d state :=
  Frame.along residual.authentic residual.admitted.frame

theorem Residual.idle {d : Descriptor} {initial before after : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index} {history extended : Log}
    (residual : Residual d initial Post Exit fuel node before history)
    (idle : Idle d.profile d.tid (before, history) (after, extended) d.family) :
    Residual d initial Post Exit fuel node after extended :=
  ⟨residual.admitted, idle.authentic residual.authentic, rwp.idle residual.generated idle⟩

theorem Residual.pause {d : Descriptor} {initial before after : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index} {history extended : Log}
    (residual : Residual d initial Post Exit fuel node before history)
    (paused : Pause d.profile d.tid (before, history) (after, extended) d.family) :
    Residual d initial Post Exit fuel node after extended :=
  residual.idle paused.toIdle

/-- Prop-valued resumption retains concrete result/tag witnesses without
eliminating a generated proposition into data. Blocking preserves positive
fuel/node and the whole state; retirement consumes one unit only in Tail.
A cut exposes Exit for a later eager restart at that exact state and log. -/
inductive Resumed (d : Descriptor) (initial : S) (Post : Assertion) (Exit : CutAssertion d)
    (fuel : Nat) (node : d.graph.Index) (before : S) (history : Log) (af : Bool) : Prop where
  | blocked
      (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (before, .blocked d.tid))
      (retained : Residual d initial Post Exit (fuel + 1) node before
        (issueLog d before history af (before, .blocked d.tid))) :
      Resumed d initial Post Exit fuel node before history af
  | retired (result : S × O) (retirement : Retirement)
      (issued : RetiredEvidence d node before af result retirement)
      (frame : Frame d result.1)
      (authentic : OriginTrace d.profile initial
        (issueLog d before history af result) result.1 d.family)
      (follows : Follow d Post Exit (Residual d initial Post Exit fuel)
        node before history af result retirement) :
      Resumed d initial Post Exit fuel node before history af

/-- Enabled one-issue resumption authenticates the exact new tick in either
branch. Interior retirement tails retain independent admission and the whole
actual prefix, while the destination marker decides whether to expose Exit. -/
theorem Residual.resume {d : Descriptor} {initial before : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index} {history : Log}
    (residual : Residual d initial Post Exit (fuel + 1) node before history) (af : Bool) :
    Resumed d initial Post Exit fuel node before history af := by
  rcases rwp.resume residual.generated af with
    ⟨blocked, retained⟩ | ⟨result, retirement, issued, frame, follows⟩
  · exact .blocked blocked ⟨residual.admitted,
      residual.authentic.snoc (step_origin blocked), retained⟩
  · have authentic : OriginTrace d.profile initial
        (issueLog d before history af result) result.1 d.family :=
      residual.authentic.snoc issued.origin
    exact .retired result retirement issued frame authentic
      (Follow.mono (fun _ generated => ⟨residual.admitted, authentic, generated⟩) follows)

/-- Specialization to an observed present step uses only determinism. A native
origin is never used as a converse for `step`; the enabled theorem already
constructed an actual result from current obligations. -/
theorem Residual.resume_of_step {d : Descriptor} {initial before : S} {Post : Assertion}
    {Exit : CutAssertion d} {fuel : Nat} {node : d.graph.Index} {history : Log}
    {af : Bool} {result : S × O}
    (residual : Residual d initial Post Exit (fuel + 1) node before history)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok result) :
    (result = (before, .blocked d.tid) ∧
      Residual d initial Post Exit (fuel + 1) node before
        (issueLog d before history af result)) ∨
    ∃ retirement, RetiredEvidence d node before af result retirement ∧
      Frame d result.1 ∧
      OriginTrace d.profile initial (issueLog d before history af result) result.1 d.family ∧
      Follow d Post Exit (Residual d initial Post Exit fuel)
        node before history af result retirement := by
  cases residual.resume af with
  | blocked blocked retained =>
    have same : result = (before, .blocked d.tid) :=
      Except.ok.inj (actual.symm.trans blocked)
    exact .inl ⟨same, by simpa only [same] using retained⟩
  | retired observed retirement issued frame authentic follows =>
    have same : observed = result := Except.ok.inj (issued.actual.symm.trans actual)
    subst observed
    exact .inr ⟨retirement, issued, frame, authentic, follows⟩

#print axioms Frame.idle
#print axioms issueLog
#print axioms jump
#print axioms jump.mono
#print axioms Follow
#print axioms Follow.mono
#print axioms Follow.returned
#print axioms rwp
#print axioms rwp.here
#print axioms rwp.idle
#print axioms rwp.pause
#print axioms rwp.enabled
#print axioms rwp.resume
#print axioms Frame.next_binding
#print axioms Frame.atomic_next_binding
#print axioms Residual
#print axioms Residual.start
#print axioms Residual.frame
#print axioms Residual.idle
#print axioms Residual.pause
#print axioms Resumed
#print axioms Residual.resume
#print axioms Residual.resume_of_step

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
