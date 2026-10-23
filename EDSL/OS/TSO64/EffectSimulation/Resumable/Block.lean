/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.OneStep
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.OS.TSO64.EffectSimulation.Resources

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Generated bounded ordinary blocks at actual TSO64 instruction boundaries.
Every positive residual is closed under all native passive origins: peer issues
and every drain, including the subject's drains after return. Each resumption
uses the current policy, current resource/read/queue gates, structural decoding
in current local memory, and the production `Effects.oneStep` over uniform Bool
flag choices. No successful future schedule or sequential suffix is a premise.

`Admission` fixes the initial worker, original resource identities, executable
window and caller-word read independently of the generated obligations.
`Residual` separately retains a connected `OriginTrace` from that admitted
state. A log alone supplies no authenticity and no Origin-to-step converse is
used. Initial pending entries need not be empty; their prior issue history is
not invented here. The frame retains protected loans, not shared RAM values.

`Post` and `Exit` are independently selected assertions. A continuing issue
consumes one fuel or exposes `Exit` at a declared cutpoint, with an authenticated
graph edge and actual successor RIP. Zero fuel and atomic/syscall heads fail
closed. Return checks `Post` at the actual response state and exact appended
tick. A later observer must retain that historical witness separately; there is
no claim that `Post` holds in a later publication world.

This module supplies proof-side blocks. The sibling `Resumable.Simulation`
adapter adds eager cutpoint restart and historical done control. Ranks,
accounting, fairness, native RMW boundaries and corpus instances need separate proofs.
Uniform Bool choices are justified only by the current `OrdinaryReady.admitted`
subset; independent vector-only flag choices and DATA1 authority are not added.
Contracts retain the underlying long-mode/CET-off, aligned scalar RAM, WB,
coherence/translation/no-alias, resource and lifetime model boundaries. No
hardware, compiler or unrestricted OS refinement is asserted.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Resumable
open X86

abbrev Assertion := S → Log → Prop

/-- Fixed call and selected-code data. `original` retains entry registers,
phase, resources, FIFO and occurrence counter without freezing future CPUs.
The code extent is confined to the original code loan, independently of RIP. -/
structure Descriptor where
  profile : Profile
  tid : Nat
  bytes : List Byte
  base : Word
  graph : Sequential.CFG.Graph
  graphProfile : Sequential.CFG.Profile
  structural : Sequential.CFG.Structural.Valid bytes graph graphProfile
  original : Worker
  codeLoan : Borrowing.Subregion ⟨base, bytes.length⟩ original.resources.code.loan.region
  callerValue : Word
  policy : S → X86.VCGen.Effects.Policy

abbrev CutAssertion (descriptor : Descriptor) := descriptor.graph.Index → S → Log → Prop

/-- Initial admission concerns only present inputs and resources, with no
return value or future execution premise. The protected caller value is the
return address read through its original loan, not a requested program result. -/
structure Admission (descriptor : Descriptor) (initial : S) : Prop where
  wellFormed : WellFormed initial descriptor.profile
  live : initial.workers[descriptor.tid]? = some descriptor.original
  running : descriptor.original.phase = .running
  code : CodeAt (published initial.world) descriptor.base descriptor.bytes
  caller : Borrowing.loadWord64 initial.world.legacy.shared descriptor.original.resources.actor
    descriptor.original.resources.caller.identifier descriptor.original.resources.callerAddress =
      .ok descriptor.callerValue

/-- Current protected frame. Running phase, entry register equalities, RSP
and shared-memory values are not frame fields. Original resource identity is
tied to a live worker at the original index. -/
structure Frame (descriptor : Descriptor) (state : S) : Prop where
  wellFormed : WellFormed state descriptor.profile
  worker : ∃ current, state.workers[descriptor.tid]? = some current ∧
    current.resources = descriptor.original.resources
  code : CodeAt (published state.world) descriptor.base descriptor.bytes
  caller : Borrowing.loadWord64 state.world.legacy.shared descriptor.original.resources.actor
    descriptor.original.resources.caller.identifier descriptor.original.resources.callerAddress =
      .ok descriptor.callerValue

theorem Admission.frame {descriptor : Descriptor} {initial : S}
    (admitted : Admission descriptor initial) : Frame descriptor initial :=
  ⟨admitted.wellFormed, ⟨descriptor.original, admitted.live, rfl⟩,
    admitted.code, admitted.caller⟩

/-- Derive frame preservation from the existing real resource and protected
loan laws, rather than assuming a shared-memory invariant. -/
theorem Frame.origin {descriptor : Descriptor} {before : S} {action : Action}
    {result : S × O} (frame : Frame descriptor before)
    (origin : Origin before action result descriptor.profile) : Frame descriptor result.1 := by
  obtain ⟨prior, live, original⟩ := frame.worker
  obtain ⟨current, currentLive, retained⟩ := origin_resources origin live
  exact ⟨origin_wellFormed origin frame.wellFormed,
    ⟨current, currentLive, retained.trans original⟩, origin_code origin frame.code,
    origin_loan_read_preserved origin frame.wellFormed frame.caller⟩

theorem Frame.along {descriptor : Descriptor} {initial final : S} {history : Log}
    (trace : OriginTrace descriptor.profile initial history final) :
    Frame descriptor initial → Frame descriptor final := by
  induction trace with
  | nil => exact id
  | cons head _ ih => intro frame; exact ih (frame.origin head)

/-- Passive transport includes own publication after RET. It asserts neither
whole-worker equality nor equality of reconstructed local memory. -/
theorem Frame.pause {descriptor : Descriptor} {before after : S} {history extended : Log}
    (frame : Frame descriptor before)
    (paused : Pause descriptor.profile descriptor.tid (before, history) (after, extended)) :
    Frame descriptor after := by
  obtain ⟨prior, live, original⟩ := frame.worker
  obtain ⟨current, currentLive, retained⟩ := paused.resources live
  exact ⟨paused.wellFormed frame.wellFormed,
    ⟨current, currentLive, retained.trans original⟩, paused.code frame.code,
    paused.loan_read_preserved frame.wellFormed frame.caller⟩

/-- Binding is about this actual worker and this actual boundary. Local code
and decoding are derived below from the protected frame and structural graph. -/
structure Binding (descriptor : Descriptor) (node : descriptor.graph.Index)
    (state : S) (worker : Worker) : Prop where
  live : state.workers[descriptor.tid]? = some worker
  resources : worker.resources = descriptor.original.resources
  running : worker.phase = .running
  pc : worker.context.rip = descriptor.base + BitVec.ofNat 64 (descriptor.graph.node node).offset

theorem Binding.localCode {descriptor : Descriptor} {node : descriptor.graph.Index}
    {state : S} {worker : Worker} (binding : Binding descriptor node state worker)
    (frame : Frame descriptor state) :
    CodeAt (localCPU state worker).memory descriptor.base descriptor.bytes := by
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  apply X86.VCGen.ManagedRules.local_code frame.wellFormed workerValid frame.code
  simpa only [binding.resources] using descriptor.codeLoan

theorem Binding.decoded {descriptor : Descriptor} {node : descriptor.graph.Index}
    {state : S} {worker : Worker} (binding : Binding descriptor node state worker)
    (frame : Frame descriptor state) :
    Sequential.decodeAt (localCPU state worker) = .ok (descriptor.graph.node node).instruction :=
  descriptor.structural.decoded (binding.localCode frame) node (localCPU state worker) rfl binding.pc

/-- No atomic or syscall outcome can satisfy the universal finish obligation
vacuously: an ordinary output must exist before quantifying over real finishes. -/
def OrdinaryOutcome (observation : Sequential.Observation) : Prop :=
  ∃ output, observation.result = .next output ∨ observation.result = .returned output

/-- Generated current-step VC. No Head or selected successor is a client input.
Both choice values run the production `executeWith` through `oneStep`. Queue
and finish quantifiers range only over the real OS semantic relations; readiness
supplies queue existence and `OrdinaryOutcome` supplies finish existence. -/
def One (descriptor : Descriptor) (node : descriptor.graph.Index) (state : S)
    (K : Bool → (S × O) → Sequential.Observation → Prop) : Prop :=
  ∃ worker, Binding descriptor node state worker ∧
    OrdinaryReady state descriptor.tid worker (descriptor.graph.node node).instruction
      descriptor.profile ∧
    X86.VCGen.Effects.oneStep (C := Bool) (descriptor.policy state)
      Sequential.FlagChoices.uniform (localCPU state worker) (descriptor.graph.node node).instruction
      (fun af observation => OrdinaryOutcome observation ∧
        ∀ (update : Queue.Cursor) (result : S × O),
          QueueEffect state worker (descriptor.graph.node node).instruction update descriptor.profile →
          FinishEffect state descriptor.tid worker update.pending observation result update.nextStore →
          K af result observation)

/-- Full checked evidence for the single actual issue. Queue and finish share
one cursor, and Head and Reifies share the complete production observation. -/
structure Issued (descriptor : Descriptor) (node : descriptor.graph.Index)
    (before : S) (af : Bool) (worker : Worker) (observation : Sequential.Observation)
    (update : Queue.Cursor) (result : S × O) : Prop where
  binding : Binding descriptor node before worker
  ready : OrdinaryReady before descriptor.tid worker (descriptor.graph.node node).instruction
    descriptor.profile
  head : X86.VCGen.Effects.Head descriptor.bytes descriptor.base (descriptor.policy before)
    (Sequential.FlagChoices.uniform af) (localCPU before worker)
    (descriptor.graph.node node).instruction observation
  queue : QueueEffect before worker (descriptor.graph.node node).instruction update descriptor.profile
  finish : FinishEffect before descriptor.tid worker update.pending observation result update.nextStore
  actual : step before (.issue descriptor.tid af) descriptor.profile = .ok result
  reifies : Reifies descriptor.tid result observation
  world : result.1.world = before.world
  wellFormed : WellFormed result.1 descriptor.profile

/-- Checking a given semantic finish identifies its result with the production
issue. This only composes the existing executor and checked queue/finish laws. -/
private theorem checked_issue {state : S} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {profile : Profile}
    {bytes : List Byte} {base : Word} {policy : X86.VCGen.Effects.Policy}
    {observation : Sequential.Observation} {update : Queue.Cursor} {result : S × O}
    (ready : OrdinaryReady state tid worker instruction profile)
    (head : X86.VCGen.Effects.Head bytes base policy (Sequential.FlagChoices.uniform af)
      (localCPU state worker) instruction observation)
    (queue : QueueEffect state worker instruction update profile)
    (finish : FinishEffect state tid worker update.pending observation result update.nextStore) :
    step state (.issue tid af) profile = .ok result := by
  have executed := head.actual
  rw [Sequential.stepWith_eq_executeWith _ head.decoded,
    Sequential.executeWith_uniform _ _ af (supported_boolChoiceProfile ready.admitted)] at executed
  obtain ⟨units, reads⟩ := ready.reads
  change issue state tid af profile = .ok result
  simp [issue, ready.live, ready.running, ready.codeCurrent, ready.callerCurrent,
    ready.dispatch, ordinary, ready.admitted, ready.bounds, head.decoded, reads,
    X86.VCGen.ManagedRules.queue_checked queue, executed, Except.mapError,
    X86.VCGen.ManagedRules.finish_checked finish]

/-- Independent one-issue enabledness from present obligations, for either AF.
A real queue and semantic finish first produce a concrete result. Determinism
identifies it with `issue_from_head`, retaining its full `ordinary_reifies`
coherence, unchanged world and checked successor WF. -/
theorem One.resume {descriptor : Descriptor} {node : descriptor.graph.Index} {state : S}
    {K : Bool → (S × O) → Sequential.Observation → Prop}
    (frame : Frame descriptor state) (vc : One descriptor node state K) (af : Bool) :
    ∃ worker observation update result,
      Issued descriptor node state af worker observation update result ∧ K af result observation := by
  obtain ⟨worker, binding, ready, generated⟩ := vc
  obtain ⟨observation, head, _noSyscall, outcome, continuation⟩ :=
    X86.VCGen.Effects.oneStep_head (binding.localCode frame) (binding.decoded frame) generated af
  obtain ⟨update, queue⟩ := ready.queue
  have finishing : ∃ result : S × O,
      FinishEffect state descriptor.tid worker update.pending observation result update.nextStore := by
    obtain ⟨output, next | returned⟩ := outcome
    · let replacement : Worker :=
        { worker with
          context := .ofCPU output
          pending := update.pending
          nextStore := update.nextStore }
      exact ⟨(install state descriptor.tid state.world replacement, .ordinary descriptor.tid),
        .next next⟩
    · let replacement : Worker :=
        { worker with
          context := .ofCPU output
          phase := .returned
          pending := update.pending
          nextStore := update.nextStore }
      exact ⟨(install state descriptor.tid state.world replacement, .returned descriptor.tid),
        .returned returned⟩
  obtain ⟨result, finish⟩ := finishing
  have checked := checked_issue ready head queue finish
  obtain ⟨issued, success, reified, world, valid⟩ := issue_from_head frame.wellFormed ready head
  have same : issued = result := Except.ok.inj (success.symm.trans checked)
  subst issued
  exact ⟨worker, observation, update, result,
    ⟨binding, ready, head, queue, finish, checked, reified, world, valid⟩,
    continuation update result queue finish⟩

/-- The exact unfiltered log extension for this issue. -/
def issueLog (tid : Nat) (before : S) (history : Log) (af : Bool) (result : S × O) : Log :=
  history ++ [⟨before, .issue tid af, result⟩]

/-- Generated control continuation. An exit is exposed only at a declared
cutpoint; no pause-closure of a bare Exit is assumed. The `Resumable.Simulation`
adapter restarts the next block before exposing it to passive interference. -/
def Follow (descriptor : Descriptor) (Post : Assertion) (Exit Tail : CutAssertion descriptor)
    (node : descriptor.graph.Index) (before : S) (history : Log) (af : Bool)
    (result : S × O) (observation : Sequential.Observation) : Prop :=
  match observation.result with
  | .returned _ => Post result.1 (issueLog descriptor.tid before history af result)
  | .next output => ∃ destination : descriptor.graph.Index,
      descriptor.graph.Edge node destination ∧
      output.rip = descriptor.base + BitVec.ofNat 64 (descriptor.graph.node destination).offset ∧
      if descriptor.graph.cutpoint destination then
        Exit destination result.1 (issueLog descriptor.tid before history af result)
      else Tail destination result.1 (issueLog descriptor.tid before history af result)
  | .atomic _ _ | .syscall _ => False

theorem Follow.mono {descriptor : Descriptor} {Post : Assertion}
    {Exit Tail Next : CutAssertion descriptor} {node : descriptor.graph.Index}
    {before : S} {history : Log} {af : Bool} {result : S × O}
    {observation : Sequential.Observation}
    (implies : ∀ destination,
      Tail destination result.1 (issueLog descriptor.tid before history af result) →
      Next destination result.1 (issueLog descriptor.tid before history af result))
    (follows : Follow descriptor Post Exit Tail node before history af result observation) :
    Follow descriptor Post Exit Next node before history af result observation := by
  cases outcome : observation.result with
  | returned output => simpa only [Follow, outcome] using follows
  | atomic event output => simp only [Follow, outcome] at follows
  | syscall request => simp only [Follow, outcome] at follows
  | next output =>
    simp only [Follow, outcome] at follows ⊢
    obtain ⟨destination, edge, pc, after⟩ := follows
    refine ⟨destination, edge, pc, ?_⟩
    by_cases isCut : descriptor.graph.cutpoint destination = true
    · simpa [isCut] using after
    · simp only [isCut] at after ⊢
      exact implies destination after

/-- Return's assertion uses the installed state of this exact tick, never a
later state reached by drains or peer publication. -/
theorem Follow.returned {descriptor : Descriptor} {Post : Assertion}
    {Exit Tail : CutAssertion descriptor} {node : descriptor.graph.Index}
    {before : S} {history : Log} {af : Bool} {result : S × O}
    {observation : Sequential.Observation} {output : X86.State}
    (follows : Follow descriptor Post Exit Tail node before history af result observation)
    (returned : observation.result = .returned output) :
    Post result.1 (issueLog descriptor.tid before history af result) := by
  simpa only [Follow, returned] using follows

/-- Bounded generated interior. Closure occurs at EVERY instruction boundary,
with the same residual node/fuel during pauses and policy re-instantiation at
each actual OS state. The successor protected frame is derived by `resume`
from native resource laws; it is not an assumed future shared-memory frame. -/
def rwp (descriptor : Descriptor) (Post : Assertion) (Exit : CutAssertion descriptor) :
    Nat → descriptor.graph.Index → S → Log → Prop
  | 0, _, _, _ => False
  | fuel + 1, node, state, history =>
      Box descriptor.profile descriptor.tid (fun current past =>
        Frame descriptor current ∧ One descriptor node current
          (Follow descriptor Post Exit (rwp descriptor Post Exit fuel) node current past)) state history

theorem rwp.here {descriptor : Descriptor} {Post : Assertion} {Exit : CutAssertion descriptor}
    {fuel : Nat} {node : descriptor.graph.Index} {state : S} {history : Log}
    (vc : rwp descriptor Post Exit (fuel + 1) node state history) :
    Frame descriptor state ∧ One descriptor node state
      (Follow descriptor Post Exit (rwp descriptor Post Exit fuel) node state history) :=
  Box.here vc

/-- Passive actions consume no ordinary-block fuel and do not change its node. -/
theorem rwp.pause {descriptor : Descriptor} {Post : Assertion} {Exit : CutAssertion descriptor}
    {fuel : Nat} {node : descriptor.graph.Index} {before after : S} {history extended : Log}
    (vc : rwp descriptor Post Exit fuel node before history)
    (paused : Pause descriptor.profile descriptor.tid (before, history) (after, extended)) :
    rwp descriptor Post Exit fuel node after extended := by
  cases fuel with
  | zero => exact False.elim vc
  | succ fuel => exact Box.stable vc paused

/-- Regenerate an actual Head and independently enabled own issue from the
current residual. Full CPU reification fixes the successor used by `Follow`.
This statement does not authenticate an arbitrary input log: use `Residual`
for independent initial admission and connected history extension. -/
theorem rwp.resume {descriptor : Descriptor} {Post : Assertion} {Exit : CutAssertion descriptor}
    {fuel : Nat} {node : descriptor.graph.Index} {before : S} {history : Log}
    (vc : rwp descriptor Post Exit (fuel + 1) node before history) (af : Bool) :
    ∃ worker observation update result,
      Issued descriptor node before af worker observation update result ∧
      Frame descriptor result.1 ∧
      Follow descriptor Post Exit (rwp descriptor Post Exit fuel) node before history af result observation := by
  obtain ⟨frame, one⟩ := rwp.here vc
  obtain ⟨worker, observation, update, result, issued, follows⟩ := One.resume frame one af
  exact ⟨worker, observation, update, result, issued,
    frame.origin (step_origin issued.actual), follows⟩

/-- Complete reification turns the authenticated observation RIP into binding
of the actual successor OS worker, including at an exposed exit cutpoint. -/
theorem Frame.next_binding {descriptor : Descriptor} {destination : descriptor.graph.Index}
    {result : S × O} {observation : Sequential.Observation} {output : X86.State}
    (frame : Frame descriptor result.1) (reified : Reifies descriptor.tid result observation)
    (next : observation.result = .next output)
    (pc : output.rip = descriptor.base + BitVec.ofNat 64 (descriptor.graph.node destination).offset) :
    ∃ worker, Binding descriptor destination result.1 worker := by
  obtain ⟨worker, live, coherence⟩ := reified
  rw [next] at coherence
  obtain ⟨_label, running, cpu⟩ := coherence
  obtain ⟨original, originalLive, resources⟩ := frame.worker
  have same : worker = original := Option.some.inj (live.symm.trans originalLive)
  refine ⟨worker, live, ?_, running, ?_⟩
  · exact (congrArg Worker.resources same).trans resources
  · exact (congrArg X86.State.rip cpu).trans pc

/-- Independently admitted initial state plus authentic connected past, kept
separate from the generated computation. This is a current residual, not a
predicate asserting that a requested future result will occur. -/
structure Residual (descriptor : Descriptor) (initial : S) (Post : Assertion)
    (Exit : CutAssertion descriptor) (fuel : Nat) (node : descriptor.graph.Index)
    (state : S) (history : Log) : Prop where
  admitted : Admission descriptor initial
  authentic : OriginTrace descriptor.profile initial history state
  generated : rwp descriptor Post Exit fuel node state history

theorem Residual.start {descriptor : Descriptor} {initial : S} {Post : Assertion}
    {Exit : CutAssertion descriptor} {fuel : Nat} {node : descriptor.graph.Index}
    (admitted : Admission descriptor initial)
    (generated : rwp descriptor Post Exit fuel node initial []) :
    Residual descriptor initial Post Exit fuel node initial [] :=
  ⟨admitted, .nil, generated⟩

theorem Residual.frame {descriptor : Descriptor} {initial state : S} {Post : Assertion}
    {Exit : CutAssertion descriptor} {fuel : Nat} {node : descriptor.graph.Index} {history : Log}
    (residual : Residual descriptor initial Post Exit fuel node state history) : Frame descriptor state :=
  Frame.along residual.authentic residual.admitted.frame

theorem Residual.pause {descriptor : Descriptor} {initial before after : S} {Post : Assertion}
    {Exit : CutAssertion descriptor} {fuel : Nat} {node : descriptor.graph.Index} {history extended : Log}
    (residual : Residual descriptor initial Post Exit fuel node before history)
    (paused : Pause descriptor.profile descriptor.tid (before, history) (after, extended)) :
    Residual descriptor initial Post Exit fuel node after extended :=
  ⟨residual.admitted, paused.authentic residual.authentic, rwp.pause residual.generated paused⟩

/-- Resume with exact authentic history extension. Interior successors retain
an independently admitted, connected residual with one less fuel; cutpoints
expose only the declared Exit. A return's Post remains indexed by this immutable
actual issue tick. No successful future run is assumed for enabledness. -/
theorem Residual.resume {descriptor : Descriptor} {initial before : S} {Post : Assertion}
    {Exit : CutAssertion descriptor} {fuel : Nat} {node : descriptor.graph.Index} {history : Log}
    (residual : Residual descriptor initial Post Exit (fuel + 1) node before history) (af : Bool) :
    ∃ worker observation update result,
      Issued descriptor node before af worker observation update result ∧
      Frame descriptor result.1 ∧
      OriginTrace descriptor.profile initial (issueLog descriptor.tid before history af result) result.1 ∧
      Follow descriptor Post Exit (Residual descriptor initial Post Exit fuel)
        node before history af result observation := by
  obtain ⟨worker, observation, update, result, issued, frame, follows⟩ :=
    rwp.resume residual.generated af
  have authentic : OriginTrace descriptor.profile initial
      (issueLog descriptor.tid before history af result) result.1 :=
    residual.authentic.snoc (step_origin issued.actual)
  refine ⟨worker, observation, update, result, issued, frame, authentic, ?_⟩
  exact Follow.mono (fun _ generated => ⟨residual.admitted, authentic, generated⟩) follows

#print axioms Descriptor
#print axioms Admission.frame
#print axioms Frame.origin
#print axioms Frame.along
#print axioms Frame.pause
#print axioms Binding.localCode
#print axioms Binding.decoded
#print axioms One
#print axioms Issued
#print axioms One.resume
#print axioms Follow.mono
#print axioms Follow.returned
#print axioms rwp
#print axioms rwp.here
#print axioms rwp.pause
#print axioms rwp.resume
#print axioms Frame.next_binding
#print axioms Residual.start
#print axioms Residual.frame
#print axioms Residual.pause
#print axioms Residual.resume

end EDSL.OS.TSO64.EffectSimulation.Resumable

#audit_edsl
