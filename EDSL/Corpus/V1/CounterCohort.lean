/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterGCC
import EDSL.Corpus.V1.CounterClang
import EDSL.OS.TSO64.ScheduleTrace
import EDSL.OS.TSO64History
import EDSL.OS.TSO64.EffectSimulation.Mixed.EventCounts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Completion evidence for cohorts of the frozen counter workers. Event properties
transfer through each worker's own complete observation projection; independently
produced stateful ghost histories are never identified. Scheduler slots remain
separate from resource actors.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- The complete observed log retains each own event's independently named
atomic target, address, actor and unit input. This forgets no scheduler position
and does not identify another annotation's stateful history with this one. -/
theorem completed_events {c : Compiler} {site : Site c} {call : Call}
    (annotations : Mixed.Annotations (descriptor site call) (Post site call))
    {initial final : S} {node : (descriptor site call).graph.Index}
    (entry : Mixed.Entry annotations initial node)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    ∀ event, .rmw site.tid event ∈ observations → EventOK site call event := by
  obtain ⟨next, _related, _trace, _authentic, post, _actions, sameObservations⟩ :=
    annotations.schedule_completion entry (stablePost site call) actual live returned
  intro event member
  rw [← sameObservations] at member
  obtain ⟨tick, inHistory, observed⟩ := List.mem_map.mp member
  exact (post.increments tick inHistory event observed).1

/-- Reuse the checked complete GCC or Clang annotation from present admission.
No caller-supplied generated annotations or future behavior enter admission. -/
theorem Pre.completed_events {c : Compiler} {site : Site c} {call : Call}
    {initial final : S} (pre : Pre site call initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    ∀ event, .rmw site.tid event ∈ observations → EventOK site call event := by
  cases c with
  | defaultGCC =>
    exact CounterCommon.completed_events (CounterGCC.annotations site call pre.callerCanonical)
      (CounterGCC.entry_of_pre pre) actual live returned
  | defaultClang =>
    exact CounterCommon.completed_events (CounterClang.annotations site call pre.callerCanonical pre.stack)
      (CounterClang.entry_of_pre pre) actual live returned

/-- Uniform count interface for either admitted compiler window. -/
theorem Pre.completed_count {c : Compiler} {site : Site c} {call : Call}
    {initial final : S} (pre : Pre site call initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    Mixed.Counts.countRMW site.tid observations = call.iterations.toNat := by
  cases c with
  | defaultGCC => exact CounterGCC.completed_count pre actual live returned
  | defaultClang => exact CounterClang.completed_count pre actual live returned

end EDSL.Corpus.V1.CounterCommon

namespace EDSL.OS.TSO64.ScheduleTrace
open X86

/-- Every actual RMW issuer belongs to the original finite worker universe.
The proof uses its real prefix and checked step, independently of event actors. -/
theorem rmw_tid_lt {initial final : State} {actions : List Action}
    {observations : List Observation} {profile : Profile} {family : RMWFamily}
    (actual : schedule initial actions profile family = .ok (final, observations))
    {tid : Nat} {event : Atomics64.FetchAddEvent}
    (member : .rmw tid event ∈ observations) : tid < initial.workers.length := by
  obtain ⟨index, observed⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨before, action, after, prefixRun, _actionAt, stepped⟩ :=
    observation_at actual observed
  have lengthEq : before.workers.length = initial.workers.length := workers_length prefixRun
  cases step_origin stepped with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | rmw live _running _code _caller _fetched _bounds _empty _grant _effect =>
    have bound := (List.getElem_of_getElem? live).1
    simpa only [lengthEq] using bound

end EDSL.OS.TSO64.ScheduleTrace

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Two admitted compiler workers sharing an independently registered cell
produce the requested modular sum on every actual finite schedule that returns
both workers. The exhaustive original slots authenticate every RMW issuer.

The current memory value is obtained from actual OS history conservation, not
from counts alone. Initial queues may be nonempty under the owned-only profile:
its checked ordinary publications cannot modify a registered atomic allocation.
This theorem does not release resources, establish progress, frame unrelated
ordinary writes, or claim physical hardware/compiler refinement. -/
theorem two_completed_total {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial final : S}
    (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1)
    (workerUniverse : initial.workers.length = 2)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations))
    {leftWorker rightWorker : Worker}
    (leftLive : final.workers[left.tid]? = some leftWorker)
    (rightLive : final.workers[right.tid]? = some rightWorker)
    (leftReturned : leftWorker.phase = .returned) (rightReturned : rightWorker.phase = .returned)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (registered : initial.world.cells target = some cell)
    (leftTarget : leftCall.target = target) (rightTarget : rightCall.target = target)
    (prior : Word)
    (readBefore : loadQWord (AddressSpace.toMemory initial.world.legacy.shared.resources.space)
      cell.address = .ok prior) :
    ∃ value,
      loadQWord (AddressSpace.toMemory final.world.legacy.shared.resources.space)
        cell.address = .ok value ∧
      value.toNat =
        (prior.toNat + leftCall.iterations.toNat + rightCall.iterations.toNat) % 2^64 := by
  have leftRun : TSO64.schedule initial actions left.profile .arithmetic =
      .ok (final, observations) := by rw [leftProfile]; exact actual
  have rightRun : TSO64.schedule initial actions right.profile .arithmetic =
      .ok (final, observations) := by rw [rightProfile]; exact actual
  have leftCount := leftPre.completed_count leftRun leftLive leftReturned
  have rightCount := rightPre.completed_count rightRun rightLive rightReturned
  have leftEvents := leftPre.completed_events leftRun leftLive leftReturned
  have rightEvents := rightPre.completed_events rightRun rightLive rightReturned
  have covered : ∀ tid event, Observation.rmw tid event ∈ observations → tid = 0 ∨ tid = 1 := by
    intro tid event member
    have bound := ScheduleTrace.rmw_tid_lt actual member
    rw [workerUniverse] at bound
    omega
  have increments : ∀ tid event, Observation.rmw tid event ∈ observations →
      event.cell = target ∧ event.arithmetic.delta = 1 := by
    intro tid event member
    rcases covered tid event member with leftIssuer | rightIssuer
    · have observed : Observation.rmw left.tid event ∈ observations := by
        simpa only [leftSlot, leftIssuer] using member
      have eventOK := leftEvents event observed
      exact ⟨eventOK.2.1.trans leftTarget, eventOK.2.2.2.1⟩
    · have observed : Observation.rmw right.tid event ∈ observations := by
        simpa only [rightSlot, rightIssuer] using member
      have eventOK := rightEvents event observed
      exact ⟨eventOK.2.1.trans rightTarget, eventOK.2.2.2.1⟩
  have total : Mixed.EventCounts.totalRMW observations =
      leftCall.iterations.toNat + rightCall.iterations.toNat :=
    Mixed.EventCounts.totalRMW_eq_two_of_counts (left := 0) (right := 1) (by decide)
      covered (by simpa only [leftSlot] using leftCount)
      (by simpa only [rightSlot] using rightCount)
  have valid : WellFormed initial := by
    simpa only [descriptor, leftProfile] using leftPre.admitted.wellFormed
  obtain ⟨value, readAfter, legal⟩ := TSO64History.schedule_sequential valid actual target cell
    registered (fun _ => ()) (fun event => event.actor) prior readBefore
  have inputTotal := Mixed.EventCounts.inputSum_selectedCalls_eq_totalRMW target
    (fun _ => ()) (fun event => event.actor) observations increments
  refine ⟨value, readAfter, ?_⟩
  rw [legal.total, inputTotal, total]
  simp only [Nat.add_assoc]

end EDSL.Corpus.V1.CounterCommon

#print axioms EDSL.Corpus.V1.CounterCommon.two_completed_total

#print axioms EDSL.Corpus.V1.CounterCommon.completed_events
#print axioms EDSL.Corpus.V1.CounterCommon.Pre.completed_events
#print axioms EDSL.Corpus.V1.CounterCommon.Pre.completed_count
#print axioms EDSL.OS.TSO64.ScheduleTrace.rmw_tid_lt

#audit_edsl
