/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.History
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphPublicationEvents
import EDSL.OS.TSO64.C23Projection.AtomicTrace.WriterRanks
import EDSL.OS.TSO64.StoreHistory.Order

/-!
Publication bounds from the actual output of a closed plain64 run. A store's
real issue leaves its complete managed entry pending. Restricting that pending
cut to an independently successful quiescent prefix forces its actual drain
before the prefix ends. The retained stamp belongs to the original run and
matches the original Post outcome with the Post's actual source annotation.

An initial issue-only block additionally bounds every buffered publication
from below: its actual drain observation requires a drain action. These are
output-run lemmas, with arbitrary words, counters and worker population. They
add no admission gate, source selection, graph construction or corpus credit.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallWitness64
open X86 TSO64 TSO64.C23Projection TSO64.C23Projection.AtomicTrace
  TSO64.PublishedHistory TSO64.StoreHistory

/-- An actual managed issue before a successful quiet cut has a complete
publication in the original run, strictly between its issue and that cut.
The shorter run's observations are recovered by determinism. In particular,
this does not use a converse of `IssuedAt.lift_prefix`. -/
theorem issued_publication_before_cut {initial : TSO64.State}
    {actions : List Action} {result prefixResult : TSO64.State × List Observation}
    {profile : Profile} {tid index cut occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      index initial actions result)
    (sequenced : Sequenced initial)
    (earlier : index < cut)
    (prefixRun : schedule initial (actions.take cut) profile = .ok prefixResult)
    (quiet : Quiescent prefixResult.1) :
    ∃ stamp, stamp ∈ writes 0 result.2 ∧
      stamp.cause = .buffered tid reference value occurrence ∧
      index < stamp.position ∧ stamp.position < cut := by
  obtain ⟨after, issuedPrefix, pending⟩ := Graph.issued_pending_at issued
  have contained : index + 1 ≤ cut := by omega
  have observations := (ScheduleTrace.suffix issued.forget.scheduled prefixRun).1
  have restricted :
      schedule initial ((actions.take cut).take (index + 1)) profile =
        .ok (after, prefixResult.2.take (index + 1)) := by
    rw [List.take_take, Nat.min_eq_left contained, observations,
      List.take_take, Nat.min_eq_left contained]
    exact issuedPrefix
  obtain ⟨publication⟩ :=
    pending_managed_publication prefixRun sequenced restricted quiet pending
  obtain ⟨published⟩ := publication.writeAt 0
  obtain ⟨whole⟩ := published.lift_prefix issued.forget.scheduled
  refine ⟨publication.stamp 0, writeAt_mem_writes whole, rfl, ?_, ?_⟩
  · have future := publication.future
    change index < 0 + publication.index
    omega
  · have bound := writes_bounds (publication.stamp_mem_writes 0)
    have prefixLength : prefixResult.2.length ≤ cut := by
      rw [ScheduleTrace.length prefixRun]
      exact List.length_take_le cut actions
    omega

private theorem drained_action {state next : TSO64.State} {action : Action}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok (next, .drained tid entry)) :
    action = .drain tid := by
  cases step_origin success with
  | ordinary _live _running _code _caller _fetched effect =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | drained => rfl

/-- A drain observed in a real run cannot lie in its initial issue-only
block. Block length counts all original actions, without a FIFO-size premise. -/
theorem drained_after_issue_prefix {initial : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile}
    {issueCount index tid : Nat} {entry : Pending}
    (success : schedule initial actions profile = .ok result)
    (issueOnly : ∀ action ∈ actions.take issueCount,
      ∃ issuer af, action = .issue issuer af)
    (observed : result.2[index]? = some (.drained tid entry)) :
    issueCount ≤ index := by
  obtain ⟨before, action, next, _prefixRun, selected, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  have drain := drained_action stepped
  by_cases inside : index < issueCount
  · have selectedPrefix : (actions.take issueCount)[index]? = some action := by
      simpa only [List.getElem?_take_of_lt inside] using selected
    obtain ⟨issuer, af, issue⟩ := issueOnly action (List.mem_of_getElem? selectedPrefix)
    have impossible : Action.drain tid = .issue issuer af := drain.symm.trans issue
    cases impossible
  · omega

/-- Every complete buffered cause in the real write enumeration is published
at or after an initial issue-only block. The actual observation and its drain
action supply the bound; an RMW is deliberately not classified as buffered. -/
theorem buffered_publication_after_issue_prefix {initial : TSO64.State}
    {actions : List Action} {result : TSO64.State × List Observation} {profile : Profile}
    {issueCount tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    {stamp : Stamp}
    (success : schedule initial actions profile = .ok result)
    (issueOnly : ∀ action ∈ actions.take issueCount,
      ∃ issuer af, action = .issue issuer af)
    (member : stamp ∈ writes 0 result.2)
    (buffered : stamp.cause = .buffered tid reference value occurrence) :
    issueCount ≤ stamp.position := by
  cases stamp with
  | mk position cause =>
      change cause = .buffered tid reference value occurrence at buffered
      subst cause
      obtain ⟨actual⟩ := writes_origin success member
      have lower := drained_after_issue_prefix success issueOnly actual.buffered_observed
      have actualPosition := actual.position
      change position = 0 + actual.index at actualPosition
      change issueCount ≤ position
      omega

end EDSL.OS.PlainCallWitness64

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS OS.TSO64 OS.TSO64.C23Projection

/-- Recover a Post slot's actual event at its original data-access position.
The source is exactly `post.sources tid`, and the execution is exactly the
Post's `actual`, rather than an independently reconstructed scanner result. -/
theorem ClosedPost.outcome_event_origin {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : ClosedPost before inputs actions actual 0) (tid : Fin before.workers.length) :
    AtomicTrace.EventAt .sharedCell
      ((post.calls.outcomes tid).machineEvent (post.sources tid) 0)
      (post.calls.outcomes tid).performed before actions actual 0 PublishedHistory.empty := by
  have slot : tid ∈ post.calls.slots :=
    post.calls.permutation.mem_iff.mpr (List.mem_finRange tid)
  have member : (post.calls.outcomes tid).machineEvent (post.sources tid) 0 ∈
      post.run.events := by
    rw [post.machineEvents]
    exact List.mem_map.mpr ⟨tid, slot, rfl⟩
  obtain ⟨eventIndex, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, same⟩ := List.getElem_of_getElem? selected
  obtain ⟨index, origin⟩ := post.captured.event_origin ⟨eventIndex, bound⟩
  have actualOrigin : AtomicTrace.EventAt .sharedCell
      ((post.calls.outcomes tid).machineEvent (post.sources tid) 0)
      index before actions actual 0 PublishedHistory.empty := by
    simpa only [same, post.execution] using origin
  have position := actualOrigin.position
  have sameIndex : index = (post.calls.outcomes tid).performed := by
    simpa only [Outcome.machineEvent, Nat.zero_add] using position.symm
  simpa only [sameIndex] using actualOrigin

private theorem outcome_store_access {input : Input} {before : TSO64.State}
    {actions : List Action} {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) (source : AtomicTrace.WriterId)
    (writing : input.site.kind = .storeRelease) :
    ∃ value, (outcome.machineEvent source 0).access =
      .store outcome.reference value outcome.initial.nextStore := by
  cases input with
  | loadAcquire image target cell occurrence => cases writing
  | storeRelease image target cell value occurrence => exact ⟨value, rfl⟩

/-- The actual store outcome has a complete graph publication before an
actual successful quiet prefix ends. Capture, sources, the stamp and its
position are derived from the supplied ClosedPost and the original run. -/
theorem ClosedPost.store_published_before_cut {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual prefixResult : TSO64.State × List Observation} {cut : Nat}
    (post : ClosedPost before inputs actions actual 0) (writer : Fin before.workers.length)
    (writing : (inputs writer).site.kind = .storeRelease)
    (earlier : (post.calls.outcomes writer).performed < cut)
    (prefixRun : schedule before (actions.take cut) .sharedCell = .ok prefixResult)
    (quiet : Quiescent prefixResult.1) :
    ∃ stamp, stamp ∈ C23Projection.writes 0 actual.2 ∧
      AtomicTrace.Graph.Publication
        ((post.calls.outcomes writer).machineEvent (post.sources writer) 0) stamp ∧
      stamp.position < cut := by
  obtain ⟨value, stored⟩ :=
    outcome_store_access (post.calls.outcomes writer) (post.sources writer) writing
  have issued := AtomicTrace.Graph.store_issued_at (post.outcome_event_origin writer) stored
  obtain ⟨stamp, member, cause, later, inside⟩ :=
    PlainCallWitness64.issued_publication_before_cut issued post.captured.sequenced
      earlier prefixRun quiet
  refine ⟨stamp, member, ?_, inside⟩
  rw [AtomicTrace.Graph.Publication, stored]
  exact ⟨cause, by simpa only [Outcome.machineEvent, Nat.zero_add] using later⟩

/-- The same derived publication also lies after every initial issue-only
block. A downstream writer RET strictly inside that block is therefore
strictly before this stamp, without postulating a publication position. -/
theorem ClosedPost.store_published_between_cuts {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {actions : List Action}
    {actual prefixResult : TSO64.State × List Observation} {cut issueCount : Nat}
    (post : ClosedPost before inputs actions actual 0) (writer : Fin before.workers.length)
    (writing : (inputs writer).site.kind = .storeRelease)
    (earlier : (post.calls.outcomes writer).performed < cut)
    (prefixRun : schedule before (actions.take cut) .sharedCell = .ok prefixResult)
    (quiet : Quiescent prefixResult.1)
    (issueOnly : ∀ action ∈ actions.take issueCount,
      ∃ issuer af, action = .issue issuer af) :
    ∃ stamp, stamp ∈ C23Projection.writes 0 actual.2 ∧
      AtomicTrace.Graph.Publication
        ((post.calls.outcomes writer).machineEvent (post.sources writer) 0) stamp ∧
      issueCount ≤ stamp.position ∧ stamp.position < cut := by
  obtain ⟨stamp, member, matched, inside⟩ :=
    post.store_published_before_cut writer writing earlier prefixRun quiet
  obtain ⟨value, stored⟩ :=
    outcome_store_access (post.calls.outcomes writer) (post.sources writer) writing
  have cause := matched
  rw [AtomicTrace.Graph.Publication, stored] at cause
  have lower := PlainCallWitness64.buffered_publication_after_issue_prefix
    post.calls.scheduled issueOnly member cause.1
  exact ⟨stamp, member, matched, lower, inside⟩

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
