/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Order

/-!
Same-thread instruction-write order and actual publication order for arbitrary
successful schedules mixing managed stores and locked RMWs. A buffered writer
must have a real issue witness in this run. Incoming initial FIFO entries may
exist, but are never assigned invented instruction positions.

Only numerical FIFO integrity is assumed. In particular these order contracts
need neither final quiescence, source legality, checker acceptance, a supplied
publication order, nor a monotonic-view invariant. Causes retain the complete
worker, authority reference, word, occurrence and RMW event. Every position
counts all scheduler actions, including peer actions and ordinary entries.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

private theorem write_order_rmw_empty {state next : State} {action : Action}
    {profile : Profile} {tid : Nat} {event : Atomics64.FetchAddEvent}
    (success : step state action profile = .ok (next, .rmw tid event)) :
    ∃ worker, state.workers[tid]? = some worker ∧ worker.pending = [] := by
  cases step_origin (profile := profile) success with
  | ordinary _live _running _code _caller _fetched effect =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | rmw live _running _code _caller _fetched _bounds empty _grant _effect =>
      exact ⟨_, live, empty⟩

/-- A committed ordinary store and an RMW cannot occupy the same instruction
position, including when both happen to write the same word to the same cell. -/
theorem IssuedAt.not_rmw {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid index otherTid : Nat}
    {entry : Pending} (issued : IssuedAt profile tid entry index state actions result)
    (event : Atomics64.FetchAddEvent) :
    result.2[index]? ≠ some (.rmw otherTid event) := by
  induction issued with
  | @head _state _action _rest first _tail _stepped _following actual =>
      intro observed
      have actualObservation : first.2 = Observation.rmw otherTid event := by
        simpa only [List.getElem?_cons_zero, Option.some.injEq] using observed
      cases actual with
      | ordinary _issuing _success _live _fetched _effect _intent _admission committed =>
          cases committed <;> cases actualObservation
  | later _stepped _following _actual ih =>
      simpa only [List.getElem?_cons_succ] using ih

/-- An actual managed issue is strictly before every matching actual drain.
The initial FIFOs may be nonempty. If a matching drain were earlier, its
post-drain counter would already exceed the occurrence a later issue must
allocate; an equal-position ordinary issue cannot be a drain. No existence
or quiescence premise is used. -/
theorem IssuedAt.index_lt_managed_drain {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid occurrence issueIndex drainIndex : Nat}
    {reference otherReference : Queue.ManagedRef} {value otherValue : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      issueIndex state actions result)
    (sequenced : Sequenced state)
    (observed : result.2[drainIndex]? =
      some (.drained tid (.managed otherReference otherValue occurrence))) :
    issueIndex < drainIndex := by
  induction issued generalizing drainIndex with
  | @head _state _action _rest first _tail _stepped _following actual =>
      cases drainIndex with
      | zero =>
          have actualObservation : first.2 =
              Observation.drained tid (.managed otherReference otherValue occurrence) := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using observed
          cases actual with
          | ordinary _issuing _success _live _fetched _effect _intent _admission committed =>
              cases committed <;> cases actualObservation
      | succ drainIndex => exact Nat.zero_lt_succ drainIndex
  | @later state action _rest first tail _index stepped _following actual ih =>
      cases drainIndex with
      | zero =>
          have actualObservation : first.2 =
              Observation.drained tid (.managed otherReference otherValue occurrence) := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using observed
          have drained : step state action profile =
              .ok (first.1, .drained tid (.managed otherReference otherValue occurrence)) := by
            rw [← actualObservation]
            exact stepped
          obtain ⟨_retained, _current, live, past⟩ :=
            step_managed_drain_lower sequenced drained
          have lower := actual.occurrence_lower live
          omega
      | succ drainIndex =>
          have later : tail.2[drainIndex]? =
              some (Observation.drained tid (.managed otherReference otherValue occurrence)) := by
            simpa only [List.getElem?_cons_succ] using observed
          exact Nat.succ_lt_succ (ih (step_sequenced sequenced stepped) later)

/-- Every real store issue preceding an actual own RMW has an exact drain
strictly between the issue and that RMW. The RMW's real own-empty gate forces
this existence: conservation through the actual prefix excludes a retained
entry. This statement works for ordinary as well as managed stores and needs
neither numerical FIFO integrity nor final quiescence. -/
theorem IssuedAt.drain_before_rmw {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid issueIndex rmwIndex : Nat}
    {entry : Pending} {event : Atomics64.FetchAddEvent}
    (issued : IssuedAt profile tid entry issueIndex state actions result)
    (observed : result.2[rmwIndex]? = some (.rmw tid event))
    (earlier : issueIndex < rmwIndex) :
    ∃ drainIndex, issueIndex < drainIndex ∧ drainIndex < rmwIndex ∧
      result.2[drainIndex]? = some (.drained tid entry) := by
  induction issued generalizing rmwIndex with
  | @head _state _action _rest _first tail _stepped following actual =>
      cases rmwIndex with
      | zero => omega
      | succ rmwIndex =>
          have later : tail.2[rmwIndex]? = some (Observation.rmw tid event) := by
            simpa only [List.getElem?_cons_succ] using observed
          obtain ⟨_before, _action, _next, prefixRun, _selected, rmwStep⟩ :=
            ScheduleTrace.observation_at following later
          obtain ⟨worker, workerLive, empty⟩ := write_order_rmw_empty rmwStep
          rcases schedule_pending_retained_or_drained prefixRun actual.queued with retained | drained
          · obtain ⟨current, currentLive, member⟩ := retained
            have same : current = worker := Option.some.inj (currentLive.symm.trans workerLive)
            subst current
            rw [empty] at member
            cases member
          · obtain ⟨drainIndex, selected⟩ := List.mem_iff_getElem?.mp drained
            have bound := (List.getElem_of_getElem? selected).1
            have beforeRMW : drainIndex < rmwIndex :=
              Nat.lt_of_lt_of_le bound (List.length_take_le _ _)
            have published : tail.2[drainIndex]? = some (Observation.drained tid entry) := by
              simpa only [List.getElem?_take_of_lt beforeRMW] using selected
            exact ⟨drainIndex + 1, Nat.zero_lt_succ drainIndex,
              Nat.succ_lt_succ beforeRMW, published⟩
  | @later _state _action _rest _first tail _index _stepped _following _actual ih =>
      cases rmwIndex with
      | zero => omega
      | succ rmwIndex =>
          have later : tail.2[rmwIndex]? = some (Observation.rmw tid event) := by
            simpa only [List.getElem?_cons_succ] using observed
          obtain ⟨drainIndex, afterIssue, beforeRMW, published⟩ :=
            ih later (Nat.lt_of_succ_lt_succ earlier)
          exact ⟨drainIndex + 1, Nat.succ_lt_succ afterIssue,
            Nat.succ_lt_succ beforeRMW, published⟩

/-- A same-thread managed store is before an actual RMW exactly when its
matching actual publication is before that RMW. Forward order is forced by
the own-empty gate and actual drain uniqueness, rather than assumed as a
publication-order premise. The complete original store entry is retained. -/
theorem IssuedAt.before_rmw_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid occurrence issueIndex drainIndex rmwIndex : Nat}
    {reference : Queue.ManagedRef} {value : Word} {event : Atomics64.FetchAddEvent}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      issueIndex state actions result)
    (sequenced : Sequenced state)
    (published : result.2[drainIndex]? =
      some (.drained tid (.managed reference value occurrence)))
    (rmw : result.2[rmwIndex]? = some (.rmw tid event)) :
    issueIndex < rmwIndex ↔ drainIndex < rmwIndex := by
  constructor
  · intro earlier
    obtain ⟨actualDrain, _afterIssue, beforeRMW, observed⟩ := issued.drain_before_rmw rmw earlier
    have same := managed_drain_index_unique issued.forget.scheduled sequenced observed published
    omega
  · intro earlier
    have afterIssue := issued.index_lt_managed_drain sequenced published
    omega

/-- The reverse mixed direction follows from actual issue-before-drain,
store-before-RMW, and disjointness of ordinary-issue and RMW positions. -/
theorem IssuedAt.rmw_before_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid occurrence issueIndex drainIndex rmwIndex : Nat}
    {reference : Queue.ManagedRef} {value : Word} {event : Atomics64.FetchAddEvent}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      issueIndex state actions result)
    (sequenced : Sequenced state)
    (published : result.2[drainIndex]? =
      some (.drained tid (.managed reference value occurrence)))
    (rmw : result.2[rmwIndex]? = some (.rmw tid event)) :
    rmwIndex < issueIndex ↔ rmwIndex < drainIndex := by
  have afterIssue := issued.index_lt_managed_drain sequenced published
  have beforeRMW := issued.before_rmw_iff sequenced published rmw
  constructor
  · intro earlier
    omega
  · intro earlier
    rcases Nat.lt_trichotomy issueIndex rmwIndex with before | same | after
    · have beforeDrain := beforeRMW.mp before
      omega
    · subst rmwIndex
      exact False.elim (issued.not_rmw event rmw)
    · exact after

end EDSL.OS.TSO64.StoreHistory

namespace EDSL.OS.TSO64.PublishedHistory
open X86

private theorem write_order_rmw_observation {observation : Observation} {tid : Nat}
    {event : Atomics64.FetchAddEvent}
    (written : writeOf observation = some (.rmw tid event)) : observation = .rmw tid event := by
  cases observation with
  | ordinary => simp [writeOf] at written
  | returned => simp [writeOf] at written
  | blocked => simp [writeOf] at written
  | drained actual entry => cases entry <;> simp [writeOf] at written
  | rmw actual changed =>
      have same : WriteCause.rmw actual changed = .rmw tid event := Option.some.inj written
      cases same
      rfl

/-- Recover the full actual RMW observation behind a publication stamp. -/
theorem WriteAt.rmw_observed {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid : Nat}
    {event : Atomics64.FetchAddEvent}
    (witness : WriteAt state actions result profile offset ⟨position, .rmw tid event⟩) :
    result.2[witness.index]? = some (.rmw tid event) := by
  have observed := write_order_rmw_observation witness.written
  simpa only [observed] using witness.observed

/-- One instruction write and its real publication, preserving the complete
cause and arbitrary observation-stream offset. Buffered causes require a real
`IssuedAt` for the exact entry at `instructionIndex`. An RMW's instruction and
publication are the same actual scheduler action. Initial queued entries may
publish, but cannot inhabit the buffered branch without an actual issue. -/
structure InstructionWriteAt (state : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset instructionIndex : Nat)
    (stamp : Stamp) where
  publication : WriteAt state actions result profile offset stamp
  actual : match stamp.cause with
    | .buffered tid reference value occurrence =>
        StoreHistory.IssuedAt profile tid (.managed reference value occurrence)
          instructionIndex state actions result
    | .rmw _ _ => instructionIndex = publication.index

/-- Build the buffered branch from independently supplied actual issue and
actual matching publication witnesses. Neither witness may be inferred from
an equal payload or an intended timestamp. -/
def InstructionWriteAt.buffered {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset instructionIndex position tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (issued : StoreHistory.IssuedAt profile tid (.managed reference value occurrence)
      instructionIndex state actions result)
    (published : WriteAt state actions result profile offset
      ⟨position, .buffered tid reference value occurrence⟩) :
    InstructionWriteAt state actions result profile offset instructionIndex
      ⟨position, .buffered tid reference value occurrence⟩ := ⟨published, issued⟩

/-- The RMW branch uses the publication witness's actual scheduler position,
including zero-delta events and repeated equal complete event payloads. -/
def InstructionWriteAt.rmw {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid : Nat}
    {event : Atomics64.FetchAddEvent}
    (published : WriteAt state actions result profile offset ⟨position, .rmw tid event⟩) :
    InstructionWriteAt state actions result profile offset published.index
      ⟨position, .rmw tid event⟩ := ⟨published, rfl⟩

/-- Actual same-thread instruction writes and their full publication stamps
have exactly the same strict order for arbitrary multi-access mixed traces.
Different cells, authority references, equal values, intervening ordinary
entries and arbitrary peer actions are allowed. No quiescence, source graph,
legality, checker result or prior view-order invariant is assumed. -/
theorem InstructionWriteAt.order_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset firstIndex secondIndex : Nat} {firstStamp secondStamp : Stamp}
    (first : InstructionWriteAt state actions result profile offset firstIndex firstStamp)
    (second : InstructionWriteAt state actions result profile offset secondIndex secondStamp)
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (sameThread : firstStamp.cause.tid = secondStamp.cause.tid) :
    firstIndex < secondIndex ↔ firstStamp.position < secondStamp.position := by
  cases firstStamp with
  | mk firstPosition firstCause =>
      cases secondStamp with
      | mk secondPosition secondCause =>
          cases firstCause with
          | buffered firstTid firstReference firstValue firstOccurrence =>
              cases secondCause with
              | buffered secondTid secondReference secondValue secondOccurrence =>
                  change firstTid = secondTid at sameThread
                  subst secondTid
                  have issueOrder := first.actual.index_lt_iff_occurrence_lt second.actual
                  have publicationOrder := StoreHistory.managed_drain_order_iff success sequenced
                    first.publication.buffered_observed second.publication.buffered_observed
                  have order := issueOrder.trans publicationOrder.symm
                  have firstAt := first.publication.position
                  have secondAt := second.publication.position
                  constructor
                  · intro earlier
                    have before := order.mp earlier
                    omega
                  · intro earlier
                    apply order.mpr
                    omega
              | rmw secondTid secondEvent =>
                  change firstTid = secondTid at sameThread
                  subst secondTid
                  have order := first.actual.before_rmw_iff sequenced
                    first.publication.buffered_observed second.publication.rmw_observed
                  have firstAt := first.publication.position
                  have secondAt := second.publication.position
                  have actualSecond : secondIndex = second.publication.index := second.actual
                  constructor
                  · intro earlier
                    have before : firstIndex < second.publication.index := by omega
                    have publishedBefore := order.mp before
                    omega
                  · intro earlier
                    have before : first.publication.index < second.publication.index := by omega
                    have instructionBefore := order.mpr before
                    omega
          | rmw firstTid firstEvent =>
              cases secondCause with
              | buffered secondTid secondReference secondValue secondOccurrence =>
                  change firstTid = secondTid at sameThread
                  subst secondTid
                  have order := second.actual.rmw_before_iff sequenced
                    second.publication.buffered_observed first.publication.rmw_observed
                  have firstAt := first.publication.position
                  have secondAt := second.publication.position
                  have actualFirst : firstIndex = first.publication.index := first.actual
                  constructor
                  · intro earlier
                    have before : first.publication.index < secondIndex := by omega
                    have publishedBefore := order.mp before
                    omega
                  · intro earlier
                    have before : first.publication.index < second.publication.index := by omega
                    have instructionBefore := order.mpr before
                    omega
              | rmw secondTid secondEvent =>
                  have firstAt := first.publication.position
                  have secondAt := second.publication.position
                  have actualFirst : firstIndex = first.publication.index := first.actual
                  have actualSecond : secondIndex = second.publication.index := second.actual
                  constructor <;> intro earlier <;> omega

/-- Publication ranks reserve zero for an initialized boundary and otherwise
use actual full publication positions plus one. The same strict-order theorem
therefore applies to these ranks at any common arbitrary stream offset. -/
theorem InstructionWriteAt.rank_order_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset firstIndex secondIndex : Nat} {firstStamp secondStamp : Stamp}
    (first : InstructionWriteAt state actions result profile offset firstIndex firstStamp)
    (second : InstructionWriteAt state actions result profile offset secondIndex secondStamp)
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (sameThread : firstStamp.cause.tid = secondStamp.cause.tid) :
    firstIndex < secondIndex ↔ firstStamp.position + 1 < secondStamp.position + 1 := by
  exact (first.order_iff second success sequenced sameThread).trans (by omega)

end EDSL.OS.TSO64.PublishedHistory

#audit_edsl
