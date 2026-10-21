/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Drains
import EDSL.OS.TSO64.PublishedHistory

/-!
Per-worker managed publication order for arbitrary successful schedules.
The numerical initial FIFO invariant permits nonempty queues. Actual suffix
origins distinguish retained initial entries from later actual issues; they
do not assign invented issue events to the initial boundary.

Occurrences order actual issues and actual managed drains independently of
their references, cells and words. Ordinary entries may consume intervening
counter values. Buffered `WriteAt` stamps retain the complete cause and use
their actual observation positions, with a common arbitrary stream offset.
These are finite scheduler contracts, not a source-language legality or
happens-before construction.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

-- The corresponding helper in Drains is private. Extract only the actual
-- head/tail effect needed here, without introducing another execution model.
private theorem order_drained_step_effect {state after : State} {action : Action}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok (after, .drained tid entry)) :
    ∃ worker tail world,
      state.workers[tid]? = some worker ∧ worker.pending = entry :: tail ∧
      after = install state tid world { worker with pending := tail } := by
  cases step_origin (profile := profile) success with
  | ordinary _live _running _code _caller _fetched effect =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | drained live fifo _gate _changed _effect => exact ⟨_, _, _, live, fifo, rfl⟩

/-- Immediately after an actual managed drain, every retained managed entry
at that same worker has a greater occurrence. The unchanged issue counter is
also strictly greater than the drained occurrence. Neither conclusion depends
on matching references, cells or values, or on the absence of ordinary entries. -/
theorem step_managed_drain_lower {state after : State} {action : Action}
    {profile : Profile} {tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    (sequenced : Sequenced state)
    (success : step state action profile =
      .ok (after, .drained tid (.managed reference value occurrence))) :
    (∀ otherReference otherValue otherOccurrence,
      Queued after tid (.managed otherReference otherValue otherOccurrence) →
        occurrence < otherOccurrence) ∧
    ∃ current, after.workers[tid]? = some current ∧ occurrence < current.nextStore := by
  obtain ⟨worker, tail, world, live, fifo, installed⟩ := order_drained_step_effect success
  have ordered := sequenced worker (List.mem_of_getElem? live)
  change (Queue.occurrences worker.pending).Pairwise (fun first second => first < second) ∧
    (∀ identifier ∈ Queue.occurrences worker.pending, identifier < worker.nextStore) at ordered
  simp only [fifo, Queue.occurrences_managed] at ordered
  let current : Worker := { worker with pending := tail }
  have currentLive : after.workers[tid]? = some current := by
    rw [installed]
    exact List.getElem?_set_self (List.getElem_of_getElem? live).1
  constructor
  · intro otherReference otherValue otherOccurrence queued
    obtain ⟨other, otherLive, member⟩ := queued
    have equal : other = current := Option.some.inj (otherLive.symm.trans currentLive)
    subst other
    exact (List.pairwise_cons.mp ordered.1).1 otherOccurrence
      (Queue.managed_mem_occurrences tail otherReference otherValue otherOccurrence member)
  · exact ⟨current, currentLive, ordered.2 occurrence List.mem_cons_self⟩

/-- Every managed drain in an actual successful suffix is above the first
actual managed drain at the same worker. A suffix entry is derived from the
real prefix execution: either it was retained in the post-drain tail, or an
actual later issue allocated it at least at the post-drain counter. -/
theorem managed_drain_lt_suffix {state after : State} {action : Action}
    {actions : List Action} {result : State × List Observation} {profile : Profile}
    {tid occurrence otherOccurrence index : Nat}
    {reference otherReference : Queue.ManagedRef} {value otherValue : Word}
    (sequenced : Sequenced state)
    (drained : step state action profile =
      .ok (after, .drained tid (.managed reference value occurrence)))
    (success : schedule after actions profile = .ok result)
    (observed : result.2[index]? =
      some (.drained tid (.managed otherReference otherValue otherOccurrence))) :
    occurrence < otherOccurrence := by
  obtain ⟨retained, _current, live, past⟩ := step_managed_drain_lower sequenced drained
  obtain ⟨before, _action, _after, prefixRun, _selected, executed⟩ :=
    ScheduleTrace.observation_at success observed
  obtain ⟨worker, _tail, _world, workerLive, fifo, _installed⟩ :=
    order_drained_step_effect executed
  have queued : Queued before tid (.managed otherReference otherValue otherOccurrence) := by
    refine ⟨worker, workerLive, ?_⟩
    rw [fifo]
    exact List.mem_cons_self
  rcases schedule_pending_origin prefixRun queued with boundary | issued
  · exact retained otherReference otherValue otherOccurrence boundary
  · obtain ⟨_issueIndex, actual⟩ := issued.indexed
    exact Nat.lt_of_lt_of_le past (actual.occurrence_lower live)

/-- Actual managed drain observations at increasing action positions have
strictly increasing occurrences at the same worker. This ranges over all
successful multi-access traces and all managed references and words, including
equal payloads, different cells and arbitrary intervening ordinary entries.
Only the initial numerical FIFO invariant is required. -/
theorem managed_drain_occurrence_lt {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (first : result.2[firstIndex]? =
      some (.drained tid (.managed firstReference firstValue firstOccurrence)))
    (second : result.2[secondIndex]? =
      some (.drained tid (.managed secondReference secondValue secondOccurrence)))
    (positions : firstIndex < secondIndex) : firstOccurrence < secondOccurrence := by
  induction actions generalizing state result firstIndex secondIndex with
  | nil =>
      have same : (state, []) = result := Except.ok.inj success
      subst result
      simp at first
  | cons action rest ih =>
      obtain ⟨head, tail, stepped, following, same⟩ := schedule_cons_ok success
      cases firstIndex with
      | zero =>
          cases secondIndex with
          | zero => omega
          | succ secondIndex =>
              have observed : head.2 =
                  .drained tid (.managed firstReference firstValue firstOccurrence) := by
                simpa only [same, List.getElem?_cons_zero, Option.some.injEq] using first
              have actual : step state action profile =
                  .ok (head.1, .drained tid (.managed firstReference firstValue firstOccurrence)) := by
                rw [← observed]
                exact stepped
              have later : tail.2[secondIndex]? =
                  some (.drained tid (.managed secondReference secondValue secondOccurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using second
              exact managed_drain_lt_suffix sequenced actual following later
      | succ firstIndex =>
          cases secondIndex with
          | zero => omega
          | succ secondIndex =>
              have firstTail : tail.2[firstIndex]? =
                  some (.drained tid (.managed firstReference firstValue firstOccurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using first
              have secondTail : tail.2[secondIndex]? =
                  some (.drained tid (.managed secondReference secondValue secondOccurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using second
              exact ih following (step_sequenced sequenced stepped) firstTail secondTail
                (Nat.lt_of_succ_lt_succ positions)

/-- Occurrence order also recovers the order of the actual drain positions.
Equal positions would force equality of the complete observed entries; the
reverse position order would contradict the forward FIFO theorem. -/
theorem managed_drain_index_lt {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (first : result.2[firstIndex]? =
      some (.drained tid (.managed firstReference firstValue firstOccurrence)))
    (second : result.2[secondIndex]? =
      some (.drained tid (.managed secondReference secondValue secondOccurrence)))
    (occurrences : firstOccurrence < secondOccurrence) : firstIndex < secondIndex := by
  rcases Nat.lt_trichotomy firstIndex secondIndex with forward | same | backward
  · exact forward
  · subst secondIndex
    have sameObservation := Option.some.inj (first.symm.trans second)
    have sameEntry := (Observation.drained.inj sameObservation).2
    cases sameEntry
    omega
  · have reversed := managed_drain_occurrence_lt success sequenced second first backward
    omega

/-- Strict order equivalence for two actual managed publications by one
worker. No distinctness premise is needed: if the occurrence is the same,
`managed_drain_index_unique` already fixes the position and both sides are false. -/
theorem managed_drain_order_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (first : result.2[firstIndex]? =
      some (.drained tid (.managed firstReference firstValue firstOccurrence)))
    (second : result.2[secondIndex]? =
      some (.drained tid (.managed secondReference secondValue secondOccurrence))) :
    firstIndex < secondIndex ↔ firstOccurrence < secondOccurrence :=
  ⟨managed_drain_occurrence_lt success sequenced first second,
    managed_drain_index_lt success sequenced first second⟩

private theorem issue_before_suffix_lt {profile : Profile}
    {tid firstOccurrence secondOccurrence index : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {action : Action} {first : State × Observation} {rest : List Action}
    {tail : State × List Observation}
    (here : Issued state action first profile tid
      (.managed firstReference firstValue firstOccurrence))
    (later : IssuedAt profile tid (.managed secondReference secondValue secondOccurrence)
      index first.1 rest tail) : firstOccurrence < secondOccurrence := by
  obtain ⟨prior, priorLive, allocated⟩ := here.managed_occurrence
  have success : step state action profile = .ok first := by
    cases here with
    | ordinary _issuing success => exact success
  obtain ⟨middle, middleLive⟩ := step_worker_present success priorLive
  have increment := here.nextStore_succ priorLive middleLive
  have lower := later.occurrence_lower middleLive
  omega

/-- Increasing positions of two real managed issues imply increasing
occurrences at the same worker. Actual step determinism and the real counter
increment suffice; neither initial emptiness nor even `Sequenced` is needed. -/
theorem IssuedAt.occurrence_lt_of_index_lt {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {actions : List Action} {result otherResult : State × List Observation}
    (first : IssuedAt profile tid (.managed firstReference firstValue firstOccurrence)
      firstIndex state actions result)
    (second : IssuedAt profile tid (.managed secondReference secondValue secondOccurrence)
      secondIndex state actions otherResult)
    (positions : firstIndex < secondIndex) : firstOccurrence < secondOccurrence := by
  induction first generalizing secondIndex secondOccurrence secondReference secondValue otherResult with
  | head stepped _following actual =>
      cases second with
      | head => omega
      | later steppedSecond _followingSecond actualSecond =>
          have same := Except.ok.inj (stepped.symm.trans steppedSecond)
          cases same
          exact issue_before_suffix_lt actual actualSecond
  | later stepped _following _actual ih =>
      cases second with
      | head => omega
      | later steppedSecond _followingSecond actualSecond =>
          have same := Except.ok.inj (stepped.symm.trans steppedSecond)
          cases same
          exact ih actualSecond (Nat.lt_of_succ_lt_succ positions)

/-- The converse uses the complete issue entry fixed at an equal position,
and the forward actual-counter argument when the positions are reversed. -/
theorem IssuedAt.index_lt_of_occurrence_lt {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {actions : List Action} {result otherResult : State × List Observation}
    (first : IssuedAt profile tid (.managed firstReference firstValue firstOccurrence)
      firstIndex state actions result)
    (second : IssuedAt profile tid (.managed secondReference secondValue secondOccurrence)
      secondIndex state actions otherResult)
    (occurrences : firstOccurrence < secondOccurrence) : firstIndex < secondIndex := by
  rcases Nat.lt_trichotomy firstIndex secondIndex with forward | same | backward
  · exact forward
  · subst secondIndex
    have sameEntry := first.entry_eq second
    cases sameEntry
    omega
  · have reversed := second.occurrence_lt_of_index_lt first backward
    omega

/-- Actual issue positions and managed occurrences have the same strict
order at one worker, even with nonempty or unsequenced initial FIFOs. This
statement concerns actual `IssuedAt` witnesses, not fabricated initial issues. -/
theorem IssuedAt.index_lt_iff_occurrence_lt {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {actions : List Action} {result otherResult : State × List Observation}
    (first : IssuedAt profile tid (.managed firstReference firstValue firstOccurrence)
      firstIndex state actions result)
    (second : IssuedAt profile tid (.managed secondReference secondValue secondOccurrence)
      secondIndex state actions otherResult) :
    firstIndex < secondIndex ↔ firstOccurrence < secondOccurrence :=
  ⟨first.occurrence_lt_of_index_lt second, first.index_lt_of_occurrence_lt second⟩

/-- Two actual issues and their matching actual publications have identical
per-worker strict order. This does not require every issue to publish; when
final queues are empty, the separate Drains existence theorem supplies the
publication witnesses. The complete original reference and word are retained. -/
theorem IssuedAt.managed_publication_order_iff {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIssue secondIssue firstDrain secondDrain : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {actions : List Action} {result : State × List Observation}
    (first : IssuedAt profile tid (.managed firstReference firstValue firstOccurrence)
      firstIssue state actions result)
    (second : IssuedAt profile tid (.managed secondReference secondValue secondOccurrence)
      secondIssue state actions result)
    (sequenced : Sequenced state)
    (firstPublished : result.2[firstDrain]? =
      some (.drained tid (.managed firstReference firstValue firstOccurrence)))
    (secondPublished : result.2[secondDrain]? =
      some (.drained tid (.managed secondReference secondValue secondOccurrence))) :
    firstIssue < secondIssue ↔ firstDrain < secondDrain :=
  (first.index_lt_iff_occurrence_lt second).trans
    (managed_drain_order_iff first.forget.scheduled sequenced firstPublished secondPublished).symm

end EDSL.OS.TSO64.StoreHistory

namespace EDSL.OS.TSO64.PublishedHistory
open X86

-- PublishedHistory's inverse classifier is private; retain the full cause
-- when recovering an actual managed-drain observation from a buffered stamp.
private theorem order_buffered_observation {observation : Observation} {tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (written : writeOf observation = some (.buffered tid reference value occurrence)) :
    observation = .drained tid (.managed reference value occurrence) := by
  cases observation with
  | ordinary => simp [writeOf] at written
  | returned => simp [writeOf] at written
  | blocked => simp [writeOf] at written
  | rmw => simp [writeOf] at written
  | drained actual entry =>
      cases entry with
      | ordinary => simp [writeOf] at written
      | managed other payload number =>
          have same : WriteCause.buffered actual other payload number =
              .buffered tid reference value occurrence := Option.some.inj written
          cases same
          rfl

/-- A real buffered stamp identifies the exact managed drain in the actual
observation stream, including its original worker, reference, word and ID. -/
theorem WriteAt.buffered_observed {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (witness : WriteAt state actions result profile offset
      ⟨position, .buffered tid reference value occurrence⟩) :
    result.2[witness.index]? = some (.drained tid (.managed reference value occurrence)) := by
  have observed := order_buffered_observation witness.written
  simpa only [observed] using witness.observed

/-- An actual managed drain constructs an actual buffered `WriteAt` witness
at `offset + index`. Its prefix, action and step come from scheduler success;
no publication-rank function or final newest-writer-map membership is assumed. -/
theorem managed_drain_writeAt {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset index tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (success : schedule state actions profile = .ok result)
    (observed : result.2[index]? = some (.drained tid (.managed reference value occurrence))) :
    ∃ witness : WriteAt state actions result profile offset
      ⟨offset + index, .buffered tid reference value occurrence⟩, witness.index = index := by
  obtain ⟨before, action, next, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  exact ⟨⟨index, .drained tid (.managed reference value occurrence), before, action, next,
    rfl, observed, prefixRun, actionAt, stepped, rfl⟩, rfl⟩

/-- Buffered publication positions and managed occurrences have the same
strict order for one worker. Both positions are those of actual `WriteAt`
witnesses at the common arbitrary stream offset. References, cells and words
may differ, and equal payloads do not identify the causes. -/
theorem WriteAt.buffered_order_iff {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset tid firstPosition secondPosition firstOccurrence secondOccurrence : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (first : WriteAt state actions result profile offset
      ⟨firstPosition, .buffered tid firstReference firstValue firstOccurrence⟩)
    (second : WriteAt state actions result profile offset
      ⟨secondPosition, .buffered tid secondReference secondValue secondOccurrence⟩)
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state) :
    firstPosition < secondPosition ↔ firstOccurrence < secondOccurrence := by
  have order := StoreHistory.managed_drain_order_iff success sequenced
    first.buffered_observed second.buffered_observed
  have firstAt : firstPosition = offset + first.index := first.position
  have secondAt : secondPosition = offset + second.index := second.position
  constructor
  · intro positions
    exact order.mp (by omega)
  · intro occurrences
    have positions := order.mpr occurrences
    omega

end EDSL.OS.TSO64.PublishedHistory
