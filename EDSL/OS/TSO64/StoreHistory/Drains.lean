/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Indexed
import EDSL.OS.TSO64.StoreHistory.Flow
import EDSL.OS.TSO64.Occurrences
import EDSL.OS.TSO64.ScheduleTrace

/-!
At-most-once managed publication in the actual successful scheduler. Identity
is the pair of scheduler thread and occurrence, independently of the managed
reference and stored value. `Sequenced` supplies FIFO order and counter bounds;
its preservation and counter monotonicity follow the existing step effects.
Nonempty initial FIFOs are permitted and do not imply an earlier issue event.

Final quiescence additionally gives each actual managed issue exactly one
later drain position. These are finite TSO64 scheduler history contracts.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

private theorem drained_step_effect {state after : State} {action : Action}
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

private theorem drained_step_queued {state after : State} {action : Action}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok (after, .drained tid entry)) :
    Queued state tid entry := by
  obtain ⟨worker, _tail, _world, live, fifo, _installed⟩ := drained_step_effect success
  refine ⟨worker, live, ?_⟩
  rw [fifo]
  exact List.mem_cons_self

/-- The actual drain removes its head occurrence from this worker, even when
another reference or value is queried. Strict FIFO ordering excludes the ID
from the remaining tail, and the unchanged counter is already above it. -/
theorem step_managed_drain_removed {state after : State} {action : Action}
    {profile : Profile} {tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    (sequenced : Sequenced state)
    (success : step state action profile =
      .ok (after, .drained tid (.managed reference value occurrence))) :
    (∀ otherReference otherValue,
      ¬ Queued after tid (.managed otherReference otherValue occurrence)) ∧
    ∃ current, after.workers[tid]? = some current ∧ occurrence < current.nextStore := by
  obtain ⟨worker, tail, world, live, fifo, installed⟩ := drained_step_effect success
  have ordered := sequenced worker (List.mem_of_getElem? live)
  change (Queue.occurrences worker.pending).Pairwise (fun first second => first < second) ∧
    (∀ identifier ∈ Queue.occurrences worker.pending, identifier < worker.nextStore) at ordered
  simp only [fifo, Queue.occurrences_managed] at ordered
  have excluded : occurrence ∉ Queue.occurrences tail := by
    intro member
    exact Nat.lt_irrefl occurrence ((List.pairwise_cons.mp ordered.1).1 occurrence member)
  let current : Worker := { worker with pending := tail }
  have currentLive : after.workers[tid]? = some current := by
    rw [installed]
    exact List.getElem?_set_self (List.getElem_of_getElem? live).1
  constructor
  · intro otherReference otherValue queued
    obtain ⟨other, otherLive, member⟩ := queued
    have equal : other = current := Option.some.inj (otherLive.symm.trans currentLive)
    subst other
    exact excluded (Queue.managed_mem_occurrences tail otherReference otherValue occurrence member)
  · exact ⟨current, currentLive, ordered.2 occurrence List.mem_cons_self⟩

private theorem excluded_occurrence_not_drained {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid occurrence index : Nat}
    {reference : Queue.ManagedRef} {value : Word} {prior : Worker}
    (success : schedule state actions profile = .ok result)
    (excluded : ∀ otherReference otherValue,
      ¬ Queued state tid (.managed otherReference otherValue occurrence))
    (live : state.workers[tid]? = some prior) (past : occurrence < prior.nextStore)
    (observed : result.2[index]? = some (.drained tid (.managed reference value occurrence))) :
    False := by
  obtain ⟨_before, _action, _after, prefixRun, _selected, executed⟩ :=
    ScheduleTrace.observation_at success observed
  have queued := drained_step_queued executed
  rcases schedule_pending_origin prefixRun queued with boundary | issued
  · exact excluded reference value boundary
  · obtain ⟨_issueIndex, actual⟩ := issued.indexed
    have lower := actual.occurrence_lower live
    omega

/-- After a real managed drain, no successful suffix can report the same
worker/occurrence again. The suffix origin is derived from actual execution:
the boundary case is excluded by FIFO removal, while a new issue would have
to allocate at least the post-drain counter. Counter monotonicity is supplied
by `IssuedAt.occurrence_lower`, not by an assumed uniqueness history. -/
theorem managed_drain_no_republication {state after : State} {action : Action}
    {actions : List Action} {result : State × List Observation} {profile : Profile}
    {tid occurrence index : Nat} {reference otherReference : Queue.ManagedRef}
    {value otherValue : Word}
    (sequenced : Sequenced state)
    (drained : step state action profile =
      .ok (after, .drained tid (.managed reference value occurrence)))
    (success : schedule after actions profile = .ok result) :
    result.2[index]? ≠ some (.drained tid (.managed otherReference otherValue occurrence)) := by
  obtain ⟨excluded, _current, live, past⟩ := step_managed_drain_removed sequenced drained
  intro observed
  exact excluded_occurrence_not_drained success excluded live past observed

/-- Two actual result observations with the same `(tid, occurrence)` occupy
the same action position. Their references and values may differ in the
premises. Only the initial numerical FIFO invariant is required: initial
emptiness, current authority and a supplied conservation oracle are absent. -/
theorem managed_drain_index_unique {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid occurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (first : result.2[firstIndex]? =
      some (.drained tid (.managed firstReference firstValue occurrence)))
    (second : result.2[secondIndex]? =
      some (.drained tid (.managed secondReference secondValue occurrence))) :
    firstIndex = secondIndex := by
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
          | zero => rfl
          | succ secondIndex =>
              have observed : head.2 = .drained tid (.managed firstReference firstValue occurrence) := by
                simpa only [same, List.getElem?_cons_zero, Option.some.injEq] using first
              have actual : step state action profile =
                  .ok (head.1, .drained tid (.managed firstReference firstValue occurrence)) := by
                rw [← observed]
                exact stepped
              have later : tail.2[secondIndex]? =
                  some (.drained tid (.managed secondReference secondValue occurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using second
              exact False.elim (managed_drain_no_republication sequenced actual following later)
      | succ firstIndex =>
          cases secondIndex with
          | zero =>
              have observed : head.2 = .drained tid (.managed secondReference secondValue occurrence) := by
                simpa only [same, List.getElem?_cons_zero, Option.some.injEq] using second
              have actual : step state action profile =
                  .ok (head.1, .drained tid (.managed secondReference secondValue occurrence)) := by
                rw [← observed]
                exact stepped
              have later : tail.2[firstIndex]? =
                  some (.drained tid (.managed firstReference firstValue occurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using first
              exact False.elim (managed_drain_no_republication sequenced actual following later)
          | succ secondIndex =>
              have firstTail : tail.2[firstIndex]? =
                  some (.drained tid (.managed firstReference firstValue occurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using first
              have secondTail : tail.2[secondIndex]? =
                  some (.drained tid (.managed secondReference secondValue occurrence)) := by
                simpa only [same, List.getElem?_cons_succ] using second
              exact congrArg Nat.succ
                (ih following (step_sequenced sequenced stepped) firstTail secondTail)

/-- The unique drain position also fixes the complete managed entry. Equal
payloads are not used to identify either position or writer. -/
theorem managed_drain_identity_unique {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid occurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (first : result.2[firstIndex]? =
      some (.drained tid (.managed firstReference firstValue occurrence)))
    (second : result.2[secondIndex]? =
      some (.drained tid (.managed secondReference secondValue occurrence))) :
    firstIndex = secondIndex ∧ firstReference = secondReference ∧ firstValue = secondValue := by
  have sameIndex := managed_drain_index_unique success sequenced first second
  subst secondIndex
  have sameObservation := Option.some.inj (first.symm.trans second)
  have sameEntry := (Observation.drained.inj sameObservation).2
  cases sameEntry
  exact ⟨rfl, rfl, rfl⟩

/-- Every actual issue has an exact drain strictly after its issue position
when the final queues are empty. This forward-flow result applies to ordinary
entries as well and needs no initial queue ordering or empty boundary. -/
theorem IssuedAt.drain_after_of_quiescent {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid index : Nat} {entry : Pending}
    (issued : IssuedAt profile tid entry index state actions result)
    (empty : Quiescent result.1) :
    ∃ drainIndex, index < drainIndex ∧ result.2[drainIndex]? = some (.drained tid entry) := by
  induction issued with
  | head _stepped following actual =>
      rcases schedule_pending_retained_or_drained following actual.queued with pending | published
      · obtain ⟨worker, live, member⟩ := pending
        have none := empty worker (List.mem_of_getElem? live)
        rw [none] at member
        cases member
      · obtain ⟨drainIndex, observed⟩ := List.mem_iff_getElem?.mp published
        exact ⟨drainIndex + 1, Nat.zero_lt_succ drainIndex, observed⟩
  | later _stepped _following _actual ih =>
      obtain ⟨drainIndex, later, observed⟩ := ih empty
      exact ⟨drainIndex + 1, Nat.succ_lt_succ later, observed⟩

/-- An actual managed issue has exactly one later drain position under final
quiescence. Uniqueness ranges over every reference and value at the original
worker/occurrence and also recovers their exact equality. A nonempty sequenced
initial boundary is allowed; no fairness or future-success premise is used. -/
theorem IssuedAt.managed_drain_exists_unique {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid occurrence index : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence) index state actions result)
    (sequenced : Sequenced state) (empty : Quiescent result.1) :
    ∃ drainIndex, index < drainIndex ∧
      result.2[drainIndex]? = some (.drained tid (.managed reference value occurrence)) ∧
      ∀ otherIndex otherReference otherValue,
        result.2[otherIndex]? =
          some (.drained tid (.managed otherReference otherValue occurrence)) →
        otherIndex = drainIndex ∧ otherReference = reference ∧ otherValue = value := by
  obtain ⟨drainIndex, later, observed⟩ := issued.drain_after_of_quiescent empty
  refine ⟨drainIndex, later, observed, ?_⟩
  intro otherIndex otherReference otherValue other
  exact managed_drain_identity_unique issued.forget.scheduled sequenced other observed

end EDSL.OS.TSO64.StoreHistory
