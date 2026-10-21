/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.Model
import EDSL.OS.TSO64.ExecutionViews.Transport
import EDSL.OS.TSO64.ExecutionViews.QueueSteps
import EDSL.OS.TSO64.StoreHistory.WriteOrder

/-!
Numerical cross-cell publication coverage in one actual finite execution.
Immediately after an instruction write, every target view of its own worker
is bounded by that instruction's actual publication position plus one. The
target may be a different cell with a different managed reference.

Published views are bounded by their actual observation prefix. Pending views
retain the production newest-qword selection and its full actual publication.
A managed issue allocates its prestate counter and increments it exactly once;
the sequenced postcut bounds every selected managed occurrence by that new
occurrence. Actual FIFO publication order, including uniqueness at equal
occurrences, then bounds the selected writer's eventual position. An own RMW
retains an empty FIFO at its actual postcut.

The full execution contract keeps success, initial well-formedness and numerical
sequencing, and final quiescence explicit. Initial mixed FIFOs may be nonempty;
their entries receive no invented instruction origins. Incoming published
metadata needs only the explicit prior-position boundary. This module states
numerical coverage only. It supplies no source-release mapping, complete
happens-before transfer, source legality, fairness, or native refinement.

-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedOrder
open PublishedHistory

/-- Every published-prefix position view is at most that prefix's upper
position boundary. Incoming stamps need no execution origin. -/
theorem prefix_view_le_cut {offset cut : Nat} {observations : List Observation}
    {incoming : Writers} (prior : Prior offset incoming)
    (target : Atomics64.CellId64) :
    view (after offset (observations.take cut) incoming) target ≤ offset + cut := by
  cases found : after offset (observations.take cut) incoming target with
  | none =>
      simp only [view, found]
      exact Nat.zero_le _
  | some latest =>
      have past := prior_after (observations := observations.take cut) prior target latest found
      have bounded : (observations.take cut).length ≤ cut := List.length_take_le _ _
      simp only [view, found]
      omega

end EDSL.OS.TSO64.PublishedOrder

namespace EDSL.OS.TSO64.ExecutionViews
open X86 StoreHistory

/-- Identify an independently described successor cut with the actual next
state of a specified real prefix step. The singleton interval comes from
successful scheduling, without a caller-supplied poststate equality. -/
theorem Cut.state_after_step {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid : Nat}
    {action : Action} {first : State × Observation}
    (snapshot : Cut initial actions result profile (index + 1) tid)
    (prefixRun : schedule initial (actions.take index) profile =
      .ok (before, result.2.take index))
    (actionAt : actions[index]? = some action)
    (stepped : step before action profile = .ok first) :
    snapshot.state = first.1 := by
  have nestedPrefix : schedule initial ((actions.take (index + 1)).take index) profile =
      .ok (before, (result.2.take (index + 1)).take index) := by
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_succ index)] using prefixRun
  have interval := (ScheduleTrace.suffix snapshot.scheduled nestedPrefix).2
  have singleton : (actions.take (index + 1)).drop index = [action] := by
    rw [← List.take_drop]
    simp only [List.take_one, List.head?_drop, actionAt, Option.toList]
  rw [singleton] at interval
  have actual : schedule before [action] profile = .ok (first.1, [first.2]) := by
    simp only [schedule, stepped, ok_bind, pure_ok]
  have same : (first.1, [first.2]) =
      (snapshot.state, (result.2.take (index + 1)).drop index) :=
    Except.ok.inj (actual.symm.trans interval)
  exact (congrArg Prod.fst same).symm

/-- The own-empty gate of a real RMW also holds at an independently supplied
actual successor cut. The existing worker-origin and queue-step APIs recover
both real endpoints; no instruction-specific effect analysis is repeated. -/
theorem Cut.pending_empty_of_rmw {initial before next : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid : Nat}
    {action : Action} {event : Atomics64.FetchAddEvent}
    (snapshot : Cut initial actions result profile (index + 1) tid)
    (prefixRun : schedule initial (actions.take index) profile =
      .ok (before, result.2.take index))
    (actionAt : actions[index]? = some action)
    (stepped : step before action profile = .ok (next, .rmw tid event)) :
    snapshot.worker.pending = [] := by
  have stateEq : snapshot.state = next := snapshot.state_after_step prefixRun actionAt stepped
  have currentLive : next.workers[tid]? = some snapshot.worker := by
    rw [← stateEq]
    exact snapshot.live
  have singletonRun : schedule before [action] profile = .ok (next, [.rmw tid event]) := by
    simp only [schedule, stepped, ok_bind, pure_ok]
  obtain ⟨prior, priorLive, _resources⟩ := schedule_worker_origin singletonRun currentLive
  exact (QueueSteps.step_own_rmw_empty stepped priorLive currentLive).2.1

end EDSL.OS.TSO64.ExecutionViews

namespace EDSL.OS.TSO64.StoreHistory
open X86

/-- A real managed allocation fixes the worker counter at every independent
description of its immediate successor cut. Allocation is recovered from the
actual admission, rather than inferred from a queue bound. -/
theorem IssuedAt.nextStore_at_succ {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {instructionIndex tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      instructionIndex initial actions result)
    (snapshot : ExecutionViews.Cut initial actions result profile (instructionIndex + 1) tid) :
    snapshot.worker.nextStore = occurrence + 1 := by
  obtain ⟨before, action, first, prefixRun, actionAt, stepped, actual⟩ := issued.prestate
  have stateEq := snapshot.state_after_step prefixRun actionAt stepped
  obtain ⟨prior, priorLive, allocated⟩ := actual.managed_occurrence
  have currentLive : first.1.workers[tid]? = some snapshot.worker := by
    rw [← stateEq]
    exact snapshot.live
  have increment := actual.nextStore_succ priorLive currentLive
  omega

/-- Nonstrict occurrence order gives nonstrict order of actual managed drain
positions. Equality uses real drain identity uniqueness, with no requirement
that the references, cells or words agree in the premises. -/
theorem managed_drain_index_le {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid firstOccurrence secondOccurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    (success : schedule initial actions profile = .ok result) (sequenced : Sequenced initial)
    (first : result.2[firstIndex]? =
      some (.drained tid (.managed firstReference firstValue firstOccurrence)))
    (second : result.2[secondIndex]? =
      some (.drained tid (.managed secondReference secondValue secondOccurrence)))
    (occurrences : firstOccurrence ≤ secondOccurrence) : firstIndex ≤ secondIndex := by
  by_cases strict : firstOccurrence < secondOccurrence
  · exact Nat.le_of_lt (managed_drain_index_lt success sequenced first second strict)
  · have same : firstOccurrence = secondOccurrence := by omega
    subst secondOccurrence
    exact Nat.le_of_eq (managed_drain_identity_unique success sequenced first second).1

end EDSL.OS.TSO64.StoreHistory

namespace EDSL.OS.TSO64.PublishedHistory
open X86 StoreHistory

/-- Every actual instruction write is no later than its actual publication.
A buffered issue is strictly earlier; an RMW uses its exact action position. -/
theorem InstructionWriteAt.index_le_publication {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset instructionIndex : Nat} {stamp : Stamp}
    (actual : InstructionWriteAt initial actions result profile offset instructionIndex stamp)
    (sequenced : Sequenced initial) : instructionIndex ≤ actual.publication.index := by
  cases stamp with
  | mk position cause =>
      cases cause with
      | buffered tid reference value occurrence =>
          exact Nat.le_of_lt (actual.actual.index_lt_managed_drain sequenced
            actual.publication.buffered_observed)
      | rmw tid event => exact Nat.le_of_eq actual.actual

/-- Every target view of the writing worker immediately after its actual
instruction is covered by that instruction's real publication position plus
one. The target need not be the written cell. All pending identities and
publication indices come from the actual `At` source, including initial FIFO
entries, while the writer retains its real issue or exact RMW position. -/
theorem InstructionWriteAt.covers_after {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset instructionIndex value : Nat} {stamp : Stamp}
    {target : Queue.ManagedRef} {incoming : Writers}
    (execution : ExecutionViews.Execution initial actions result profile)
    (prior : PublishedOrder.Prior offset incoming)
    (actual : InstructionWriteAt initial actions result profile offset instructionIndex stamp)
    (view : ExecutionViews.At initial actions result profile (instructionIndex + 1)
      stamp.cause.tid target offset incoming value) : value ≤ stamp.position + 1 := by
  rcases view with ⟨snapshot, source⟩
  cases source with
  | published _absent =>
      have prefixBound := PublishedOrder.prefix_view_le_cut
        (observations := result.2) (cut := instructionIndex + 1) prior target.handle.cell
      have instructionBound := actual.index_le_publication execution.sequenced
      have position := actual.publication.position
      omega
  | @pending origin selection publication _cell =>
      cases stamp with
      | mk position cause =>
          cases cause with
          | buffered tid reference writtenValue occurrence =>
              have counter := actual.actual.nextStore_at_succ snapshot
              have below := snapshot.worker.storeCursor.managed_occurrence_lt
                (snapshot.ordered execution) selection.reference origin.value selection.occurrence
                (List.mem_of_getElem? selection.selected)
              change selection.occurrence < snapshot.worker.nextStore at below
              have occurrenceBound : selection.occurrence ≤ occurrence := by omega
              have publicationBound := managed_drain_index_le execution.success execution.sequenced
                publication.observed actual.publication.buffered_observed occurrenceBound
              have publishedAt : position = offset + actual.publication.index :=
                actual.publication.position
              change offset + publication.index + 1 ≤ position + 1
              omega
          | rmw tid event =>
              have sameIndex : instructionIndex = actual.publication.index := actual.actual
              have observationEq : actual.publication.observation = .rmw tid event :=
                Option.some.inj (actual.publication.observed.symm.trans actual.publication.rmw_observed)
              have stepped : step actual.publication.before actual.publication.action profile =
                  .ok (actual.publication.next, .rmw tid event) := by
                simpa only [observationEq] using actual.publication.stepped
              have prefixRun : schedule initial (actions.take instructionIndex) profile =
                  .ok (actual.publication.before, result.2.take instructionIndex) := by
                simpa only [← sameIndex] using actual.publication.prefixRun
              have actionAt : actions[instructionIndex]? = some actual.publication.action := by
                simpa only [← sameIndex] using actual.publication.actionAt
              have empty := snapshot.pending_empty_of_rmw prefixRun actionAt stepped
              have member : .managed selection.reference origin.value selection.occurrence ∈
                  snapshot.worker.pending := List.mem_of_getElem? selection.selected
              rw [empty] at member
              cases member

end EDSL.OS.TSO64.PublishedHistory

#audit_edsl
