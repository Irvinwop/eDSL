/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Drains
import EDSL.OS.TSO64.C23Projection.WriteEvents

/-!
Actual publication positions for entries pending at any cut of a complete
successful scheduler trace. Final quiescence forces a real suffix drain;
sequence integrity makes its managed writer identity unique in the full run.
No publication position, rank, future drain, or origin oracle is an input.

Arbitrary mixed initial FIFOs are allowed. An incoming entry's earlier issue
is not invented. These are finite-trace results, conditional on actual success
and final quiescence, not fairness or eventual completion of every scheduler.
The rank below is the actual publication position plus one, not an issue-time
rank, a pending-own view invariant, or a C23 legality theorem.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86 PublishedHistory

/-- Every exact pending entry at a real cut drains in the actual remaining
suffix if the full run ends quiescent. Works for ordinary and managed entries,
without an initial emptiness or numerical-integrity premise. -/
theorem queued_future_drain {state before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {cut tid : Nat}
    {entry : Pending}
    (success : schedule state actions profile = .ok result)
    (prefixRun : schedule state (actions.take cut) profile = .ok (before, result.2.take cut))
    (empty : Quiescent result.1) (pending : Queued before tid entry) :
    ∃ index, cut ≤ index ∧ result.2[index]? = some (.drained tid entry) := by
  have suffixRun := (ScheduleTrace.suffix success prefixRun).2
  rcases schedule_pending_retained_or_drained suffixRun pending with retained | drained
  · obtain ⟨worker, live, member⟩ := retained
    have absent := empty worker (List.mem_of_getElem? live)
    rw [absent] at member
    cases member
  · obtain ⟨localIndex, selected⟩ := List.mem_iff_getElem?.mp drained
    refine ⟨cut + localIndex, Nat.le_add_right cut localIndex, ?_⟩
    simpa only [List.getElem?_drop] using selected

/-- An exact managed writer pending at a real cut, with its actual unique
publication. The complete execution and cut origin are retained; this record
cannot be assembled from a desired final RAM word or timestamp alone. -/
structure PendingPublication (state : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (cut tid : Nat)
    (reference : Queue.ManagedRef) (value : Word) (occurrence : Nat) where
  execution : schedule state actions profile = .ok result
  pendingAtCut : ∃ before,
    schedule state (actions.take cut) profile = .ok (before, result.2.take cut) ∧
      Queued before tid (.managed reference value occurrence)
  index : Nat
  future : cut ≤ index
  observed : result.2[index]? = some (.drained tid (.managed reference value occurrence))
  unique : ∀ otherIndex otherReference otherValue,
    result.2[otherIndex]? = some (.drained tid (.managed otherReference otherValue occurrence)) →
      otherIndex = index ∧ otherReference = reference ∧ otherValue = value

/-- Construct all future-position and identity facts from the successful run,
its actual pending entry and the final empty queues. No desired future result
or view-order inequality is an admission premise. -/
theorem pending_managed_publication {state before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {cut tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (success : schedule state actions profile = .ok result)
    (sequenced : Sequenced state)
    (prefixRun : schedule state (actions.take cut) profile = .ok (before, result.2.take cut))
    (empty : Quiescent result.1)
    (pending : Queued before tid (.managed reference value occurrence)) :
    Nonempty (PendingPublication state actions result profile cut tid reference value occurrence) := by
  obtain ⟨index, future, observed⟩ := queued_future_drain success prefixRun empty pending
  exact ⟨{
    execution := success
    pendingAtCut := ⟨before, prefixRun, pending⟩
    index := index
    future := future
    observed := observed
    unique := fun _ _ _ other => managed_drain_identity_unique success sequenced other observed }⟩

namespace PendingPublication
variable {state : State} {actions : List Action} {result : State × List Observation}
  {profile : Profile} {cut tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}

/-- The full actual buffered cause, retaining the original reference and word.
The position counts every observation from the supplied offset. -/
def stamp (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    (offset : Nat) : Stamp :=
  ⟨offset + publication.index, .buffered tid reference value occurrence⟩

/-- Zero is reserved for the initialized boundary by the graph layer. A pending
writer's position is its later publication, not the earlier store issue. -/
def rank (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    (offset : Nat) : Nat := (publication.stamp offset).position + 1

theorem rank_after_cut
    (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    (offset : Nat) : offset + cut < publication.rank offset := by
  have bound := publication.future
  simp only [rank, stamp]
  omega

/-- Actual prefix, selected action and successful publication step behind the
chosen stamp. No writer is recovered by searching for an equal payload. -/
theorem writeAt
    (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    (offset : Nat) : Nonempty (WriteAt state actions result profile offset (publication.stamp offset)) := by
  obtain ⟨before, action, after, prefixRun, selected, stepped⟩ :=
    ScheduleTrace.observation_at publication.execution publication.observed
  exact ⟨⟨publication.index, .drained tid (.managed reference value occurrence),
    before, action, after, rfl, publication.observed, prefixRun, selected, stepped, rfl⟩⟩

/-- The chosen full stamp belongs to the production complete write enumeration.
This connects the rank bound to real graph inputs, not an auxiliary clock. -/
theorem stamp_mem_writes
    (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    (offset : Nat) : publication.stamp offset ∈ C23Projection.writes offset result.2 := by
  obtain ⟨origin⟩ := publication.writeAt offset
  exact C23Projection.writeAt_mem_writes origin

/-- A retained pending identity was not already published at an earlier cut.
Any such observation would contradict its unique actual future drain. -/
theorem no_past_drain
    (publication : PendingPublication state actions result profile cut tid reference value occurrence)
    {index : Nat} (earlier : index < cut) (otherReference : Queue.ManagedRef) (otherValue : Word) :
    result.2[index]? ≠ some (.drained tid (.managed otherReference otherValue occurrence)) := by
  intro observed
  have same := (publication.unique index otherReference otherValue observed).1
  have bound := publication.future
  omega

/-- Different cut witnesses for the same thread/occurrence retain exactly one
publication, reference and word. Logical invocation labels play no role. -/
theorem same_occurrence
    (first : PendingPublication state actions result profile cut tid reference value occurrence)
    {otherCut : Nat} {otherReference : Queue.ManagedRef} {otherValue : Word}
    (second : PendingPublication state actions result profile otherCut tid otherReference otherValue occurrence) :
    second.index = first.index ∧ otherReference = reference ∧ otherValue = value :=
  first.unique second.index otherReference otherValue second.observed

end PendingPublication
end EDSL.OS.TSO64.StoreHistory

#audit_edsl
