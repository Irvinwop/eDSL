/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Trace
import EDSL.OS.TSO64.StoreHistory.Drains
import EDSL.OS.TSO64.C23Projection.Origins
import EDSL.OS.TSO64.C23Projection.WriteEvents

/-!
Connect computed store issues and computed managed write observations.
The scanner's success supplies all issue origins; clients do not provide a
history oracle. Empty boundaries and numerical sequencing remain explicit.
These are store-event correspondences, not C23 graph legality or source orders.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection
open X86 StoreHistory PublishedHistory

/-- Empty initial FIFOs establish their numerical sequencing directly. This
does not establish world/resource well-formedness or supply past store issues. -/
theorem quiescent_sequenced {state : State} (empty : Quiescent state) : Sequenced state := by
  intro worker member
  change (Queue.occurrences worker.pending).Pairwise (fun first second => first < second) ∧
    (∀ occurrence ∈ Queue.occurrences worker.pending, occurrence < worker.nextStore)
  rw [empty worker member]
  exact ⟨.nil, fun _ member => by cases member⟩

/-- Every computed managed issue has exactly one later drain in a completed
quiescent run. Its corresponding write stamp is retained by the write-event
enumeration. No issue, publication or value-origin proof is supplied by clients. -/
theorem scan_issue_published_once {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {result : Trace.Result} {issue : Trace.Issue}
    {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat}
    (success : Trace.scan state actions profile offset = .ok result)
    (sequenced : Sequenced state) (empty : Quiescent result.state)
    (member : issue ∈ result.issues) (managed : issue.entry = .managed reference value occurrence) :
    ∃ drainIndex, issue.position < offset + drainIndex ∧
      result.observations[drainIndex]? =
        some (.drained issue.tid (.managed reference value occurrence)) ∧
      (⟨offset + drainIndex, .buffered issue.tid reference value occurrence⟩ : Stamp) ∈
        writes offset result.observations ∧
      ∀ otherIndex otherReference otherValue,
        result.observations[otherIndex]? =
          some (.drained issue.tid (.managed otherReference otherValue occurrence)) →
        otherIndex = drainIndex ∧ otherReference = reference ∧ otherValue = value := by
  obtain ⟨index, position, actual⟩ := Trace.scan_sound success member
  rw [managed] at actual
  obtain ⟨drainIndex, later, observed, unique⟩ :=
    actual.managed_drain_exists_unique sequenced empty
  refine ⟨drainIndex, by omega, observed, ?_, unique⟩
  exact (mem_writes_iff offset result.observations _).mpr
    ⟨drainIndex, .drained issue.tid (.managed reference value occurrence),
      observed, rfl, rfl⟩

/-- Every computed buffered publication resolves to a unique earlier computed
issue with its complete identity. An empty initial boundary excludes arbitrary
pre-run entries; the successful scan supplies the actual full schedule. -/
theorem scan_publication_origin {state : State} {actions : List Action} {profile : Profile}
    {offset position tid occurrence : Nat} {result : Trace.Result}
    {reference : Queue.ManagedRef} {value : Word}
    (success : Trace.scan state actions profile offset = .ok result)
    (empty : Quiescent state)
    (member : (⟨position, .buffered tid reference value occurrence⟩ : Stamp) ∈
      writes offset result.observations) :
    ∃ issue : Trace.Issue, issue ∈ result.issues ∧ issue.tid = tid ∧
      issue.entry = .managed reference value occurrence ∧ issue.position < position ∧
      ∀ other : Trace.Issue, other ∈ result.issues → other.tid = tid →
        other.entry = .managed reference value occurrence → other = issue := by
  have scheduled := Trace.scan_scheduled success
  obtain ⟨witness⟩ := writes_origin scheduled member
  obtain ⟨index, before, actual, unique⟩ := buffered_issue_unique empty scheduled witness
  let issue : Trace.Issue := ⟨offset + index, tid, .managed reference value occurrence⟩
  have issueMember : issue ∈ result.issues := Trace.scan_complete success actual
  refine ⟨issue, issueMember, rfl, rfl, ?_, ?_⟩
  · have publication : position = offset + witness.index := witness.position
    change offset + index < position
    omega
  · intro other otherMember otherTid otherEntry
    obtain ⟨otherIndex, otherPosition, otherActual⟩ := Trace.scan_sound success otherMember
    rw [otherTid, otherEntry] at otherActual
    have sameIndex := unique otherIndex otherActual
    cases other with
    | mk otherPositionValue otherThread otherTag =>
        change otherThread = tid at otherTid
        change otherTag = .managed reference value occurrence at otherEntry
        change otherPositionValue = offset + otherIndex at otherPosition
        subst otherThread
        subst otherTag
        subst otherPositionValue
        rw [sameIndex]

end EDSL.OS.TSO64.C23Projection
