/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64CrossCellFixtures
import tests.AccessSourceRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.PublicationViews

/-!
An admitted load from cell A is followed by a store to separately allocated B.
The first load forwards from the writer's FIFO; the second reads published RAM.
Their independently specified equal source identity and rank are authenticated
by the actual access scan and actual publication, never supplied to execution.

This finite scalar-RAM, long-mode/CET-off example uses stable checked resources.
It establishes numerical coverage, not release/acquire, HB, source-C23 legality,
physical execution or additional compiler-corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.Tests.PublicationCoverageLoads
open X86 OS.TSO64 OS.TSO64.PublishedHistory OS.TSO64.C23Projection.AtomicTrace

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

/-- Bytes 48 89 37; 48 8b 07; 48 8b 07; 48 89 32; c3.
Both loads target A through RDI; the final store targets B through RDX. -/
def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64CrossCellFixtures.start 0x8b48078b48378948 0x000000c332894807 3 5 7 11 0 12

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel
def initial : OS.TSO64.State := checked initialAttempt initial_succeeds
theorem initial_actual : initialAttempt = .ok initial := checked_ok _ _
theorem initial_valid : WellFormed initial .sharedCell :=
  TSO64CrossCellFixtures.start_valid initial_actual

/-- The drain separates the two actual loads, without changing their source
writer. The peer performs only its checked return. -/
def actions : List Action :=
  [.issue 0 false, .issue 0 true, .drain 0, .issue 0 false,
    .issue 0 true, .drain 0, .issue 0 false, .issue 1 true]

def scanAttempt : Except Fault Result := scan initial actions .sharedCell 83 empty
theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel
def scanned : Result := checked scanAttempt scan_succeeds
theorem scanned_actual : scan initial actions .sharedCell 83 empty = .ok scanned :=
  checked_ok _ _
def result : OS.TSO64.State × List Observation := scanned.execution
theorem scheduled : schedule initial actions .sharedCell = .ok result :=
  scan_scheduled scanned_actual

theorem initial_quiescent : Quiescent initial :=
  AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)
theorem initial_sequenced : Sequenced initial := by
  intro worker member
  simp [Worker.storeCursor, Queue.Cursor.Ordered, initial_quiescent worker member]
theorem final_quiescent : Quiescent result.1 :=
  AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)
theorem execution : ExecutionViews.Execution initial actions result .sharedCell :=
  ⟨scheduled, initial_valid, initial_sequenced, final_quiescent⟩

/-- Complete literal authority descriptors, including distinct allocation and
cell identifiers. Equal stored words do not identify either target. -/
def referenceA : Queue.ManagedRef := ⟨⟨0⟩, ⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩
def referenceB : Queue.ManagedRef := ⟨⟨2⟩, ⟨11, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩

theorem different_cells : referenceA.handle.cell ≠ referenceB.handle.cell ∧
    referenceA.cell.ticket.identifier ≠ referenceB.cell.ticket.identifier := by decide

theorem literal_accesses : scanned.events =
    [⟨83, 0, .store referenceA 7 0⟩,
      ⟨84, 0, .load referenceA 7 (.store 0 0)⟩,
      ⟨86, 0, .load referenceA 7 (.store 0 0)⟩,
      ⟨87, 0, .store referenceB 7 1⟩] := by decide +kernel

theorem literal_observations : result.2 =
    [.ordinary 0, .ordinary 0, .drained 0 (.managed referenceA 7 0),
      .ordinary 0, .ordinary 0, .drained 0 (.managed referenceB 7 1),
      .returned 0, .returned 1] := by decide +kernel

/-- The first load sees an unpublished FIFO writer over RAM value three; the
second sees an empty FIFO and published seven. These checks distinguish the
forwarded and published branches independently of the source annotation. -/
def visibility (cut : Nat) : Option (List Pending × Word) := do
  let before ← (schedule initial (actions.take cut) .sharedCell).toOption
  let worker ← before.1.workers[0]?
  let word ← (loadQWord (published before.1.world) 65536).toOption
  return (worker.pending, word)

theorem load_visibility :
    visibility 1 = some ([.managed referenceA 7 0], 3) ∧
    visibility 3 = some ([], 7) := by decide +kernel

private theorem authenticated {event : Event} {index : Nat}
    (member : event ∈ scanned.events) (position : event.position = 83 + index) :
    EventAt .sharedCell event index initial actions result 83 empty :=
  AccessSourceRanks.scanned_at_position initial_valid initial_sequenced scanned_actual member position

theorem forwarded_at : EventAt .sharedCell ⟨84, 0, .load referenceA 7 (.store 0 0)⟩
    1 initial actions result 83 empty := by
  apply authenticated
  · rw [literal_accesses]; simp
  · rfl

theorem published_at : EventAt .sharedCell ⟨86, 0, .load referenceA 7 (.store 0 0)⟩
    3 initial actions result 83 empty := by
  apply authenticated
  · rw [literal_accesses]; simp
  · rfl

private theorem store_issue_of_event {state : OS.TSO64.State} {acts : List Action}
    {out : OS.TSO64.State × List Observation} {profile : Profile}
    {position tid occurrence index offset : Nat} {target : Queue.ManagedRef} {value : Word}
    {incoming : Writers}
    (actual : EventAt profile ⟨position, tid, .store target value occurrence⟩
      index state acts out offset incoming) :
    StoreHistory.IssuedAt profile tid (.managed target value occurrence) index state acts out := by
  induction actual with
  | head stepped following access =>
      cases access with
      | store issued => exact .head stepped following issued
  | later stepped following _actual ih => exact .later stepped following ih

theorem B_issued : StoreHistory.IssuedAt .sharedCell 0 (.managed referenceB 7 1)
    4 initial actions result := by
  apply store_issue_of_event (position := 87) (offset := 83) (incoming := empty)
  apply authenticated
  · rw [literal_accesses]; simp
  · rfl

def BStamp : Stamp := ⟨88, .buffered 0 referenceB 7 1⟩

/-- Real drain observations provide the exact source rank independently of
either loaded word or the scanner's source annotation. -/
theorem source_rank : WriterRank initial actions result .sharedCell 83
    referenceA.handle.cell (.store 0 0) 86 := by
  have observed : result.2[2]? = some (.drained 0 (.managed referenceA 7 0)) := by
    rw [literal_observations]; rfl
  obtain ⟨publication, _index⟩ := managed_drain_writeAt (offset := 83) scheduled observed
  simpa only [Graph.publicationKey, WriteCause.cell, Nat.reduceAdd] using
    (WriterRank.publication publication rfl)

theorem later_write : Nonempty (InstructionWriteAt initial actions result .sharedCell 83 4 BStamp) := by
  have observed : result.2[5]? = some (.drained 0 (.managed referenceB 7 1)) := by
    rw [literal_observations]; rfl
  obtain ⟨publication, _index⟩ := managed_drain_writeAt (offset := 83) scheduled observed
  exact ⟨InstructionWriteAt.buffered B_issued publication⟩

/-- One generic composition discharges both clients. The source rank comes
from actual load provenance; uniqueness aligns it with the literal drain rank. -/
private theorem load_covered {position index : Nat}
    (actual : EventAt .sharedCell ⟨position, 0, .load referenceA 7 (.store 0 0)⟩
      index initial actions result 83 empty) (ordered : index ≤ 4) :
    WriterRank initial actions result .sharedCell 83 referenceA.handle.cell (.store 0 0) 86 ∧
      86 ≤ BStamp.position + 1 ∧
      ∃ rank, Nonempty (ExecutionViews.At initial actions result .sharedCell 5 0
        referenceA 83 empty rank) ∧ rank ≤ BStamp.position + 1 := by
  obtain ⟨written⟩ := later_write
  obtain ⟨rank, ranked, bounded⟩ :=
    actual.load_source_le_write execution rfl written rfl ordered
  have same := WriterRank.unique scheduled initial_sequenced ranked source_rank
  obtain ⟨target, postRank, related, view, postBound⟩ :=
    actual.covered_by_write (cut := 5) execution (PublishedOrder.prior_empty 83)
      written rfl (by omega)
  have targetEq : target = referenceA := related.2
  subst target
  exact ⟨source_rank, by omega, postRank, view, postBound⟩

/-- A load before publication and one after publication both retain A's
source writer while the later B instruction bounds their rank by eighty-nine. -/
theorem forwarded_load_covered :
    WriterRank initial actions result .sharedCell 83 referenceA.handle.cell (.store 0 0) 86 ∧
      86 ≤ BStamp.position + 1 ∧
      ∃ rank, Nonempty (ExecutionViews.At initial actions result .sharedCell 5 0
        referenceA 83 empty rank) ∧ rank ≤ BStamp.position + 1 :=
  load_covered forwarded_at (by decide)

theorem published_load_covered :
    WriterRank initial actions result .sharedCell 83 referenceA.handle.cell (.store 0 0) 86 ∧
      86 ≤ BStamp.position + 1 ∧
      ∃ rank, Nonempty (ExecutionViews.At initial actions result .sharedCell 5 0
        referenceA 83 empty rank) ∧ rank ≤ BStamp.position + 1 :=
  load_covered published_at (by decide)

end EDSL.Tests.PublicationCoverageLoads

#print axioms EDSL.Tests.PublicationCoverageLoads.execution
#print axioms EDSL.Tests.PublicationCoverageLoads.literal_accesses
#print axioms EDSL.Tests.PublicationCoverageLoads.source_rank
#print axioms EDSL.Tests.PublicationCoverageLoads.later_write
#print axioms EDSL.Tests.PublicationCoverageLoads.forwarded_load_covered
#print axioms EDSL.Tests.PublicationCoverageLoads.published_load_covered
#audit_edsl
