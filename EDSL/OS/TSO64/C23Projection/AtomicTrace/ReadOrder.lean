/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadRanks
import EDSL.OS.TSO64.ExecutionViews.PublicationCovers
import EDSL.OS.TSO64.ExecutionViews.Monotone

/-!
Instruction order recovered from the exact writer of an actual managed load.
A forwarded source retains its own worker and occurrence; monotonicity of the
actual issue counter puts that writer's real instruction before the load.
A published source retains a real publication in the load's prestate prefix.
Its graph key identifies the complete publication, independently of its word.

The incoming publication map is empty, while incoming mixed queues may be
nonempty. An initial queued writer has no invented issue origin: the conclusion
requires an independently witnessed instruction write in this run. This module
does not establish source-language ordering, C23 legality, synchronization,
fairness or native refinement.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

/-- A real managed issue whose occurrence is already below a worker's counter
must precede that actual cut. The reverse interval would make the issue's
allocating prestate counter at least the cut's counter, a contradiction. -/
theorem IssuedAt.index_lt_of_counter_lt {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {instructionIndex cut tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      instructionIndex initial actions result)
    (snapshot : ExecutionViews.Cut initial actions result profile cut tid)
    (below : occurrence < snapshot.worker.nextStore) : instructionIndex < cut := by
  by_cases ordered : cut ≤ instructionIndex
  · obtain ⟨before, action, first, prefixRun, _actionAt, _stepped, actual⟩ := issued.prestate
    obtain ⟨prior, priorLive, allocated⟩ := actual.managed_occurrence
    let issueCut : ExecutionViews.Cut initial actions result profile instructionIndex tid :=
      ⟨before, prior, prefixRun, priorLive⟩
    have counters := schedule_nextStore_le (snapshot.interval issueCut ordered)
      snapshot.live issueCut.live
    change snapshot.worker.nextStore ≤ prior.nextStore at counters
    omega
  · omega

end EDSL.OS.TSO64.StoreHistory

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86 PublishedHistory StoreHistory

/-- A scanned store event retains the exact indexed managed issue. Forget
only its access annotation; preserve the actual scheduler step and suffix.
Clients need no new induction over their program to construct a write witness. -/
theorem EventAt.store_issued {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {position tid occurrence index offset : Nat} {target : Queue.ManagedRef} {value : Word}
    {incoming : Writers}
    (actual : EventAt profile ⟨position, tid, .store target value occurrence⟩
      index initial actions result offset incoming) :
    IssuedAt profile tid (.managed target value occurrence) index initial actions result := by
  induction actual with
  | head stepped following access =>
      cases access with
      | store issued => exact .head stepped following issued
  | later stepped following _actual ih => exact .later stepped following ih

/-- A real load reading an independently witnessed instruction writer follows
that writer's instruction. If the writer belongs to a different thread, the
load also follows its actual publication. Own forwarding need not wait for a
publication and therefore keeps the two conclusions separate. -/
theorem LoadSource.write_order {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {cut tid offset writeIndex : Nat} {worker : Worker} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (prefixRun : schedule initial (actions.take cut) profile =
      .ok (before, result.2.take cut))
    (live : before.workers[tid]? = some worker)
    (read : LoadSource before worker tid target value
      (after offset (result.2.take cut) empty) source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp) :
    writeIndex < cut ∧ (stamp.cause.tid ≠ tid → written.publication.index < cut) := by
  cases read with
  | forwarded selector writer occurrence _newest _entry _payload _address _current below =>
      cases stamp with
      | mk position cause =>
        cases cause with
        | buffered writerTid reference writtenValue writerOccurrence =>
            change WriterId.store tid occurrence = .store writerTid writerOccurrence at readFrom
            obtain ⟨sameThread, sameOccurrence⟩ := WriterId.store.inj readFrom
            subst writerTid
            subst writerOccurrence
            let snapshot : ExecutionViews.Cut initial actions result profile cut tid :=
              ⟨before, worker, prefixRun, live⟩
            have earlier := written.actual.index_lt_of_counter_lt snapshot below
            refine ⟨earlier, ?_⟩
            intro different
            exact False.elim (different rfl)
        | rmw writerTid event => cases readFrom
  | published _absent _loaded =>
      cases found : after offset (result.2.take cut) empty target.handle.cell with
      | none =>
          simp only [publishedSource, found] at readFrom
          cases stamp with
          | mk position cause => cases cause <;> cases readFrom
      | some latest =>
          obtain ⟨past, _cell, _noLater⟩ := newest_write_at prefixRun found
          obtain ⟨full⟩ := past.lift_prefix execution.success
          have selectedKey :
              publishedSource (after offset (result.2.take cut) empty) target.handle.cell =
                Graph.publicationKey latest := by
            simp only [publishedSource, found, Graph.publicationKey]
            cases latest.cause <;> rfl
          have sameKey : Graph.publicationKey latest = Graph.publicationKey stamp :=
            selectedKey.symm.trans readFrom
          have sameStamp := publicationKey_writeAt_unique execution.success execution.sequenced
            full written.publication sameKey
          have pastBefore : past.index < cut :=
            Nat.lt_of_lt_of_le (List.getElem_of_getElem? past.observed).1
              (List.length_take_le _ _)
          have samePosition := congrArg Stamp.position sameStamp
          have pastPosition := past.position
          have writtenPosition := written.publication.position
          have publishedBefore : written.publication.index < cut := by omega
          exact ⟨Nat.lt_of_le_of_lt (written.index_le_publication execution.sequenced)
            publishedBefore, fun _different => publishedBefore⟩

/-- An actual annotated load supplies its own successful prestate and exact
read source. Equality with an actual instruction writer's graph key therefore
recovers instruction order, and cross-thread sources have already published.
No source-rank, issue-order or publication-position premise is supplied. -/
theorem EventAt.load_write_order {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {accessIndex offset writeIndex : Nat} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId} {stamp : Stamp}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event accessIndex initial actions result offset empty)
    (loaded : event.access = .load target value source)
    (written : InstructionWriteAt initial actions result profile offset writeIndex stamp)
    (readFrom : source = Graph.publicationKey stamp) :
    writeIndex < accessIndex ∧
      (stamp.cause.tid ≠ event.tid → written.publication.index < accessIndex) := by
  obtain ⟨before, action, first, prefixRun, _actionAt, _observed, _stepped, access⟩ :=
    actual.prestate
  cases access with
  | load _origin live read =>
      cases loaded
      exact read.write_order execution prefixRun live written readFrom
  | store => cases loaded
  | rmw => cases loaded

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
