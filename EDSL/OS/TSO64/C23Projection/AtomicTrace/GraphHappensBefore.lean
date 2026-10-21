/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphActionOrder
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphWellFormed

/-!
Actual action clocks for release membership, synchronization and every nonempty
happens-before path of a structurally mapped finite scan. Distinct release
members are same-thread writes or RMWs; real instruction/publication order
therefore makes their clocks follow the head's clock. The exact selected RF
writer then places every synchronizing acquire strictly after its head.

Declared interface orders remain arbitrary. The execution context supplies
real origins, initial well-formedness/sequencing and final quiescence; incoming
publication metadata is empty. Incoming mixed queues remain permitted when the
complete graph mapping admits them, without inventing instruction origins.
Initialization provenance remains separate. These results prove HB acyclicity
and no-future RF, not the four HB coherence obligations, full C23 legality,
source/native preservation, fairness or graph-construction totality.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86 PublishedHistory

private theorem publication_tid {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) : stamp.cause.tid = event.tid := by
  cases access : event.access with
  | load target value source => simp only [Publication, access] at matched
  | store target value occurrence =>
      have parts : stamp.cause = .buffered event.tid target value occurrence ∧
          event.position < stamp.position := by simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.tid]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [parts.1, WriteCause.tid]

private theorem event_write {inputs : Inputs} {orders : Orders} {table : Table}
    {location : Atomics64.CellId64} {value : Word}
    (mapped : Built inputs orders table) (slot : Fin inputs.events.length)
    (written : Concurrency.C23Atomic.Writes table.toCandidate
      (inputs.initials.length + slot.val) location value) :
    inputs.events[slot.val].object = location ∧
      (inputs.events[slot.val].toSource orders).access.writeValue = some value := by
  obtain ⟨node, live, object, written⟩ := written
  have same := Option.some.inj (live.symm.trans (mapped.event_at slot))
  subst node
  exact ⟨object, written⟩

namespace Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Table}

/-- Actual instructions precede their publications; initializers have clock
zero. This bound does not identify instruction clocks with write ranks. -/
private theorem write_clock_le_rank
    (executed : Executed initial actions profile offset run initials orders table)
    {index : Nat} {location : Atomics64.CellId64} {value : Word}
    (written : Concurrency.C23Atomic.Writes table.toCandidate index location value) :
    actionClock initials run index ≤ table.rank index := by
  rcases executed.writes_cases written with boundary | actual
  · obtain ⟨slot, aligned, _object, _value, _rank⟩ := boundary
    rw [aligned, executed.initial_clock slot]
    exact Nat.zero_le _
  · obtain ⟨slot, aligned, _object, stored⟩ := actual
    obtain ⟨_actionIndex, _stamp, actualWrite, _matched, ⟨instruction⟩, ranked⟩ :=
      executed.write_rank slot stored
    have instructionBefore := instruction.index_le_publication executed.sequenced
    have eventPosition := actualWrite.position
    have publicationPosition := instruction.publication.position
    rw [aligned, executed.event_clock slot, ranked]
    omega

/-- An actual RMW's publication occurs at its own instruction action. -/
private theorem rmw_clock_eq_rank
    (executed : Executed initial actions profile offset run initials orders table)
    {index : Nat} (rmw : Concurrency.C23Atomic.IsRMW table.toCandidate index) :
    actionClock initials run index = table.rank index := by
  obtain ⟨node, live, isRMW⟩ := rmw
  rcases executed.row_cases live with boundary | actual
  · obtain ⟨_slot, _aligned, same⟩ := boundary
    rw [same] at isRMW
    cases isRMW
  · obtain ⟨slot, aligned, same⟩ := actual
    rw [same] at isRMW
    cases access : run.events[slot.val].access with
    | load target value source =>
        simp only [Event.toSource, access, Concurrency.C23Atomic.Access.isRMW,
          Bool.false_eq_true] at isRMW
    | store target value occurrence =>
        simp only [Event.toSource, access, Concurrency.C23Atomic.Access.isRMW,
          Bool.false_eq_true] at isRMW
    | rmw changed source =>
        obtain ⟨_publication, _cause, position, stored⟩ := executed.mapped.rmw_rank slot access
        have ranked : table.rank (initials.length + slot.val) =
            run.events[slot.val].position + 1 := by
          have storedAt : table.ranks[initials.length + slot.val]? =
              some (run.events[slot.val].position + 1) := by
            simp only [runInputs] at stored position
            rw [position] at stored
            exact stored
          simp only [Concurrency.C23Atomic.Check.Table.rank, storedAt, Option.getD_some]
        rw [aligned, executed.event_clock slot, ranked]

/-- Invert actual same-thread write publication order to recover instruction
order. Both real write witnesses, not a supplied rank/order oracle, come from
the mapped scan; the rank comparison is the release-member bound. -/
private theorem same_thread_write_clock_lt
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Nat} {location : Atomics64.CellId64} {a b : Word}
    (firstWrite : Concurrency.C23Atomic.Writes table.toCandidate first location a)
    (secondWrite : Concurrency.C23Atomic.Writes table.toCandidate second location b)
    (same : Concurrency.C23Atomic.SameThread table.toCandidate first second)
    (before : table.rank first < table.rank second) :
    actionClock initials run first < actionClock initials run second := by
  obtain ⟨left, right, leftIndex, rightIndex, sameThread⟩ := executed.same_thread_events same
  have firstWritten : Concurrency.C23Atomic.Writes table.toCandidate
      (initials.length + left.val) location a := by
    simpa only [leftIndex] using firstWrite
  have secondWritten : Concurrency.C23Atomic.Writes table.toCandidate
      (initials.length + right.val) location b := by
    simpa only [rightIndex] using secondWrite
  obtain ⟨firstAction, firstStamp, firstActual, firstMatched, ⟨firstInstruction⟩, firstRank⟩ :=
    executed.write_rank left (event_write executed.mapped left firstWritten).2
  obtain ⟨secondAction, secondStamp, secondActual, secondMatched, ⟨secondInstruction⟩, secondRank⟩ :=
    executed.write_rank right (event_write executed.mapped right secondWritten).2
  have writers : firstStamp.cause.tid = secondStamp.cause.tid :=
    (publication_tid firstMatched).trans (sameThread.trans (publication_tid secondMatched).symm)
  have ranked : firstStamp.position + 1 < secondStamp.position + 1 := by
    simpa only [leftIndex, rightIndex, firstRank, secondRank] using before
  have ordered := (firstInstruction.rank_order_iff secondInstruction
    executed.execution.success executed.sequenced writers).mpr ranked
  rw [leftIndex, rightIndex, executed.event_clock left, executed.event_clock right]
  have firstPosition := firstActual.position
  have secondPosition := secondActual.position
  omega

/-- Release membership never moves backward in actual instruction clocks.
Equal ranks identify the same write on one object through structural uniqueness.
A strict member is either a same-thread write with recovered instruction order
or an RMW whose own instruction is its publication. No predecessor, legality,
checker, view or intended-clock witness is a premise. -/
theorem release_clock_le
    (executed : Executed initial actions profile offset run initials orders table)
    {head member : Nat}
    (membership : Concurrency.C23Atomic.ReleaseMember table.toCandidate head member) :
    actionClock initials run head ≤ actionClock initials run member := by
  obtain ⟨_release, location, headValue, memberValue, headWrite, memberWrite,
    lower, contiguous⟩ := membership
  change table.rank head ≤ table.rank member at lower
  by_cases sameRank : table.rank head = table.rank member
  · have same := executed.mapped.wellFormed.rankUnique head member location headValue
      memberValue headWrite memberWrite sameRank
    exact Nat.le_of_eq (congrArg (actionClock initials run) same)
  · have before : table.rank head < table.rank member := by omega
    rcases contiguous member memberValue memberWrite before (Nat.le_refl _) with same | rmw
    · exact Nat.le_of_lt (same_thread_write_clock_lt executed headWrite memberWrite same before)
    · have headBefore := write_clock_le_rank executed headWrite
      have memberAt := rmw_clock_eq_rank executed rmw
      omega

/-- Every semantic synchronization edge strictly increases the actual action
clock, including own-thread synchronization and RMW acquires. The exact RF
writer and actual release membership supply both parts of the comparison. -/
theorem sw_clock_lt
    (executed : Executed initial actions profile offset run initials orders table)
    {head reader : Nat}
    (edge : Concurrency.C23Atomic.SynchronizesWith table.toCandidate head reader) :
    actionClock initials run head < actionClock initials run reader := by
  obtain ⟨_acquire, writer, source, membership⟩ := edge
  exact Nat.lt_of_le_of_lt (executed.release_clock_le membership) (executed.rf_clock_lt source)

/-- Every nonempty sequencing/synchronization path increases the actual clock.
Clock comparison does not introduce any extra semantic HB edge. -/
theorem hb_clock_lt
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Nat}
    (path : Concurrency.C23Atomic.HappensBefore table.toCandidate first second) :
    actionClock initials run first < actionClock initials run second :=
  path.clock_lt executed.seq_clock_lt executed.sw_clock_lt

/-- Actual sequencing and synchronization admit no happens-before cycle. -/
theorem hb_acyclic
    (executed : Executed initial actions profile offset run initials orders table) :
    ∀ index, ¬ Concurrency.C23Atomic.HappensBefore table.toCandidate index index :=
  Concurrency.C23Atomic.acyclic_of_clock executed.seq_clock_lt executed.sw_clock_lt

/-- An exact selected source cannot lie in its reader's happens-before future.
This does not assume or conclude the separate HB coherence obligations. -/
theorem noFutureHB
    (executed : Executed initial actions profile offset run initials orders table)
    {reader writer : Nat}
    (source : Concurrency.C23Atomic.ReadsFrom table.toCandidate reader writer) :
    ¬ Concurrency.C23Atomic.HappensBefore table.toCandidate reader writer := by
  intro future
  exact Nat.lt_asymm (executed.rf_clock_lt source) (executed.hb_clock_lt future)

end Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
