/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphHappensBefore
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadTransfer

/-!
Actual views of an arbitrary current managed target transfer through release
membership, synchronization and every nonempty happens-before path of a mapped
scan. The viewed cell may differ from every path endpoint's accessed object.
Real access origins and current authorization construct intermediate domains;
full writer keys authenticate the exact RF instruction and publication.

Declared interface orders remain arbitrary. The execution context retains its
successful finite scan, initial well-formedness/sequencing, final quiescence and
empty incoming publication metadata. Incoming mixed queues remain allowed when
the complete graph mapping admits them; no instruction origin is invented for
an incoming entry. Initial-manifest provenance remains separate. These view
bounds do not assert all HB coherence fields, full C23 legality, source/native
preservation, fairness, graph-construction totality or corpus coverage.
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

private theorem publication_writer {event : Event} {stamp : Stamp}
    (matched : Publication event stamp) :
    event.writer = some (publicationKey stamp) := by
  cases access : event.access with
  | load target value source => simp only [Publication, access] at matched
  | store target value occurrence =>
      have parts : stamp.cause = .buffered event.tid target value occurrence ∧
          event.position < stamp.position := by simpa only [Publication, access] using matched
      simp only [Event.writer, access, publicationKey, parts.1]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [Event.writer, access, publicationKey, parts.1, parts.2]

private theorem writer_at_event (inputs : Inputs) (slot : Fin inputs.events.length) :
    (writerIds inputs)[inputs.initials.length + slot.val]? =
      some (inputs.events[slot.val].writer) := by
  unfold writerIds
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : inputs.initials.length + slot.val - inputs.initials.length = slot.val := by
    omega
  simp only [List.length_map, aligned, List.getElem?_map,
    List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem event_write {inputs : Inputs} {orders : Orders} {table : Table}
    {location : Atomics64.CellId64} {value : Word}
    (mapped : Built inputs orders table) (slot : Fin inputs.events.length)
    (written : Concurrency.C23Atomic.Writes table.toCandidate
      (inputs.initials.length + slot.val) location value) :
    (inputs.events[slot.val].toSource orders).access.writeValue = some value := by
  obtain ⟨node, live, _object, written⟩ := written
  have same := Option.some.inj (live.symm.trans (mapped.event_at slot))
  subst node
  exact written

namespace Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Table}

private theorem same_event_thread
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Fin run.events.length}
    (same : Concurrency.C23Atomic.SameThread table.toCandidate
      (initials.length + first.val) (initials.length + second.val)) :
    run.events[first.val].tid = run.events[second.val].tid := by
  obtain ⟨left, right, leftIndex, rightIndex, threads⟩ := executed.same_thread_events same
  have leftSlot : left = first := Fin.ext (by omega)
  have rightSlot : right = second := Fin.ext (by omega)
  simpa only [leftSlot, rightSlot] using threads

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

/-- Same-thread sequencing transfers any genuine post-instruction view to the
later instruction's prestate. Actual action clocks supply the required cuts. -/
theorem seq_transfers_view
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Fin run.events.length}
    {firstIndex secondIndex earlierRank laterRank : Nat} {target : Queue.ManagedRef}
    (before : Concurrency.C23Atomic.SeqBefore table.toCandidate
      (initials.length + first.val) (initials.length + second.val))
    (firstActual : EventAt profile run.events[first.val] firstIndex initial actions
      run.execution offset empty)
    (secondActual : EventAt profile run.events[second.val] secondIndex initial actions
      run.execution offset empty)
    (earlier : ExecutionViews.At initial actions run.execution profile (firstIndex + 1)
      run.events[first.val].tid target offset empty earlierRank)
    (later : ExecutionViews.At initial actions run.execution profile secondIndex
      run.events[second.val].tid target offset empty laterRank) : earlierRank ≤ laterRank := by
  have clocks := executed.seq_clock_lt before
  rw [executed.event_action_clock first firstActual,
    executed.event_action_clock second secondActual] at clocks
  have cuts : firstIndex + 1 ≤ secondIndex := by omega
  have threads := same_event_thread executed before.2
  have ownEarlier : ExecutionViews.At initial actions run.execution profile (firstIndex + 1)
      run.events[second.val].tid target offset empty earlierRank := by
    simpa only [threads] using earlier
  exact ownEarlier.monotone executed.execution (PublishedOrder.prior_empty offset) cuts later

/-- Release membership transfers every genuine head successor view to a
member's successor view, including other-cell views and foreign RMW members.
Current-domain construction is separate from these supplied genuine views. -/
theorem release_transfers_view
    (executed : Executed initial actions profile offset run initials orders table)
    {head member : Fin run.events.length}
    {headIndex memberIndex earlierRank laterRank : Nat} {target : Queue.ManagedRef}
    (membership : Concurrency.C23Atomic.ReleaseMember table.toCandidate
      (initials.length + head.val) (initials.length + member.val))
    (headActual : EventAt profile run.events[head.val] headIndex initial actions
      run.execution offset empty)
    (memberActual : EventAt profile run.events[member.val] memberIndex initial actions
      run.execution offset empty)
    (earlier : ExecutionViews.At initial actions run.execution profile (headIndex + 1)
      run.events[head.val].tid target offset empty earlierRank)
    (later : ExecutionViews.At initial actions run.execution profile (memberIndex + 1)
      run.events[member.val].tid target offset empty laterRank) : earlierRank ≤ laterRank := by
  obtain ⟨_release, location, headValue, memberValue, headWrite, memberWrite,
    lower, contiguous⟩ := membership
  change table.rank (initials.length + head.val) ≤
    table.rank (initials.length + member.val) at lower
  by_cases sameRank : table.rank (initials.length + head.val) =
      table.rank (initials.length + member.val)
  · have sameRows := executed.mapped.wellFormed.rankUnique _ _ location headValue
      memberValue headWrite memberWrite sameRank
    have sameSlot : head = member := Fin.ext (by omega)
    have sameIndex : headIndex = memberIndex := by
      have headPosition := headActual.position
      have memberPosition := memberActual.position
      rw [sameSlot] at headPosition
      omega
    have alignedEarlier : ExecutionViews.At initial actions run.execution profile (memberIndex + 1)
        run.events[member.val].tid target offset empty earlierRank := by
      simpa only [sameSlot, sameIndex] using earlier
    exact Nat.le_of_eq (alignedEarlier.unique later)
  · have strict : table.rank (initials.length + head.val) <
        table.rank (initials.length + member.val) := by omega
    have clocks := executed.release_clock_le
      (show Concurrency.C23Atomic.ReleaseMember table.toCandidate
        (initials.length + head.val) (initials.length + member.val) from
        ⟨_release, location, headValue, memberValue, headWrite, memberWrite, lower, contiguous⟩)
    rw [executed.event_action_clock head headActual,
      executed.event_action_clock member memberActual] at clocks
    have cuts : headIndex + 1 ≤ memberIndex + 1 := by omega
    rcases contiguous (initials.length + member.val) memberValue memberWrite strict
        (Nat.le_refl _) with same | rmw
    · have threads := same_event_thread executed same
      have ownEarlier : ExecutionViews.At initial actions run.execution profile (headIndex + 1)
          run.events[member.val].tid target offset empty earlierRank := by
        simpa only [threads] using earlier
      exact ownEarlier.monotone executed.execution (PublishedOrder.prior_empty offset) cuts later
    · obtain ⟨writeIndex, stamp, actualHead, matched, ⟨instruction⟩, headRank⟩ :=
        executed.write_rank head (event_write executed.mapped head headWrite)
      have sameIndex : writeIndex = headIndex := by
        have firstPosition := actualHead.position
        have secondPosition := headActual.position
        omega
      have writerView : ExecutionViews.At initial actions run.execution profile (writeIndex + 1)
          stamp.cause.tid target offset empty earlierRank := by
        simpa only [sameIndex, publication_tid matched] using earlier
      have covered := instruction.covers_after executed.execution
        (PublishedOrder.prior_empty offset) writerView
      have memberRank := rmw_clock_eq_rank executed rmw
      rw [executed.event_action_clock member memberActual] at memberRank
      have visible : earlierRank ≤ offset + (memberIndex + 1) := by omega
      exact earlier.le_of_rank_before_cut later (PublishedOrder.prior_empty offset) cuts visible rfl

/-- A synchronizing acquire receives every genuine view after its release
head, through the actual selected release member and exact RF source writer.
Intermediate views use the supplied current target and real worker origins. -/
theorem sw_transfers_view
    (executed : Executed initial actions profile offset run initials orders table)
    {head reader : Fin run.events.length}
    {headIndex readerIndex earlierRank laterRank : Nat}
    {target : Queue.ManagedRef} {resources : Resources}
    (edge : Concurrency.C23Atomic.SynchronizesWith table.toCandidate
      (initials.length + head.val) (initials.length + reader.val))
    (headActual : EventAt profile run.events[head.val] headIndex initial actions
      run.execution offset empty)
    (readerActual : EventAt profile run.events[reader.val] readerIndex initial actions
      run.execution offset empty)
    (current : Queue.Current initial.world resources target)
    (earlier : ExecutionViews.At initial actions run.execution profile (headIndex + 1)
      run.events[head.val].tid target offset empty earlierRank)
    (later : ExecutionViews.At initial actions run.execution profile readerIndex
      run.events[reader.val].tid target offset empty laterRank) : earlierRank ≤ laterRank := by
  obtain ⟨_acquire, writer, source, membership⟩ := edge
  obtain ⟨_location, _headValue, _memberValue, _headWrite, memberWrite, _lower, _contiguous⟩ :=
    membership.2
  rcases executed.writes_cases memberWrite with boundary | actual
  · obtain ⟨slot, aligned, _object, _value, _rank⟩ := boundary
    have clocks := executed.release_clock_le membership
    rw [executed.event_clock head, aligned, executed.initial_clock slot] at clocks
    omega
  · obtain ⟨member, memberRow, _object, stored⟩ := actual
    obtain ⟨memberIndex, stamp, memberActual, matched, ⟨instruction⟩, _rank⟩ :=
      executed.write_rank member stored
    obtain ⟨_worker, _accessTarget, live, _accessCurrent, _related⟩ := memberActual.initial_authority
    obtain ⟨memberRank, ⟨memberView⟩⟩ :=
      ExecutionViews.exists_at executed.execution live (memberIndex + 1) current offset empty
    have memberOf : Concurrency.C23Atomic.ReleaseMember table.toCandidate
        (initials.length + head.val) (initials.length + member.val) := by
      simpa only [memberRow] using membership
    have firstBound := executed.release_transfers_view memberOf headActual memberActual earlier memberView
    obtain ⟨readSlot, readIndex, key, readerRow, actualRead, readAccess, selected⟩ :=
      executed.rf_source source
    have sameSlot : readSlot = reader := Fin.ext (by omega)
    subst readSlot
    have sameIndex : readIndex = readerIndex := by
      have firstPosition := actualRead.position
      have secondPosition := readerActual.position
      omega
    have selectedAt : WriterAt (runInputs initials run offset) key
        (initials.length + member.val) := by
      simpa only [memberRow] using selected
    have keyAt := writer_at_event (runInputs initials run offset) member
    change (writerIds (runInputs initials run offset))[initials.length + member.val]? =
      some run.events[member.val].writer at keyAt
    rw [selectedAt.1, publication_writer matched] at keyAt
    have readFrom : key = publicationKey stamp := Option.some.inj (Option.some.inj keyAt)
    have writerView : ExecutionViews.At initial actions run.execution profile (memberIndex + 1)
        stamp.cause.tid target offset empty memberRank := by
      simpa only [publication_tid matched] using memberView
    have readerView : ExecutionViews.At initial actions run.execution profile readIndex
        run.events[reader.val].tid target offset empty laterRank := by
      simpa only [sameIndex] using later
    have lastBound := actualRead.read_transfers_view executed.execution readAccess instruction
      readFrom writerView readerView
    exact Nat.le_trans firstBound lastBound

/-- Every HB endpoint is an actual event row. Initializers have no thread
and cannot release or acquire, so no edge or path invents an action for them. -/
theorem hb_event_rows
    (executed : Executed initial actions profile offset run initials orders table)
    {i j : Nat}
    (path : EDSL.Concurrency.C23Atomic.HappensBefore table.toCandidate i j) :
    ∃ first second : Fin run.events.length,
      i = initials.length + first.val ∧ j = initials.length + second.val := by
  induction path with
  | sequenced before =>
      obtain ⟨left, right, leftIndex, rightIndex, _threads⟩ :=
        executed.same_thread_events before.2
      exact ⟨left, right, leftIndex, rightIndex⟩
  | synchronizes edge =>
      obtain ⟨acquire, _writer, _source, membership⟩ := edge
      obtain ⟨_headNode, headLive, releases⟩ := membership.1
      rcases executed.row_cases headLive with boundary | actual
      · obtain ⟨_slot, _index, same⟩ := boundary
        rw [same] at releases
        cases releases
      · obtain ⟨first, firstPoint, _headSame⟩ := actual
        obtain ⟨_readNode, readLive, acquires⟩ := acquire
        rcases executed.row_cases readLive with boundary | actual
        · obtain ⟨_slot, _index, same⟩ := boundary
          rw [same] at acquires
          cases acquires
        · obtain ⟨second, secondPoint, _readSame⟩ := actual
          exact ⟨first, second, firstPoint, secondPoint⟩
  | trans _first _second ihFirst ihSecond =>
      obtain ⟨first, _middle, firstPoint, _middlePoint⟩ := ihFirst
      obtain ⟨_middle, second, _middlePoint, secondPoint⟩ := ihSecond
      exact ⟨first, second, firstPoint, secondPoint⟩

private theorem hb_transfers_view_aux
    (executed : Executed initial actions profile offset run initials orders table)
    {firstRow secondRow : Nat}
    (path : Concurrency.C23Atomic.HappensBefore table.toCandidate firstRow secondRow) :
    ∀ (first second : Fin run.events.length)
      (firstIndex secondIndex earlierRank laterRank : Nat)
      (target : Queue.ManagedRef) (resources : Resources),
      firstRow = initials.length + first.val → secondRow = initials.length + second.val →
      EventAt profile run.events[first.val] firstIndex initial actions run.execution offset empty →
      EventAt profile run.events[second.val] secondIndex initial actions run.execution offset empty →
      Queue.Current initial.world resources target →
      ExecutionViews.At initial actions run.execution profile (firstIndex + 1)
        run.events[first.val].tid target offset empty earlierRank →
      ExecutionViews.At initial actions run.execution profile secondIndex
        run.events[second.val].tid target offset empty laterRank → earlierRank ≤ laterRank := by
  induction path with
  | sequenced before =>
      intro first second firstIndex secondIndex earlierRank laterRank target resources
        firstPoint secondPoint firstActual secondActual _current earlier later
      have actualBefore : Concurrency.C23Atomic.SeqBefore table.toCandidate
          (initials.length + first.val) (initials.length + second.val) := by
        simpa only [firstPoint, secondPoint] using before
      exact executed.seq_transfers_view actualBefore firstActual secondActual earlier later
  | synchronizes edge =>
      intro first second firstIndex secondIndex earlierRank laterRank target resources
        firstPoint secondPoint firstActual secondActual current earlier later
      have actualEdge : Concurrency.C23Atomic.SynchronizesWith table.toCandidate
          (initials.length + first.val) (initials.length + second.val) := by
        simpa only [firstPoint, secondPoint] using edge
      exact executed.sw_transfers_view actualEdge firstActual secondActual current earlier later
  | @trans _firstRow _middleRow _lastRow _firstPath secondPath firstIH secondIH =>
      intro first second firstIndex secondIndex earlierRank laterRank target resources
        firstPoint secondPoint firstActual secondActual current earlier later
      obtain ⟨middle, _last, middlePoint, _lastPoint⟩ := executed.hb_event_rows secondPath
      obtain ⟨middleIndex, middleActual⟩ := executed.event_origin middle
      obtain ⟨_worker, _accessTarget, live, _accessCurrent, _related⟩ := middleActual.initial_authority
      obtain ⟨beforeRank, ⟨beforeView⟩⟩ :=
        ExecutionViews.exists_at executed.execution live middleIndex current offset empty
      obtain ⟨afterRank, ⟨afterView⟩⟩ :=
        ExecutionViews.exists_at executed.execution live (middleIndex + 1) current offset empty
      have firstBound := firstIH first middle firstIndex middleIndex earlierRank beforeRank
        target resources firstPoint middlePoint firstActual middleActual current earlier beforeView
      have middleBound := beforeView.step executed.execution (PublishedOrder.prior_empty offset) afterView
      have lastBound := secondIH middle second middleIndex secondIndex afterRank laterRank
        target resources middlePoint secondPoint middleActual secondActual current afterView later
      exact Nat.le_trans firstBound (Nat.le_trans middleBound lastBound)

/-- Every nonempty HB path transfers genuine post-instruction views to its
endpoint's genuine prestate views. The target is arbitrary current authority,
including cells unrelated to either endpoint; all intermediate worker domains
and cut orders come from actual scanned events and the semantic path. -/
theorem hb_transfers_view
    (executed : Executed initial actions profile offset run initials orders table)
    {first second : Fin run.events.length}
    {firstIndex secondIndex earlierRank laterRank : Nat}
    {target : Queue.ManagedRef} {resources : Resources}
    (path : EDSL.Concurrency.C23Atomic.HappensBefore table.toCandidate
      (initials.length + first.val) (initials.length + second.val))
    (firstActual : EventAt profile run.events[first.val] firstIndex initial actions
      run.execution offset empty)
    (secondActual : EventAt profile run.events[second.val] secondIndex initial actions
      run.execution offset empty)
    (current : Queue.Current initial.world resources target)
    (earlier : ExecutionViews.At initial actions run.execution profile (firstIndex + 1)
      run.events[first.val].tid target offset empty earlierRank)
    (later : ExecutionViews.At initial actions run.execution profile secondIndex
      run.events[second.val].tid target offset empty laterRank) : earlierRank ≤ laterRank :=
  hb_transfers_view_aux executed path first second firstIndex secondIndex earlierRank laterRank
    target resources rfl rfl firstActual secondActual current earlier later

end Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
