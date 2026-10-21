/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.AccessGraphRanks
import tests.RMWSourceRanks
import tests.WriteViewRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphCoherence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphWellFormed
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphNoAcquire
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadAccess
import EDSL.Audit

/-!
Integration clients of actual annotated executions and graph
mapping. The equal-word load graph is reused verbatim. The second graph is
computed from `WriteViewRanks.Whole`: A's real store, the zero-delta RMW of B,
and the peer's actual B/A loads. Both initial manifests come from the complete
live registry through `Initials.enumerate`. No desired RF/rank table, legality
proof, replacement execution or per-instruction semantics is an input.

Literal sources, publication ranks, object identities and logical threads are
independent expectations for the computed tables. Generic read-side clients
exercise RMW initialization, an actual source publication separated by a peer
action, and same-worker WR/RR/strict-RW constraints on existing actual writes.
Universal graph sequencing, no-future sequencing and RMW predecessor clients
use production `Executed` methods; structural well-formedness uses `Built`.

These are finite sharedCell scalar-RAM, long-mode/CET-off clients with stable
initialized resources. The declared no-acquire interface has universal finite
atomic-fragment legality. General acquiring interfaces, full C23, native
execution, fairness, graph-build totality and compiler-corpus increments remain
outside these claims.
-/

set_option autoImplicit false

namespace EDSL.Tests.GraphOperationalCoherence
open X86 OS.TSO64 OS.TSO64.C23Projection AtomicTrace

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem get_ok {α : Type} (attempt : Option α)
    (accepted : attempt.isSome = true) : attempt = some (attempt.get accepted) := by
  cases attempt with
  | none => cases accepted
  | some value => rfl

private theorem mapped_run {inputs : Graph.Inputs} {run : AtomicTrace.Result}
    {result : OS.TSO64.State × List Observation}
    {offset : Nat} {initials : List Initials.Entry} {orders : Orders} {table : Graph.Table}
    (mapped : Graph.Built inputs orders table)
    (same : result = run.execution)
    (manifest : inputs.initials = initials) (events : inputs.events = run.events)
    (publications : inputs.writes = writes offset result.2) :
    Graph.Built (Graph.runInputs initials run offset) orders table := by
  cases same
  cases inputs with
  | mk actualInitials actualEvents actualWrites =>
    change actualInitials = initials at manifest
    change actualEvents = run.events at events
    change actualWrites = writes offset run.observations at publications
    cases manifest
    cases events
    cases publications
    exact mapped

private theorem input_manifest (initials : List Initials.Entry) (events : List AtomicTrace.Event)
    (publications : List PublishedHistory.Stamp) :
    (Graph.Inputs.mk initials events publications).initials = initials := rfl

private theorem executed_run {initial : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile} {offset : Nat}
    {run : AtomicTrace.Result} {initials : List Initials.Entry}
    {orders : Orders} {table : Graph.Table}
    (execution : ExecutionViews.Execution initial actions result profile)
    (same : result = run.execution)
    (scanned : scan initial actions profile offset PublishedHistory.empty = .ok run)
    (mapped : Graph.Built (Graph.runInputs initials run offset) orders table) :
    Graph.Executed initial actions profile offset run initials orders table := by
  cases same
  exact ⟨execution.valid, execution.sequenced, scanned, execution.quiescent, mapped⟩

namespace LoadGraph

/-- Reuse the actual equal-word scan and the existing computed graph.
All five premises are execution invariants or structural correspondence. -/
theorem executed : Graph.Executed AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
    .sharedCell 10 AccessSourceRanks.Loads.scanned AccessGraphRanks.manifest
    AccessGraphRanks.interfaceOrders AccessGraphRanks.table := by
  apply executed_run AccessSourceRanks.Loads.execution rfl AccessSourceRanks.Loads.scanned_actual
  exact mapped_run (result := AccessSourceRanks.Loads.result) AccessGraphRanks.built rfl
    (input_manifest AccessGraphRanks.manifest AccessSourceRanks.Loads.scanned.events
      (writes 10 AccessSourceRanks.Loads.result.2)) AccessGraphRanks.events_eq
    AccessGraphRanks.complete_publications

/-- All related graph rows, including both roles of RMWs when present.
This uses the production universal theorem, with no replay of graph pairs. -/
theorem sequenced_coherent :
    Concurrency.C23Atomic.SequencedCoherent AccessGraphRanks.table.toCandidate :=
  executed.sequencedCoherent

theorem no_acquire_annotations :
    AccessGraphRanks.interfaceOrders.noAcquire AccessSourceRanks.Loads.scanned.events = true :=
  Orders.noAcquire_relaxed _

/-- No per-pair legality proof or graph checker result is needed for this
computed actual graph under its explicitly relaxed interface annotations. -/
theorem finite_fragment_legal :
    Concurrency.C23Atomic.Legal AccessGraphRanks.table.toCandidate :=
  executed.legal_without_acquire no_acquire_annotations

theorem structurally_well_formed :
    Concurrency.C23Atomic.WellFormed AccessGraphRanks.table.toCandidate :=
  AccessGraphRanks.built.wellFormed

theorem no_future_sequenced {reader writer : Nat}
    (source : Concurrency.C23Atomic.ReadsFrom AccessGraphRanks.table.toCandidate reader writer) :
    ¬ Concurrency.C23Atomic.SeqBefore AccessGraphRanks.table.toCandidate reader writer :=
  executed.noFutureSequenced source

theorem rmw_predecessor {index writer : Nat}
    (rmw : Concurrency.C23Atomic.IsRMW AccessGraphRanks.table.toCandidate index)
    (source : Concurrency.C23Atomic.ReadsFrom AccessGraphRanks.table.toCandidate index writer) :
    Concurrency.C23Atomic.ModBefore AccessGraphRanks.table.toCandidate writer index ∧
      ∀ middle, Concurrency.C23Atomic.ModBefore AccessGraphRanks.table.toCandidate writer middle →
        ¬ Concurrency.C23Atomic.ModBefore AccessGraphRanks.table.toCandidate middle index :=
  executed.rmwPredecessor rmw source

/-- The reused table includes every load and both equal-valued stores.
Thread and object expectations also check the full graph's initial-row offset. -/
theorem literal_mapping :
    AccessGraphRanks.table.sources = [none, some 0, none, none, some 3, some 2, some 3] ∧
      AccessGraphRanks.table.ranks = [0, 0, 15, 18, 0, 0, 0] ∧
      AccessGraphRanks.table.events.map (fun event => event.object) =
        [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] ∧
      AccessGraphRanks.table.events.map (fun event => event.thread) =
        [none, some 1, some 0, some 0, some 0, some 1, some 0] := by
  refine ⟨AccessGraphRanks.literal_sources, AccessGraphRanks.literal_ranks, ?_, ?_⟩
  all_goals decide +kernel

end LoadGraph

namespace CrossCell

theorem manifest_succeeds :
    (Initials.enumerate WriteViewRanks.Whole.initial.world).toOption.isSome = true := by
  obtain ⟨entries, success⟩ :=
    Initials.enumerate_success WriteViewRanks.Whole.initial_valid.1
  rw [success]
  rfl

def manifest : List Initials.Entry :=
  checked (Initials.enumerate WriteViewRanks.Whole.initial.world) manifest_succeeds

theorem manifest_actual :
    Initials.enumerate WriteViewRanks.Whole.initial.world = .ok manifest :=
  checked_ok _ _

/-- No caller supplies an object subset, initial word or replacement registry. -/
theorem manifest_covers_live (entry : Initials.Entry) :
    entry ∈ manifest ↔
      WriteViewRanks.Whole.initial.world.cells entry.identifier = some entry.cell ∧
      loadQWord (published WriteViewRanks.Whole.initial.world) entry.cell.address = .ok entry.value :=
  Initials.enumerate_live_iff WriteViewRanks.Whole.initial_valid.1 manifest_actual entry

/-- Primitive-interface annotations, not orders inferred from MOV/LOCK bytes. -/
def interfaceOrders : Orders where
  read _ _ := .relaxed
  write _ _ := .relaxed
  rmw _ _ := .relaxed

def inputs : Graph.Inputs :=
  ⟨manifest, WriteViewRanks.Whole.scanned.events,
    writes 151 WriteViewRanks.Whole.scanned.observations⟩

def buildAttempt : Option Graph.Table := Graph.build inputs interfaceOrders

theorem build_succeeds : buildAttempt.isSome = true := by decide +kernel

def table : Graph.Table := buildAttempt.get build_succeeds

theorem table_actual : Graph.build inputs interfaceOrders = some table :=
  get_ok buildAttempt build_succeeds

theorem built : Graph.Built inputs interfaceOrders table := Graph.build_sound table_actual

/-- This graph context uses the same actual run as the enumerated boundary.
The zero-delta RMW and both peer loads remain in the scanner's event list. -/
theorem executed : Graph.Executed WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
    .sharedCell 151 WriteViewRanks.Whole.scanned manifest interfaceOrders table where
  valid := WriteViewRanks.Whole.initial_valid
  sequenced := WriteViewRanks.Whole.initial_sequenced
  scanned := WriteViewRanks.Whole.scanned_actual
  quiescent := by
    simpa only [WriteViewRanks.Whole.result, AtomicTrace.Result.execution] using
      WriteViewRanks.Whole.final_quiescent
  mapped := built

theorem sequenced_coherent : Concurrency.C23Atomic.SequencedCoherent table.toCandidate :=
  executed.sequencedCoherent

theorem no_acquire_annotations : interfaceOrders.noAcquire WriteViewRanks.Whole.scanned.events = true :=
  Orders.noAcquire_relaxed _

theorem finite_fragment_legal : Concurrency.C23Atomic.Legal table.toCandidate :=
  executed.legal_without_acquire no_acquire_annotations

/-- Preserve acquiring orders as an explicit remaining obligation. These
controls use the same actual scan and distinguish acquiring MOV reads from
an acquiring read side of the unchanged-value RMW. -/
def acquiringLoads : Orders where
  read _ _ := .acquire
  write _ _ := .relaxed
  rmw _ _ := .relaxed

def acquiringRMW : Orders where
  read _ _ := .relaxed
  write _ _ := .relaxed
  rmw _ _ := .acquire

theorem acquiring_annotations_require_synchronization :
    acquiringLoads.noAcquire WriteViewRanks.Whole.scanned.events = false ∧
      acquiringRMW.noAcquire WriteViewRanks.Whole.scanned.events = false := by
  decide +kernel

theorem structurally_well_formed : Concurrency.C23Atomic.WellFormed table.toCandidate :=
  built.wellFormed

theorem no_future_sequenced {reader writer : Nat}
    (source : Concurrency.C23Atomic.ReadsFrom table.toCandidate reader writer) :
    ¬ Concurrency.C23Atomic.SeqBefore table.toCandidate reader writer :=
  executed.noFutureSequenced source

theorem rmw_predecessor {index writer : Nat}
    (rmw : Concurrency.C23Atomic.IsRMW table.toCandidate index)
    (source : Concurrency.C23Atomic.ReadsFrom table.toCandidate index writer) :
    Concurrency.C23Atomic.ModBefore table.toCandidate writer index ∧
      ∀ middle, Concurrency.C23Atomic.ModBefore table.toCandidate writer middle →
        ¬ Concurrency.C23Atomic.ModBefore table.toCandidate middle index :=
  executed.rmwPredecessor rmw source

/-- Full graph rows are initial A/B, store A, RMW B, peer B load, peer A load.
Initial B and the unchanged RMW both contain seven, but select different rows.
The intervening A publication supplies rank 153; it is not a B predecessor. -/
theorem literal_mapping :
    table.sources = [none, none, none, some 1, some 3, some 2] ∧
      table.ranks = [0, 0, 153, 154, 0, 0] ∧
      table.events.map (fun event => event.object) = [⟨0⟩, ⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨0⟩] ∧
      table.events.map (fun event => event.thread) =
        [none, none, some 0, some 0, some 1, some 1] := by
  decide +kernel

/-- A positive instance of the universal RMW theorem. Its RF writer is first
recovered from the actual RMW's source key, then compared with expected row one.
The other-cell A publication at rank 153 cannot become an intervening B write. -/
theorem initial_B_predecessor :
    Concurrency.C23Atomic.ReadsFrom table.toCandidate 3 1 ∧
      Concurrency.C23Atomic.ModBefore table.toCandidate 1 3 ∧
      ∀ middle, Concurrency.C23Atomic.ModBefore table.toCandidate 1 middle →
        ¬ Concurrency.C23Atomic.ModBefore table.toCandidate middle 3 := by
  let slot : Fin inputs.events.length := ⟨1, by decide +kernel⟩
  have actual : inputs.events[slot.val] =
      ⟨153, 0, .rmw WriteViewRanks.Whole.changed (.initial ⟨1⟩)⟩ := by
    simp [inputs, slot, WriteViewRanks.Whole.literal_accesses]
  have requested : inputs.events[slot.val].source = some (.initial ⟨1⟩) := by
    rw [actual]
    rfl
  obtain ⟨writer, _selected, edge⟩ := built.readsFrom slot requested
  have count : inputs.initials.length = 2 := by decide +kernel
  have actualEdge : Concurrency.C23Atomic.ReadsFrom table.toCandidate 3 writer.val := by
    simpa only [count, slot] using edge
  have source : table.source 3 = some 1 := by
    simp [Concurrency.C23Atomic.Check.Table.source, literal_mapping.1]
  have same : writer.val = 1 := Option.some.inj (actualEdge.1.symm.trans source)
  have knownEdge : Concurrency.C23Atomic.ReadsFrom table.toCandidate 3 1 := by
    simpa only [same] using actualEdge
  have rmw : Concurrency.C23Atomic.IsRMW table.toCandidate 3 := by
    refine ⟨inputs.events[slot.val].toSource interfaceOrders, ?_, ?_⟩
    · simpa [count, slot, Concurrency.C23Atomic.Check.Table.toCandidate] using built.event_at slot
    · rw [actual]
      rfl
  exact ⟨knownEdge, executed.rmwPredecessor rmw knownEdge⟩

/-- The RF witness comes from the actual B load's source-rank bridge.
The independently expected source row is compared only after that bridge. -/
theorem B_load_source :
    ∃ writer : table.Index,
      writer.val = 3 ∧
      Concurrency.C23Atomic.ReadsFrom table.toCandidate 4 writer.val ∧
      table.rank writer.val = 154 ∧
      Nonempty (ExecutionViews.At WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
        WriteViewRanks.Whole.result .sharedCell 3 1 WriteViewRanks.peerB
        151 PublishedHistory.empty (table.rank writer.val)) := by
  have selected : inputs.events[2]? =
      some ⟨154, 1, .load WriteViewRanks.peerB 7 (.rmw 153)⟩ := by
    change WriteViewRanks.Whole.scanned.events[2]? = _
    rw [WriteViewRanks.Whole.literal_accesses]
    rfl
  have publications : inputs.writes = writes 151 WriteViewRanks.Whole.result.2 := by
    unfold inputs WriteViewRanks.Whole.result AtomicTrace.Result.execution
    rfl
  obtain ⟨writer, edge, view⟩ :=
    WriteViewRanks.Whole.B_load_at.load_graph_rank_at
      (inputs := inputs) (orders := interfaceOrders) (table := table)
      (target := WriteViewRanks.peerB) WriteViewRanks.Whole.execution rfl built
      publications 2 selected
  have count : inputs.initials.length = 2 := by decide +kernel
  have actualEdge : Concurrency.C23Atomic.ReadsFrom table.toCandidate 4 writer.val := by
    simpa only [count] using edge
  have source : table.source 4 = some 3 := by
    simp [Concurrency.C23Atomic.Check.Table.source, literal_mapping.1]
  have same : writer.val = 3 := Option.some.inj (actualEdge.1.symm.trans source)
  refine ⟨writer, same, actualEdge, ?_, ?_⟩
  · rw [same]
    simp [Concurrency.C23Atomic.Check.Table.rank, literal_mapping.2.1]
  · exact view

/-- The other peer load selects A's buffered writer, not B's later RMW.
Both peer clients retain actual prestate views at their selected graph ranks. -/
theorem A_load_source :
    ∃ writer : table.Index,
      writer.val = 2 ∧
      Concurrency.C23Atomic.ReadsFrom table.toCandidate 5 writer.val ∧
      table.rank writer.val = 153 ∧
      Nonempty (ExecutionViews.At WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
        WriteViewRanks.Whole.result .sharedCell 4 1 WriteViewRanks.peerA
        151 PublishedHistory.empty (table.rank writer.val)) := by
  have selected : inputs.events[3]? =
      some ⟨155, 1, .load WriteViewRanks.peerA 0 (.store 0 0)⟩ := by
    change WriteViewRanks.Whole.scanned.events[3]? = _
    rw [WriteViewRanks.Whole.literal_accesses]
    rfl
  have publications : inputs.writes = writes 151 WriteViewRanks.Whole.result.2 := by
    unfold inputs WriteViewRanks.Whole.result AtomicTrace.Result.execution
    rfl
  obtain ⟨writer, edge, view⟩ :=
    WriteViewRanks.Whole.A_load_at.load_graph_rank_at
      (inputs := inputs) (orders := interfaceOrders) (table := table)
      (target := WriteViewRanks.peerA) WriteViewRanks.Whole.execution rfl built
      publications 3 selected
  have count : inputs.initials.length = 2 := by decide +kernel
  have actualEdge : Concurrency.C23Atomic.ReadsFrom table.toCandidate 5 writer.val := by
    simpa only [count] using edge
  have source : table.source 5 = some 2 := by
    simp [Concurrency.C23Atomic.Check.Table.source, literal_mapping.1]
  have same : writer.val = 2 := Option.some.inj (actualEdge.1.symm.trans source)
  refine ⟨writer, same, actualEdge, ?_, view⟩
  rw [same]
  simp [Concurrency.C23Atomic.Check.Table.rank, literal_mapping.2.1]

end CrossCell

namespace RMWReads

/-- Normalize a generic actual read-side view against independently supplied
writer evidence. The rank is not a premise of the production read-side API. -/
private theorem read_at_known_rank {initial : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {event : AtomicTrace.Event} {index offset rank : Nat} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset PublishedHistory.empty)
    (read : ReadAccess event source)
    (known : WriterRank initial actions result profile offset event.object source rank) :
    ∃ target, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid target
        offset PublishedHistory.empty rank) ∧
      WriterRank initial actions result profile offset event.object source rank := by
  obtain ⟨target, actualRank, related, view, ranked⟩ := actual.read_view_rank execution read
  have same : actualRank = rank :=
    WriterRank.unique execution.success execution.sequenced ranked known
  subst actualRank
  exact ⟨target, related, view, ranked⟩

/-- A first RMW really reads rank zero. Its target/view are recovered from
the actual admission, rather than constructed from the literal inequality. -/
theorem initial_source :
    ∃ target,
      AccessTarget ⟨81, 0, .rmw RMWSourceRanks.Initial.changed
        (.initial RMWSourceRanks.Initial.changed.cell)⟩ target ∧
      Nonempty (ExecutionViews.At RMWSourceRanks.Initial.initial
        RMWSourceRanks.Initial.actions RMWSourceRanks.Initial.scanned.execution
        .sharedCell 0 0 target 81 PublishedHistory.empty 0) ∧
      WriterRank RMWSourceRanks.Initial.initial RMWSourceRanks.Initial.actions
        RMWSourceRanks.Initial.scanned.execution .sharedCell 81
        RMWSourceRanks.Initial.changed.cell (.initial RMWSourceRanks.Initial.changed.cell) 0 := by
  exact read_at_known_rank RMWSourceRanks.Initial.execution RMWSourceRanks.Initial.actual
    (ReadAccess.rmw rfl) WriterRank.initial

/-- The source publication is rank 63, not the preceding global action rank
64 or the RMW's own rank 65. The independent witness is the real prefix's
published source, including the peer's intervening pending store. -/
theorem gapped_source :
    ∃ target, AccessTarget ⟨64, 0, .rmw RMWSourceRanks.Gap.changed (.store 0 0)⟩ target ∧
      Nonempty (ExecutionViews.At MixedWriteOrder.initial RMWSourceRanks.Gap.actions
        RMWSourceRanks.Gap.scanned.execution .sharedCell 3 0 target
        61 PublishedHistory.empty 63) ∧
      WriterRank MixedWriteOrder.initial RMWSourceRanks.Gap.actions
        RMWSourceRanks.Gap.scanned.execution .sharedCell 61
        RMWSourceRanks.Gap.changed.cell (.store 0 0) 63 := by
  exact read_at_known_rank RMWSourceRanks.Gap.execution RMWSourceRanks.Gap.actual
    (ReadAccess.rmw rfl) RMWSourceRanks.Gap.source_rank

/-- A real same-worker store precedes the RMW's read side. Its publication
and the exact source rank both refer to the actual first store, not its value. -/
theorem write_read :
    ∃ rank, WriterRank MixedWriteOrder.initial MixedWriteOrder.actions
      AccessSourceRanks.RMW.scanned.execution .sharedCell 37 MixedWriteOrder.event.cell
      (.store 0 0) rank ∧ rank = 40 ∧ MixedWriteOrder.firstStoreStamp.position + 1 ≤ rank := by
  obtain ⟨firstStore, _firstRMW, _secondStore, _secondRMW, _indices⟩ :=
    MixedWriteOrder.instruction_writes
  have written : PublishedHistory.InstructionWriteAt MixedWriteOrder.initial MixedWriteOrder.actions
      AccessSourceRanks.RMW.scanned.execution .sharedCell 37 0 MixedWriteOrder.firstStoreStamp := by
    rw [AccessSourceRanks.RMW.execution_eq]
    exact firstStore
  have sameCell : MixedWriteOrder.firstStoreStamp.cause.cell = MixedWriteOrder.event.cell :=
    MixedWriteOrder.event_contract.2.2.1.symm
  obtain ⟨rank, ranked, bound⟩ := AccessSourceRanks.RMW.first_rmw_at.write_read_source_rank
    AccessSourceRanks.RMW.execution written (ReadAccess.rmw rfl) rfl sameCell (by decide)
  exact ⟨rank, ranked,
    WriterRank.unique AccessSourceRanks.RMW.scheduled MixedWriteOrder.initial_sequenced
      ranked AccessSourceRanks.RMW.first_store_rank, bound⟩

/-- Both reads are real RMWs with identical arithmetic payloads. Their
different source identities are fixed by two independent store publications. -/
theorem read_read :
    ∃ firstRank secondRank,
      WriterRank MixedWriteOrder.initial MixedWriteOrder.actions
        AccessSourceRanks.RMW.scanned.execution .sharedCell 37 MixedWriteOrder.event.cell
        (.store 0 0) firstRank ∧
      WriterRank MixedWriteOrder.initial MixedWriteOrder.actions
        AccessSourceRanks.RMW.scanned.execution .sharedCell 37 MixedWriteOrder.event.cell
        (.store 0 1) secondRank ∧
      firstRank = 40 ∧ secondRank = 44 ∧ firstRank ≤ secondRank := by
  obtain ⟨firstRank, secondRank, first, second, ordered⟩ :=
    AccessSourceRanks.RMW.first_rmw_at.read_read_source_rank AccessSourceRanks.RMW.execution
      (ReadAccess.rmw rfl) AccessSourceRanks.RMW.second_rmw_at (ReadAccess.rmw rfl)
      rfl rfl (by decide)
  exact ⟨firstRank, secondRank, first, second,
    WriterRank.unique AccessSourceRanks.RMW.scheduled MixedWriteOrder.initial_sequenced
      first AccessSourceRanks.RMW.first_store_rank,
    WriterRank.unique AccessSourceRanks.RMW.scheduled MixedWriteOrder.initial_sequenced
      second AccessSourceRanks.RMW.second_store_rank, ordered⟩

/-- The first RMW's actual source strictly precedes the later same-worker
store publication. No fresh program or desired source-rank premise is used. -/
theorem read_write :
    ∃ rank, WriterRank MixedWriteOrder.initial MixedWriteOrder.actions
      AccessSourceRanks.RMW.scanned.execution .sharedCell 37 MixedWriteOrder.event.cell
      (.store 0 0) rank ∧ rank = 40 ∧ rank < MixedWriteOrder.secondStoreStamp.position + 1 := by
  obtain ⟨_firstStore, _firstRMW, secondStore, _secondRMW, _indices⟩ :=
    MixedWriteOrder.instruction_writes
  have written : PublishedHistory.InstructionWriteAt MixedWriteOrder.initial MixedWriteOrder.actions
      AccessSourceRanks.RMW.scanned.execution .sharedCell 37 4 MixedWriteOrder.secondStoreStamp := by
    rw [AccessSourceRanks.RMW.execution_eq]
    exact secondStore
  obtain ⟨rank, ranked, bound⟩ := AccessSourceRanks.RMW.first_rmw_at.read_write_source_rank_lt
    AccessSourceRanks.RMW.execution (ReadAccess.rmw rfl) written rfl (by decide)
  exact ⟨rank, ranked,
    WriterRank.unique AccessSourceRanks.RMW.scheduled MixedWriteOrder.initial_sequenced
      ranked AccessSourceRanks.RMW.first_store_rank, bound⟩

end RMWReads
end EDSL.Tests.GraphOperationalCoherence

#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.literal_mapping
#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.executed
#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.sequenced_coherent
#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.finite_fragment_legal
#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.structurally_well_formed
#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.no_future_sequenced
#print axioms EDSL.Tests.GraphOperationalCoherence.LoadGraph.rmw_predecessor
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.manifest_actual
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.manifest_covers_live
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.build_succeeds
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.table_actual
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.built
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.executed
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.sequenced_coherent
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.finite_fragment_legal
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.acquiring_annotations_require_synchronization
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.structurally_well_formed
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.no_future_sequenced
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.rmw_predecessor
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.literal_mapping
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.initial_B_predecessor
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.B_load_source
#print axioms EDSL.Tests.GraphOperationalCoherence.CrossCell.A_load_source
#print axioms EDSL.Tests.GraphOperationalCoherence.RMWReads.initial_source
#print axioms EDSL.Tests.GraphOperationalCoherence.RMWReads.gapped_source
#print axioms EDSL.Tests.GraphOperationalCoherence.RMWReads.write_read
#print axioms EDSL.Tests.GraphOperationalCoherence.RMWReads.read_read
#print axioms EDSL.Tests.GraphOperationalCoherence.RMWReads.read_write
#audit_edsl
