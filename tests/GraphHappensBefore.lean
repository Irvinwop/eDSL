/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.AccessGraphRanks
import tests.C23AtomicEvents
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphHappensBefore

/-!
Actual-execution clients for synchronization and happens-before clocks with
acquiring interface orders. The first program publishes a release store, then
runs a foreign-thread RMW and a second acquiring RMW. The latter reads through
the foreign RMW's membership in the original store's release sequence.

The second program reuses the equal-word scan with acquiring MOV reads and
release MOV writes. It distinguishes own forwarding from the peer's older
equal-valued source, including forwarding before the selected store drains.
Both tables are computed by `Graph.build` from complete scanned events and
publications. Initial manifests come from the actual live registry.

Literal arithmetic, sources, ranks and clocks are independent expectations.
Finite reflection supplies only concrete RF/release-sequence/SW witnesses;
universal clock, acyclicity and no-future-HB facts come from actual execution,
without the graph legality checker or an HB certificate.

Scope: finite sharedCell scalar-RAM, long-mode/CET-off executions and explicit
primitive-interface annotations. These claims do not establish acquiring
coherence or full C23 legality, native/kernel behavior, fairness, graph-build
totality, compiler preservation or new compiler-corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.Tests.GraphHappensBefore
open X86 OS.TSO64 OS.TSO64.C23Projection AtomicTrace
open Concurrency.C23Atomic

private instance : DecidableEq
    (Nat × Nat × Nat × OS.Atomics64.CellId64 × Word × Option WriterId × Option WriterId) :=
  inferInstance

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

namespace ForeignRMW

/-- MOV [RDI],RSI; LOCK XADD [RDI],RSI. The peer starts at the LOCK.
The store writes seven; the peer adds five; the original worker adds seven. -/
def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x37c10f48f0378948 0 9 7 5 0 3

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel

def initial : OS.TSO64.State := checked initialAttempt initial_succeeds

theorem initial_actual : initialAttempt = .ok initial := checked_ok _ _

def actions : List Action :=
  [.issue 0 false, .issue 0 true, .drain 0, .issue 1 true, .issue 0 false]

def scanAttempt : Except Fault AtomicTrace.Result :=
  AtomicTrace.scan initial actions .sharedCell 61

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

def scanned : AtomicTrace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual : AtomicTrace.scan initial actions .sharedCell 61 = .ok scanned :=
  checked_ok _ _

theorem initial_valid : OS.TSO64.WellFormed initial .sharedCell :=
  AccessSourceRanks.shared_start_valid initial_actual

theorem initial_sequenced : Sequenced initial :=
  quiescent_sequenced (AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel))

theorem final_quiescent : Quiescent scanned.state :=
  AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)

theorem manifest_succeeds : (Initials.enumerate initial.world).toOption.isSome = true := by
  obtain ⟨entries, success⟩ := Initials.enumerate_success initial_valid.1
  rw [success]
  rfl

def manifest : List Initials.Entry :=
  checked (Initials.enumerate initial.world) manifest_succeeds

theorem manifest_actual : Initials.enumerate initial.world = .ok manifest := checked_ok _ _

theorem manifest_covers_live (entry : Initials.Entry) :
    entry ∈ manifest ↔ initial.world.cells entry.identifier = some entry.cell ∧
      loadQWord (published initial.world) entry.cell.address = .ok entry.value :=
  Initials.enumerate_live_iff initial_valid.1 manifest_actual entry

/-- These annotations are declared by the primitive interface, not decoded
from MOV or LOCK bytes. The RMWs have acquiring and releasing read/write sides. -/
def interfaceOrders : Orders where
  read _ _ := .acquire
  write _ _ := .release
  rmw _ _ := .acqRel

def inputs : Graph.Inputs := Graph.runInputs manifest scanned 61
def buildAttempt : Option Graph.Table := Graph.build inputs interfaceOrders

theorem build_succeeds : buildAttempt.isSome = true := by decide +kernel

def table : Graph.Table := buildAttempt.get build_succeeds

theorem table_actual : Graph.build inputs interfaceOrders = some table := get_ok _ _

theorem built : Graph.Built inputs interfaceOrders table := Graph.build_sound table_actual

theorem executed : Graph.Executed initial actions .sharedCell 61 scanned
    manifest interfaceOrders table :=
  ⟨initial_valid, initial_sequenced, scanned_actual, final_quiescent, built⟩

/-- The blocked LOCK emits no atomic event. RMW source keys name original
positions, and both successful RMWs retain independent arithmetic contracts. -/
theorem literal_accesses : scanned.events.map TSO64AtomicTrace.eventSummary =
    [(61, 0, 1, ⟨0⟩, 7, none, some (.store 0 0)),
      (64, 1, 2, ⟨0⟩, 12, some (.store 0 0), some (.rmw 64)),
      (65, 0, 2, ⟨0⟩, 19, some (.rmw 64), some (.rmw 65))] := by
  decide +kernel

theorem literal_mapping :
    table.sources = [none, none, some 1, some 2] ∧
      table.ranks = [0, 64, 65, 66] ∧
      table.events = [⟨none, ⟨0⟩, .initialize 9⟩,
        ⟨some 0, ⟨0⟩, .store .release 7⟩,
        ⟨some 1, ⟨0⟩, .rmw .acqRel 7 12⟩,
        ⟨some 0, ⟨0⟩, .rmw .acqRel 12 19⟩] := by
  decide +kernel

theorem event_count : table.events.length = 4 := by rw [literal_mapping.2.2]; rfl

def head : table.Index := ⟨1, by rw [event_count]; decide⟩
def foreign : table.Index := ⟨2, by rw [event_count]; decide⟩
def observer : table.Index := ⟨3, by rw [event_count]; decide⟩

theorem foreign_reads_store : ReadsFrom table.toCandidate 2 1 :=
  (Check.rf_iff table foreign head).mpr (by decide +kernel)

theorem observer_reads_foreign : ReadsFrom table.toCandidate 3 2 :=
  (Check.rf_iff table observer foreign).mpr (by decide +kernel)

/-- This is a proper successor member, on a different thread from its head. -/
theorem foreign_release_member : ReleaseMember table.toCandidate 1 2 :=
  (Check.releaseMember_iff table head foreign).mpr (by decide +kernel)

theorem foreign_thread : ¬ SameThread table.toCandidate 1 2 := by
  simp [SameThread, Check.Table.toCandidate, literal_mapping.2.2]

theorem through_foreign_synchronizes : SynchronizesWith table.toCandidate 1 3 := by
  refine ⟨(Check.acquires_iff table observer).mpr (by decide +kernel),
    2, observer_reads_foreign, foreign_release_member⟩

theorem through_foreign_hb : HappensBefore table.toCandidate 1 3 :=
  .synchronizes through_foreign_synchronizes

/-- Drains and a blocked action remain in the clock; row indices and
publication ranks do not replace the actual store's issue position. -/
theorem literal_clocks :
    (List.range 4).map (Graph.actionClock manifest scanned) = [0, 62, 65, 66] := by
  decide +kernel

theorem through_foreign_clock :
    Graph.actionClock manifest scanned 1 < Graph.actionClock manifest scanned 3 :=
  executed.hb_clock_lt through_foreign_hb

theorem hb_acyclic (index : Nat) : ¬ HappensBefore table.toCandidate index index :=
  executed.hb_acyclic index

theorem no_future_hb {reader writer : Nat} (source : ReadsFrom table.toCandidate reader writer) :
    ¬ HappensBefore table.toCandidate reader writer := executed.noFutureHB source

end ForeignRMW

namespace ForwardedLoads

def interfaceOrders : Orders where
  read _ _ := .acquire
  write _ _ := .release
  rmw _ _ := .acqRel

def inputs : Graph.Inputs :=
  Graph.runInputs AccessGraphRanks.manifest AccessSourceRanks.Loads.scanned 10

def buildAttempt : Option Graph.Table := Graph.build inputs interfaceOrders

theorem build_succeeds : buildAttempt.isSome = true := by decide +kernel

def table : Graph.Table := buildAttempt.get build_succeeds

theorem table_actual : Graph.build inputs interfaceOrders = some table := get_ok _ _

theorem built : Graph.Built inputs interfaceOrders table := Graph.build_sound table_actual

theorem executed : Graph.Executed AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
    .sharedCell 10 AccessSourceRanks.Loads.scanned AccessGraphRanks.manifest
    interfaceOrders table :=
  executed_run AccessSourceRanks.Loads.execution rfl
    AccessSourceRanks.Loads.scanned_actual built

theorem literal_mapping :
    table.sources = [none, some 0, none, none, some 3, some 2, some 3] ∧
      table.ranks = [0, 0, 15, 18, 0, 0, 0] ∧ table.events.length = 7 ∧
      (List.range 7).map
        (Graph.actionClock AccessGraphRanks.manifest AccessSourceRanks.Loads.scanned) =
          [0, 11, 12, 13, 14, 16, 17] := by
  decide +kernel

def older : table.Index := ⟨2, by rw [literal_mapping.2.2.1]; decide⟩
def newer : table.Index := ⟨3, by rw [literal_mapping.2.2.1]; decide⟩
def forwarded : table.Index := ⟨4, by rw [literal_mapping.2.2.1]; decide⟩
def peer : table.Index := ⟨5, by rw [literal_mapping.2.2.1]; decide⟩

theorem forwarded_source : ReadsFrom table.toCandidate 4 3 :=
  (Check.rf_iff table forwarded newer).mpr (by decide +kernel)

theorem peer_source : ReadsFrom table.toCandidate 5 2 :=
  (Check.rf_iff table peer older).mpr (by decide +kernel)

/-- Identical stored words cannot substitute the older store for the
forwarded occurrence or the newer pending store for the peer's publication. -/
theorem equal_words_keep_distinct_sources :
    ¬ ReadsFrom table.toCandidate 4 2 ∧ ¬ ReadsFrom table.toCandidate 5 3 :=
  ⟨not_readsFrom_of_ne forwarded_source (by decide),
    not_readsFrom_of_ne peer_source (by decide)⟩

theorem forwarded_synchronizes : SynchronizesWith table.toCandidate 3 4 :=
  (Check.sync_iff table newer forwarded).mpr (by decide +kernel)

theorem peer_synchronizes : SynchronizesWith table.toCandidate 2 5 :=
  (Check.sync_iff table older peer).mpr (by decide +kernel)

theorem forwarded_hb : HappensBefore table.toCandidate 3 4 :=
  .synchronizes forwarded_synchronizes

theorem forwarded_clock :
    Graph.actionClock AccessGraphRanks.manifest AccessSourceRanks.Loads.scanned 3 <
      Graph.actionClock AccessGraphRanks.manifest AccessSourceRanks.Loads.scanned 4 :=
  executed.hb_clock_lt forwarded_hb

theorem hb_acyclic (index : Nat) : ¬ HappensBefore table.toCandidate index index :=
  executed.hb_acyclic index

theorem no_future_hb {reader writer : Nat} (source : ReadsFrom table.toCandidate reader writer) :
    ¬ HappensBefore table.toCandidate reader writer := executed.noFutureHB source

end ForwardedLoads

/-- Reuse the independent model-level negative control: a foreign plain
write breaks the sequence even when the selected later RMW writes equal bits. -/
theorem foreign_plain_write_breaks_sequence :
    ¬ ReleaseMember C23AtomicEvents.interrupted 1 4 ∧
      ¬ SynchronizesWith C23AtomicEvents.interrupted 1 5 :=
  ⟨C23AtomicEvents.interrupted_no_rejoin, C23AtomicEvents.interrupted_no_sync⟩

end EDSL.Tests.GraphHappensBefore

#print axioms EDSL.Tests.GraphHappensBefore.ForeignRMW.executed
#print axioms EDSL.Tests.GraphHappensBefore.ForeignRMW.manifest_covers_live
#print axioms EDSL.Tests.GraphHappensBefore.ForeignRMW.foreign_release_member
#print axioms EDSL.Tests.GraphHappensBefore.ForeignRMW.through_foreign_hb
#print axioms EDSL.Tests.GraphHappensBefore.ForeignRMW.hb_acyclic
#print axioms EDSL.Tests.GraphHappensBefore.ForeignRMW.no_future_hb
#print axioms EDSL.Tests.GraphHappensBefore.ForwardedLoads.executed
#print axioms EDSL.Tests.GraphHappensBefore.ForwardedLoads.equal_words_keep_distinct_sources
#print axioms EDSL.Tests.GraphHappensBefore.ForwardedLoads.forwarded_hb
#print axioms EDSL.Tests.GraphHappensBefore.ForwardedLoads.hb_acyclic
#print axioms EDSL.Tests.GraphHappensBefore.ForwardedLoads.no_future_hb
#audit_edsl
