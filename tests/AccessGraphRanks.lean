/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.AccessSourceRanks
import tests.RMWSourceRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphRanks

/-!
Source-rank graph clients for an actual finite equal-word execution. The
`AccessSourceRanks.Loads` program reads initialization, issues two zero stores,
forwards the newer store, drains the older store, then reads from the peer and
forwards again before the newer store drains. Its successful annotated scan
and original access origins supply the execution, events and complete writes.

The initial manifest is computed by `Initials.enumerate` on that execution's
initial world. Incoming publication history is empty; the live initial registry
and its published RAM are still present. Relaxed interface orders are declared
explicitly here, with no inference from MOV bytes. `Graph.build` computes and
checks the table; no graph, RF selection or desired rank is an execution input.

Independent literals distinguish original cuts 0/3/5/6, filtered event indices
0/3/4/5, full graph rows 1/4/5/6 and source rows 0/3/2/3. The equal stores have
actual publication ranks 15 and 18. Every load's own row has rank zero; its
returned semantic RF writer carries the rank of its actual prestate `At` view.

The scope is the finite sharedCell scalar-RAM, long-mode/CET-off execution with
stable initialized resources authenticated by `Loads.execution`. This supplies
no C23 legality, graph-construction totality, lifecycle/fairness, native or final
ELF verification, or additional corpus-coverage claim.
-/

set_option autoImplicit false

namespace EDSL.Tests.AccessGraphRanks
open X86 OS.TSO64 OS.TSO64.C23Projection
open AtomicTrace AccessSourceRanks

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

theorem manifest_succeeds :
    (Initials.enumerate Loads.initial.world).toOption.isSome = true := by
  obtain ⟨entries, success⟩ := Initials.enumerate_success Loads.initial_valid.1
  rw [success]
  rfl

def manifest : List Initials.Entry :=
  checked (Initials.enumerate Loads.initial.world) manifest_succeeds

theorem manifest_actual : Initials.enumerate Loads.initial.world = .ok manifest :=
  checked_ok (Initials.enumerate Loads.initial.world) manifest_succeeds

/-- Every live readable initial object is covered, with its actual RAM word.
No subset of objects or list of initial values is supplied to enumeration. -/
theorem manifest_covers_live (entry : Initials.Entry) :
    entry ∈ manifest ↔ Loads.initial.world.cells entry.identifier = some entry.cell ∧
      loadQWord (published Loads.initial.world) entry.cell.address = .ok entry.value :=
  Initials.enumerate_live_iff Loads.initial_valid.1 manifest_actual entry

/-- These are declared primitive-interface annotations for this client. -/
def interfaceOrders : Orders where
  read _ _ := .relaxed
  write _ _ := .relaxed
  rmw _ _ := .relaxed

def inputs : Graph.Inputs :=
  ⟨manifest, Loads.scanned.events, writes 10 Loads.result.2⟩

private theorem inputs_writes (initials : List Initials.Entry) (events : List AtomicTrace.Event)
    (publications : List PublishedHistory.Stamp) :
    (Graph.Inputs.mk initials events publications).writes = publications := rfl

theorem complete_publications : inputs.writes = writes 10 Loads.result.2 :=
  inputs_writes manifest Loads.scanned.events (writes 10 Loads.result.2)

private theorem inputs_events (initials : List Initials.Entry) (events : List AtomicTrace.Event)
    (publications : List PublishedHistory.Stamp) :
    (Graph.Inputs.mk initials events publications).events = events := rfl

theorem events_eq : inputs.events = Loads.scanned.events :=
  inputs_events manifest Loads.scanned.events (writes 10 Loads.result.2)

private theorem event_lookup {graphInputs : Graph.Inputs} {events : List AtomicTrace.Event}
    {index : Nat} {event : AtomicTrace.Event} (same : graphInputs.events = events)
    (selected : events[index]? = some event) : graphInputs.events[index]? = some event := by
  rw [same]
  exact selected

theorem initial_count : inputs.initials.length = 1 := by decide +kernel
theorem event_count : inputs.events.length = 6 := by decide +kernel

def buildAttempt : Option Graph.Table := Graph.build inputs interfaceOrders

theorem build_succeeds : buildAttempt.isSome = true := by decide +kernel

def table : Graph.Table := buildAttempt.get build_succeeds

theorem table_actual : Graph.build inputs interfaceOrders = some table :=
  get_ok buildAttempt build_succeeds

theorem built : Graph.Built inputs interfaceOrders table := Graph.build_sound table_actual

/-- The full graph includes initialization and every intervening load. These
literal expectations are checked against the computed build, not its proposal
algorithm or a caller-constructed table. Equal zero words select distinct rows. -/
theorem literal_sources :
    table.sources = [none, some 0, none, none, some 3, some 2, some 3] := by
  decide +kernel

/-- Actual drains at positions 14 and 17 determine writer ranks 15 and 18.
Issue positions 11/12, filtered indices 1/2 and load rows do not supply them. -/
theorem literal_ranks : table.ranks = [0, 0, 15, 18, 0, 0, 0] := by
  decide +kernel

/-- Retain the very writer returned by the actual-access graph bridge, its
semantic RF edge, its independent literal row/rank and the view at its rank.
The load's own row is checked separately in the same contract. -/
def GraphLoadContract (graph : Graph.Table) (initial : OS.TSO64.State) (actions : List Action)
    (result : OS.TSO64.State × List Observation) (profile : Profile) (offset cut tid : Nat)
    (target : Queue.ManagedRef)
    (reader writerRow sourceRank : Nat) : Prop :=
  ∃ writer : graph.Index,
    writer.val = writerRow ∧
    Concurrency.C23Atomic.ReadsFrom graph.toCandidate reader writer.val ∧
    graph.rank writer.val = sourceRank ∧ graph.rank reader = 0 ∧
    Nonempty (ExecutionViews.At initial actions result profile
      cut tid target offset PublishedHistory.empty (graph.rank writer.val))

abbrev LoadContract (cut tid : Nat) (target : Queue.ManagedRef)
    (reader writerRow sourceRank : Nat) : Prop :=
  GraphLoadContract table Loads.initial Loads.actions Loads.result .sharedCell 10
    cut tid target reader writerRow sourceRank

-- This only aligns the returned semantic edge with already checked table
-- literals. The actual-access bridge below derives the RF edge and At witness
-- before these comparisons; neither is manufactured from a table lookup.
private theorem load_contract_of_graph_view {graph : Graph.Table}
    {initial : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {offset cut tid reader computedReader writerRow sourceRank : Nat}
    {target : Queue.ManagedRef}
    (actual : ∃ writer : graph.Index,
      Concurrency.C23Atomic.ReadsFrom graph.toCandidate computedReader writer.val ∧
      Nonempty (ExecutionViews.At initial actions result profile
        cut tid target offset PublishedHistory.empty (graph.rank writer.val)))
    (readerEq : computedReader = reader)
    (selected : graph.source reader = some writerRow)
    (ranked : graph.rank writerRow = sourceRank) (own : graph.rank reader = 0) :
    GraphLoadContract graph initial actions result profile offset cut tid target
      reader writerRow sourceRank := by
  subst computedReader
  obtain ⟨writer, edge, view⟩ := actual
  have same : writer.val = writerRow := Option.some.inj (edge.1.symm.trans selected)
  exact ⟨writer, same, edge, by simpa only [same] using ranked, own, view⟩

/-- Original cut zero, filtered event zero, graph load row one: initialization
is the actual source even though both later stores also contain zero. -/
theorem initial_load : LoadContract 0 1 Loads.firstReference 1 0 0 := by
  apply load_contract_of_graph_view (computedReader := inputs.initials.length + 0)
  · exact Loads.initial_load_at.load_graph_rank_at (inputs := inputs) (orders := interfaceOrders)
        (table := table) (target := Loads.firstReference) Loads.execution rfl built complete_publications
        0 (event_lookup events_eq Loads.computed_loads.1)
  · rw [initial_count]
  all_goals simp [Concurrency.C23Atomic.Check.Table.source,
    Concurrency.C23Atomic.Check.Table.rank, literal_sources, literal_ranks]

/-- Original cut three, filtered event three: forwarding selects writer row
three and its eventual rank eighteen, while the load row four has rank zero. -/
theorem forwarded_load : LoadContract 3 0 Loads.ownReference 4 3 18 := by
  apply load_contract_of_graph_view (computedReader := inputs.initials.length + 3)
  · exact Loads.forwarded_load_at.load_graph_rank_at (inputs := inputs) (orders := interfaceOrders)
        (table := table) (target := Loads.ownReference) Loads.execution rfl built complete_publications
        3 (event_lookup events_eq Loads.computed_loads.2.1)
  · rw [initial_count]
  all_goals simp [Concurrency.C23Atomic.Check.Table.source,
    Concurrency.C23Atomic.Check.Table.rank, literal_sources, literal_ranks]

/-- Original cut five is filtered event four. The peer reads older writer row
two at rank fifteen, independently of the newer equal-valued pending store. -/
theorem published_load : LoadContract 5 1 Loads.peerReference 5 2 15 := by
  apply load_contract_of_graph_view (computedReader := inputs.initials.length + 4)
  · exact Loads.published_load_at.load_graph_rank_at (inputs := inputs) (orders := interfaceOrders)
        (table := table) (target := Loads.peerReference) Loads.execution rfl built complete_publications
        4 (event_lookup events_eq Loads.computed_loads.2.2.1)
  · rw [initial_count]
  all_goals simp [Concurrency.C23Atomic.Check.Table.source,
    Concurrency.C23Atomic.Check.Table.rank, literal_sources, literal_ranks]

/-- After the older drain, original cut six is filtered event five. Own
forwarding still selects rank eighteen; the equal published rank is fifteen. -/
theorem forwarded_after_older_drain : LoadContract 6 0 Loads.ownReference 6 3 18 := by
  apply load_contract_of_graph_view (computedReader := inputs.initials.length + 5)
  · exact Loads.forwarded_after_older_drain_at.load_graph_rank_at (inputs := inputs) (orders := interfaceOrders)
        (table := table) (target := Loads.ownReference) Loads.execution rfl built
        complete_publications 5 (event_lookup events_eq Loads.computed_loads.2.2.2)
  · rw [initial_count]
  all_goals simp [Concurrency.C23Atomic.Check.Table.source,
    Concurrency.C23Atomic.Check.Table.rank, literal_sources, literal_ranks]

end EDSL.Tests.AccessGraphRanks

#print axioms EDSL.Tests.AccessGraphRanks.manifest_actual
#print axioms EDSL.Tests.AccessGraphRanks.manifest_covers_live
#print axioms EDSL.Tests.AccessGraphRanks.build_succeeds
#print axioms EDSL.Tests.AccessGraphRanks.table_actual
#print axioms EDSL.Tests.AccessGraphRanks.built
#print axioms EDSL.Tests.AccessGraphRanks.literal_sources
#print axioms EDSL.Tests.AccessGraphRanks.literal_ranks
#print axioms EDSL.Tests.AccessGraphRanks.initial_load
#print axioms EDSL.Tests.AccessGraphRanks.forwarded_load
#print axioms EDSL.Tests.AccessGraphRanks.published_load
#print axioms EDSL.Tests.AccessGraphRanks.forwarded_after_older_drain
#audit_edsl
