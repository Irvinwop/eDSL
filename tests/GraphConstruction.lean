/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.GraphHBCoherence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphConstruction
import EDSL.Audit

/-!
Graph-construction clients start with initialized resources and actual scans,
without a supplied graph table, structural correspondence, builder-acceptance
certificate or legality proof. Every typed interface annotation is admitted by
the reusable construction theorem. No client reflects on builder success.

The fixtures independently exercise a foreign-thread release sequence at offset
61, equal-word FIFO forwarding at offset 10, and cross-cell publication at
offset 151. For the acquiring interfaces, determinism identifies the constructed
output with an existing computed table, allowing reuse of independent RF and
publication-rank expectations without new per-program construction proofs.

Scope: initial and final empty queues, initialized stable resources, finite
sharedCell scalar-RAM long-mode/CET-off executions and explicit typed interface
orders. This does not establish full C23, compiler preservation, native CPU or
kernel behavior, fairness, or additional compiler-corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.Tests.GraphConstruction
open X86 OS.TSO64 OS.TSO64.C23Projection AtomicTrace
open Concurrency.C23Atomic

/-- This equality only identifies an already constructed output for the literal
checks below; it supplies no premise to any raw construction theorem. -/
private theorem build_deterministic {inputs : Graph.Inputs} {orders : Orders}
    {left right : Graph.Table}
    (first : Graph.build inputs orders = some left)
    (second : Graph.build inputs orders = some right) : left = right :=
  Option.some.inj (first.symm.trans second)

namespace ForeignRMW
open GraphHappensBefore.ForeignRMW

/-- The blocked LOCK, both successful RMWs and real store publication remain in
the scan. The only reflected new boundary fact is that the initial queues are
empty; construction and legality are obtained from the production theorems. -/
theorem captured : Graph.Captured initial actions .sharedCell 61 scanned manifest where
  valid := initial_valid
  initialEmpty := AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)
  scanned := scanned_actual
  quiescent := final_quiescent
  enumerated := manifest_actual

/-- The executable builder succeeds for any declared typed interface orders,
including acquiring read sides. No finite builder decision appears here. -/
theorem complete (orders : Orders) :
    ∃ table, Graph.build inputs orders = some table ∧
      Graph.Executed initial actions .sharedCell 61 scanned manifest orders table :=
  captured.build_complete orders

theorem constructed (orders : Orders) :
    ∃ table, Graph.build inputs orders = some table ∧
      Graph.Executed initial actions .sharedCell 61 scanned manifest orders table ∧
      Legal table.toCandidate :=
  captured.build_legal orders

/-- Blocked-action and drain gaps do not become filtered-event ranks. Both RMWs
retain their actual predecessors, including the foreign-thread successor. -/
theorem acquiring_expectations :
    ∃ table, Graph.build inputs interfaceOrders = some table ∧
      Graph.Executed initial actions .sharedCell 61 scanned manifest interfaceOrders table ∧
      Legal table.toCandidate ∧
      table.sources = [none, none, some 1, some 2] ∧
      table.ranks = [0, 64, 65, 66] ∧
      ReadsFrom table.toCandidate 2 1 ∧ ReadsFrom table.toCandidate 3 2 := by
  obtain ⟨table, success, executed, legal⟩ := constructed interfaceOrders
  have same : table = GraphHappensBefore.ForeignRMW.table :=
    build_deterministic success table_actual
  subst table
  exact ⟨GraphHappensBefore.ForeignRMW.table, success, executed, legal,
    literal_mapping.1, literal_mapping.2.1, foreign_reads_store, observer_reads_foreign⟩

end ForeignRMW

namespace ForwardedLoads

/-- Equal zero words are not source identities. Both pending occurrences and
all real loads are retained in the raw successful scan. -/
theorem captured : Graph.Captured AccessSourceRanks.Loads.initial
    AccessSourceRanks.Loads.actions .sharedCell 10 AccessSourceRanks.Loads.scanned
    AccessGraphRanks.manifest where
  valid := AccessSourceRanks.Loads.initial_valid
  initialEmpty := AccessSourceRanks.Loads.initial_quiescent
  scanned := AccessSourceRanks.Loads.scanned_actual
  quiescent := by
    simpa only [AccessSourceRanks.Loads.result, AtomicTrace.Result.execution] using
      AccessSourceRanks.Loads.final_quiescent
  enumerated := AccessGraphRanks.manifest_actual

theorem constructed (orders : Orders) :
    ∃ table, Graph.build GraphHappensBefore.ForwardedLoads.inputs orders = some table ∧
      Graph.Executed AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
        .sharedCell 10 AccessSourceRanks.Loads.scanned AccessGraphRanks.manifest orders table ∧
      Legal table.toCandidate :=
  captured.build_legal orders

/-- The own load uses the newest pending occurrence, while the peer sees the
older already published occurrence. Equal payload bits cannot erase that split. -/
theorem acquiring_expectations :
    ∃ table, Graph.build GraphHappensBefore.ForwardedLoads.inputs
        GraphHappensBefore.ForwardedLoads.interfaceOrders = some table ∧
      Graph.Executed AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
        .sharedCell 10 AccessSourceRanks.Loads.scanned AccessGraphRanks.manifest
        GraphHappensBefore.ForwardedLoads.interfaceOrders table ∧
      Legal table.toCandidate ∧
      table.sources = [none, some 0, none, none, some 3, some 2, some 3] ∧
      table.ranks = [0, 0, 15, 18, 0, 0, 0] ∧
      ReadsFrom table.toCandidate 4 3 ∧ ReadsFrom table.toCandidate 5 2 ∧
      ¬ ReadsFrom table.toCandidate 4 2 ∧ ¬ ReadsFrom table.toCandidate 5 3 := by
  obtain ⟨table, success, executed, legal⟩ :=
    constructed GraphHappensBefore.ForwardedLoads.interfaceOrders
  have same : table = GraphHappensBefore.ForwardedLoads.table :=
    build_deterministic success GraphHappensBefore.ForwardedLoads.table_actual
  subst table
  exact ⟨GraphHappensBefore.ForwardedLoads.table, success, executed, legal,
    GraphHappensBefore.ForwardedLoads.literal_mapping.1,
    GraphHappensBefore.ForwardedLoads.literal_mapping.2.1,
    GraphHappensBefore.ForwardedLoads.forwarded_source,
    GraphHappensBefore.ForwardedLoads.peer_source,
    GraphHappensBefore.ForwardedLoads.equal_words_keep_distinct_sources⟩

end ForwardedLoads

namespace CrossCell

/-- Initialization is enumerated from both live cells, rather than a selected
object subset. The B RMW writes the same bits as initial B, after publishing A. -/
theorem captured : Graph.Captured WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
    .sharedCell 151 WriteViewRanks.Whole.scanned GraphOperationalCoherence.CrossCell.manifest where
  valid := WriteViewRanks.Whole.initial_valid
  initialEmpty := WriteViewRanks.Whole.initial_quiescent
  scanned := WriteViewRanks.Whole.scanned_actual
  quiescent := by
    simpa only [WriteViewRanks.Whole.result, AtomicTrace.Result.execution] using
      WriteViewRanks.Whole.final_quiescent
  enumerated := GraphOperationalCoherence.CrossCell.manifest_actual

theorem constructed (orders : Orders) :
    ∃ table, Graph.build GraphOperationalCoherence.CrossCell.inputs orders = some table ∧
      Graph.Executed WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
        .sharedCell 151 WriteViewRanks.Whole.scanned GraphOperationalCoherence.CrossCell.manifest
        orders table ∧ Legal table.toCandidate :=
  captured.build_legal orders

/-- The acquire must read the actual B RMW, despite its initial-equal bits.
Its synchronization carries the separate A publication into happens-before. -/
theorem acquiring_expectations :
    ∃ table, Graph.build GraphOperationalCoherence.CrossCell.inputs
        GraphHBCoherence.CrossCell.interfaceOrders = some table ∧
      Graph.Executed WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
        .sharedCell 151 WriteViewRanks.Whole.scanned GraphOperationalCoherence.CrossCell.manifest
        GraphHBCoherence.CrossCell.interfaceOrders table ∧
      Legal table.toCandidate ∧
      table.sources = [none, none, none, some 1, some 3, some 2] ∧
      table.ranks = [0, 0, 153, 154, 0, 0] ∧
      ReadsFrom table.toCandidate 4 3 ∧ ¬ ReadsFrom table.toCandidate 4 1 ∧
      HappensBefore table.toCandidate 2 5 := by
  obtain ⟨table, success, executed, legal⟩ :=
    constructed GraphHBCoherence.CrossCell.interfaceOrders
  have same : table = GraphHBCoherence.CrossCell.table :=
    build_deterministic success GraphHBCoherence.CrossCell.table_actual
  subst table
  exact ⟨GraphHBCoherence.CrossCell.table, success, executed, legal,
    GraphHBCoherence.CrossCell.literal_mapping.2.1,
    GraphHBCoherence.CrossCell.literal_mapping.2.2,
    GraphHBCoherence.CrossCell.B_acquire_source,
    GraphHBCoherence.CrossCell.unchanged_B_not_initial,
    GraphHBCoherence.CrossCell.publication_hb⟩

end CrossCell
end EDSL.Tests.GraphConstruction

#print axioms EDSL.Tests.GraphConstruction.ForeignRMW.captured
#print axioms EDSL.Tests.GraphConstruction.ForeignRMW.complete
#print axioms EDSL.Tests.GraphConstruction.ForeignRMW.constructed
#print axioms EDSL.Tests.GraphConstruction.ForeignRMW.acquiring_expectations
#print axioms EDSL.Tests.GraphConstruction.ForwardedLoads.captured
#print axioms EDSL.Tests.GraphConstruction.ForwardedLoads.constructed
#print axioms EDSL.Tests.GraphConstruction.ForwardedLoads.acquiring_expectations
#print axioms EDSL.Tests.GraphConstruction.CrossCell.captured
#print axioms EDSL.Tests.GraphConstruction.CrossCell.constructed
#print axioms EDSL.Tests.GraphConstruction.CrossCell.acquiring_expectations
#audit_edsl
