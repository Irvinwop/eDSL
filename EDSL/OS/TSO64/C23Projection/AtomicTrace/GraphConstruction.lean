/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphComplete
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphInputOrigins
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphHBCoherence

/-!
Constructing a finite atomic graph from actual initialized execution evidence.
Every input adequacy obligation is derived from `Captured`: no caller supplies
writer/source/rank metadata, a graph table, builder acceptance or legality.
The existing executable builder and its structural checks are unchanged.

This construction has empty initial and final queues, stable initialized cells,
a successful production scan and explicit well-formed resources. Offsets and
typed interface orders are arbitrary. Legality concerns the modeled finite
atomic fragment; it does not establish full C23, compiler preservation, native
CPU/kernel behavior, fairness or a successful separate legality-checker run.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph.Captured
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}

/-- Derive all finite builder requirements from actual scan and initialization
origins. In particular, source values are authenticated independently of ranks. -/
theorem inputs_ready (captured : Captured initial actions profile offset run initials)
    (orders : Orders) : InputsReady (runInputs initials run offset) orders where
  writerKeys := captured.writer_keys
  publicationKeys := captured.publication_keys
  publicationPositions := captured.publication_positions
  boundary := captured.event_boundary
  reads := captured.read_source orders
  writes := captured.event_publication
  complete := captured.publication_event

/-- The existing executable builder succeeds from raw actual execution evidence,
and its output has the structural correspondence required by execution proofs. -/
theorem build_complete (captured : Captured initial actions profile offset run initials)
    (orders : Orders) :
    ∃ table, build (runInputs initials run offset) orders = some table ∧
      Executed initial actions profile offset run initials orders table := by
  obtain ⟨table, success, mapped⟩ := Graph.build_complete (captured.inputs_ready orders)
  exact ⟨table, success, captured.valid, captured.sequenced, captured.scanned,
    captured.quiescent, mapped⟩

/-- Actual initialized scans construct a graph whose modeled finite-fragment
legality follows from execution, without a caller-supplied graph or checker oracle. -/
theorem build_legal (captured : Captured initial actions profile offset run initials)
    (orders : Orders) :
    ∃ table, build (runInputs initials run offset) orders = some table ∧
      Executed initial actions profile offset run initials orders table ∧
      Concurrency.C23Atomic.Legal table.toCandidate := by
  obtain ⟨table, success, executed⟩ := captured.build_complete orders
  exact ⟨table, success, executed, executed.legal⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph.Captured

#audit_edsl
