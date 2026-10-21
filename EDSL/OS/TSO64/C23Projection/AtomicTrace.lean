/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
import EDSL.OS.TSO64.C23Projection.AtomicTrace.SourceOrigins
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.PublicationViews
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ViewTransfer
import EDSL.OS.TSO64.C23Projection.AtomicTrace.RMWPredecessor
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Coherence

/-!
Checked finite atomic graphs from actual executions. The executable interface
enumerates all live initialized cells, runs the production scheduler with access
annotations, derives every publication, builds identity-based RF and modification
metadata, and invokes the proved C23 atomic-fragment checker.

Successful certification concerns the supplied finite schedule and declared
typed interface orders. It is not universal TSO-to-C23 preservation, a compiler
preservation theorem, a native CPU/Linux model, or a liveness result. World and
resource well-formedness remain explicit premises of the execution-origin
theorem. Empty initial/final queues are checked, not silently assumed. Initialization
is an already-initialized stable-object boundary, not C object lifecycle semantics.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace

inductive Failure where
  | initialQueues
  | initialRead (fault : Fault)
  | execution (fault : Fault)
  | finalQueues
  | mapping
  | legality
  deriving DecidableEq, Repr

structure Output where
  initials : List Initials.Entry
  run : Result
  table : Graph.Table

def Output.inputs (output : Output) : Graph.Inputs :=
  ⟨output.initials, output.run.events, writes 0 output.run.observations⟩

def emptyQueues (state : State) : Bool :=
  state.workers.all (fun worker => worker.pending.isEmpty)

theorem emptyQueues_iff (state : State) : emptyQueues state = true ↔ Quiescent state := by
  simp only [emptyQueues, List.all_eq_true, List.isEmpty_iff, Quiescent]

/-- Extract and check a graph, without accepting a graph, RF table, initial
value manifest, publication history or legality proof from the caller. Orders
are declared primitive/interface annotations; MOV bytes do not establish them.
Failures distinguish execution faults, open queue boundaries, mapping rejection
and C23 graph rejection. No failure establishes a defect in the input program. -/
def verify (initial : State) (actions : List Action) (orders : Orders)
    (profile : Profile := .sharedCell) : Except Failure Output :=
  if emptyQueues initial then
    match Initials.enumerate initial.world with
    | .error fault => .error (.initialRead fault)
    | .ok initials =>
        match scan initial actions profile 0 PublishedHistory.empty with
        | .error fault => .error (.execution fault)
        | .ok run =>
            if emptyQueues run.state then
              match Graph.build ⟨initials, run.events, writes 0 run.observations⟩ orders with
              | none => .error .mapping
              | some table =>
                  if Concurrency.C23Atomic.Check.certify table then
                    .ok ⟨initials, run, table⟩
                  else .error .legality
            else .error .finalQueues
  else .error .initialQueues

/-- Independently stated correspondence for successful results. The initial
manifest covers every live registry descriptor and exact initial RAM value;
the scanner covers every actual managed access; RF keys resolve to actual
prefix origins; publication ranks and graph rows satisfy `Graph.Built`; and
the independent C23 atomic-fragment legality predicate holds. -/
structure Verification (initial : State) (actions : List Action) (orders : Orders)
    (profile : Profile) (output : Output) : Prop where
  initialEmpty : Quiescent initial
  finalEmpty : Quiescent output.run.state
  initials : ∀ entry, entry ∈ output.initials ↔
    initial.world.cells entry.identifier = some entry.cell ∧
      X86.loadQWord (published initial.world) entry.cell.address = .ok entry.value
  execution : AtomicTrace.Certificate initial actions profile 0 PublishedHistory.empty output.run
  sources : ∀ event, event ∈ output.run.events →
    OriginAt initial actions output.run.execution profile event
  graph : Graph.Built output.inputs orders output.table
  legal : Concurrency.C23Atomic.Legal output.table.toCandidate

private theorem verify_parts {initial : State} {actions : List Action} {orders : Orders}
    {profile : Profile} {output : Output}
    (success : verify initial actions orders profile = .ok output) :
    emptyQueues initial = true ∧ emptyQueues output.run.state = true ∧
      Initials.enumerate initial.world = .ok output.initials ∧
      scan initial actions profile 0 PublishedHistory.empty = .ok output.run ∧
      Graph.Built output.inputs orders output.table ∧
      Concurrency.C23Atomic.Legal output.table.toCandidate := by
  by_cases before : emptyQueues initial = true
  · cases enumerated : Initials.enumerate initial.world with
    | error fault => simp [verify, before, enumerated] at success
    | ok initials =>
        cases scanned : scan initial actions profile 0 PublishedHistory.empty with
        | error fault => simp [verify, before, enumerated, scanned] at success
        | ok run =>
            by_cases after : emptyQueues run.state = true
            · cases built : Graph.build ⟨initials, run.events, writes 0 run.observations⟩ orders with
              | none => simp [verify, before, enumerated, scanned, after, built] at success
              | some table =>
                  by_cases checked : Concurrency.C23Atomic.Check.certify table = true
                  · have same : (⟨initials, run, table⟩ : Output) = output := by
                      simpa only [verify, before, enumerated, scanned, after, built, checked,
                        Bool.true_eq, ↓reduceIte, Except.ok.injEq] using success
                    subst output
                    exact ⟨before, after, rfl, rfl, Graph.build_sound built,
                      Concurrency.C23Atomic.Check.certify_sound table checked⟩
                  · simp [verify, before, enumerated, scanned, after, built, checked] at success
            · simp [verify, before, enumerated, scanned, after] at success
  · simp [verify, before] at success

/-- Certification joins actual execution, complete input enumeration, real
source origins, graph correspondence and legality. No caller-supplied graph
classification, coherence premise or history oracle appears in the contract. -/
theorem verify_sound {initial : State} {actions : List Action} {orders : Orders}
    {profile : Profile} {output : Output}
    (valid : WellFormed initial profile)
    (success : verify initial actions orders profile = .ok output) :
    Verification initial actions orders profile output := by
  obtain ⟨before, after, enumerated, scanned, mapped, legal⟩ := verify_parts success
  have empty := (emptyQueues_iff initial).mp before
  exact ⟨empty, (emptyQueues_iff output.run.state).mp after,
    fun entry => Initials.enumerate_live_iff valid.1 enumerated entry,
    scan_certificate valid (quiescent_sequenced empty) scanned,
    fun _ member => scan_source_origins valid empty scanned member, mapped, legal⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace
