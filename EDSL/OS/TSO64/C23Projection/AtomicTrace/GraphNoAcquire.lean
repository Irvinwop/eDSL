/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphCoherence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphWellFormed

/-!
Universal finite atomic-fragment legality for actual mapped scans whose
explicit interface annotations have no acquiring access. This includes the
all-relaxed interface. The check inspects declared annotations, not machine
bytes; it neither infers source intent nor silently weakens an acquiring order.

Every mapped graph is proved legal using actual execution constraints and
structural correspondence, without running the graph legality checker or
assuming its success. Initialization-manifest provenance, graph-build totality,
source preservation, physical CPU/Linux refinement and fairness remain separate.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace

/-- Canonical explicitly declared relaxed primitive/interface annotations. -/
def Orders.relaxed : Orders where
  read _ _ := .relaxed
  write _ _ := .relaxed
  rmw _ _ := .relaxed

/-- A finite check on actual event annotations. A false result establishes no
program defect; it leaves synchronization and HB proof obligations open. -/
def Orders.noAcquire (orders : Orders) (events : List Event) : Bool :=
  events.all (fun event => !(event.toSource orders).access.acquires)

theorem Orders.noAcquire_relaxed (events : List Event) :
    Orders.relaxed.noAcquire events = true := by
  apply List.all_eq_true.mpr
  intro event _member
  cases event with
  | mk position tid access => cases access <;> rfl

namespace Graph.Executed
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}
  {orders : Orders} {table : Graph.Table}

/-- The checked annotation condition excludes every acquiring graph row,
including out-of-domain rows. Initializers never acquire. -/
theorem no_acquires
    (executed : Graph.Executed initial actions profile offset run initials orders table)
    (checked : orders.noAcquire run.events = true) (index : Nat) :
    ¬ Concurrency.C23Atomic.Acquires table.toCandidate index := by
  rintro ⟨node, live, acquired⟩
  rcases executed.row_cases live with boundary | actual
  · obtain ⟨slot, _index, same⟩ := boundary
    rw [same] at acquired
    cases acquired
  · obtain ⟨slot, _index, same⟩ := actual
    have absent := List.all_eq_true.mp checked run.events[slot.val] (List.getElem_mem slot.isLt)
    rw [same] at acquired
    change (!(run.events[slot.val].toSource orders).access.acquires) = true at absent
    rw [acquired] at absent
    cases absent

/-- All four coherence conditions, HB acyclicity, no-future RF and RMW
predecessors for every graph row follow from one actual structurally mapped
scan and a successful finite no-acquire annotation check. No legality or
coherence oracle is supplied by the caller. -/
theorem legal_without_acquire
    (executed : Graph.Executed initial actions profile offset run initials orders table)
    (checked : orders.noAcquire run.events = true) :
    Concurrency.C23Atomic.Legal table.toCandidate := by
  exact Concurrency.C23Atomic.legal_of_no_synchronization executed.mapped.wellFormed
    executed.sequencedCoherent
    (fun _ reader edge => executed.no_acquires checked reader edge.1)
    (fun edge => executed.noFutureSequenced edge)
    (fun rmw edge => executed.rmwPredecessor rmw edge)

/-- Every actual graph mapped under the declared all-relaxed interface has
finite atomic-fragment legality, without a per-program legality-check proof. -/
theorem relaxed_legal
    (executed : Graph.Executed initial actions profile offset run initials Orders.relaxed table) :
    Concurrency.C23Atomic.Legal table.toCandidate :=
  executed.legal_without_acquire (Orders.noAcquire_relaxed run.events)

end Graph.Executed
end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
