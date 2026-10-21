/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphAccess
import EDSL.OS.TSO64.C23Projection.AtomicTrace.AccessDomain

/-!
Raw scan and initialization evidence for constructing an atomic graph.
No graph table, structural mapping, source/rank metadata or semantic legality
is a premise. The empty initial queue boundary matches `AtomicTrace.verify`;
more general incoming FIFO boundaries require a separate construction theorem.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open PublishedHistory

/-- Actual initialized resources, successful scanning and closed queue endpoints,
before constructing any graph table or choosing declared interface orders. -/
structure Captured (initial : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (run : Result) (initials : List Initials.Entry) : Prop where
  valid : WellFormed initial profile
  initialEmpty : Quiescent initial
  scanned : scan initial actions profile offset empty = .ok run
  quiescent : Quiescent run.state
  enumerated : Initials.enumerate initial.world = .ok initials

namespace Captured
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}

theorem sequenced (captured : Captured initial actions profile offset run initials) :
    Sequenced initial := quiescent_sequenced captured.initialEmpty

theorem certificate (captured : Captured initial actions profile offset run initials) :
    Certificate initial actions profile offset empty run :=
  scan_certificate captured.valid captured.sequenced captured.scanned

theorem execution (captured : Captured initial actions profile offset run initials) :
    ExecutionViews.Execution initial actions run.execution profile :=
  ⟨captured.certificate.scheduled, captured.valid, captured.sequenced, captured.quiescent⟩

theorem event_origin (captured : Captured initial actions profile offset run initials)
    (slot : Fin run.events.length) :
    ∃ index, EventAt profile run.events[slot.val] index initial actions run.execution offset empty :=
  (captured.certificate.events _).mp (List.getElem_mem slot.isLt)

theorem publication_origin (captured : Captured initial actions profile offset run initials)
    {stamp : Stamp} (member : stamp ∈ writes offset run.observations) :
    Nonempty (WriteAt initial actions run.execution profile offset stamp) :=
  writes_origin captured.certificate.scheduled member

theorem manifest_unique (captured : Captured initial actions profile offset run initials) :
    (initials.map Initials.Entry.identifier).Nodup :=
  Initials.enumerate_identifiers_nodup captured.enumerated

/-- Every live initial descriptor has an enumerated row. The word is obtained
by reading the actual well-formed initial world, rather than supplied by a caller. -/
theorem manifest_cell (captured : Captured initial actions profile offset run initials)
    {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    (live : initial.world.cells identifier = some cell) :
    ∃ slot : Fin initials.length,
      initials[slot.val].identifier = identifier ∧ initials[slot.val].cell = cell := by
  obtain ⟨value, read⟩ := (captured.valid.1.cells identifier cell live).2.1.load_exists
  have member := Initials.enumerate_complete captured.valid.1 captured.enumerated live read
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, equal⟩ := List.getElem_of_getElem? selected
  exact ⟨⟨index, bound⟩, by rw [equal], by rw [equal]⟩

/-- Actual access authorization supplies the initial manifest boundary for
each scanned event, including the complete plain-access descriptor. -/
theorem event_boundary (captured : Captured initial actions profile offset run initials)
    (slot : Fin run.events.length) :
    AtBoundary (runInputs initials run offset) run.events[slot.val] := by
  obtain ⟨index, actual⟩ := captured.event_origin slot
  obtain ⟨worker, target, _live, current, related⟩ := actual.initial_authority
  have registered := (Atomics64.authorize_ok initial.world worker.resources.actor
    target.identifier (target.handle, target.cell) current.2).2.2.1
  obtain ⟨boundary, identifier, descriptor⟩ := captured.manifest_cell registered
  cases access : run.events[slot.val].access with
  | load reference value source =>
      have same : target = reference := by simpa only [access] using related.2
      subst target
      simp only [AtBoundary, access, runInputs]
      exact ⟨boundary, identifier.symm, descriptor.symm⟩
  | store reference value occurrence =>
      have same : target = reference := by simpa only [access] using related.2
      subst target
      simp only [AtBoundary, access, runInputs]
      exact ⟨boundary, identifier.symm, descriptor.symm⟩
  | rmw changed source =>
      have object : target.handle.cell = changed.cell := by
        simpa only [Event.object, access] using related.1
      have details : target.identifier = changed.handle ∧
          target.cell.address = changed.arithmetic.event.address := by
        simpa only [access] using related.2
      simp only [AtBoundary, access, runInputs]
      exact ⟨boundary, object.symm.trans identifier.symm,
        details.2.symm.trans (congrArg Atomics64.Cell.address descriptor).symm⟩

/-- The observation-position enumeration never emits duplicate positions.
This is independent of values, interface orders and graph construction. -/
theorem publication_positions
    (_captured : Captured initial actions profile offset run initials) :
    ((writes offset run.observations).map (fun stamp => stamp.position)).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  exact (writes_ordered offset run.observations).imp (fun less same => by
    rw [same] at less
    exact Nat.lt_irrefl _ less)

end Captured
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
