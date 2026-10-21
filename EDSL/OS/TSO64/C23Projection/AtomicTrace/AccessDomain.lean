/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Capture
import EDSL.OS.TSO64.ExecutionViews.Transport

/-!
Managed access domains derived from actual scheduler origins. Loads and stores
retain their complete selected reference; RMWs authenticate the actual handle,
persistent cell and operand address using checked current authorization.
Neither a registered cell nor an address alone supplies this authority.

The real access prestate transports its worker and complete resource record
back to the initial state. A fixed well-formed, sequenced successful execution
with a quiescent endpoint then supplies a view at every cut, including cuts
beyond the action list. Incoming queues and writer maps remain explicit
boundaries. View existence authenticates the access domain, not the provenance
of an arbitrary incoming writer map or source-language memory orders.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86

/-- Relate an actual access to its exact authority target. Loads and stores
require their original complete reference. RMW observations carry the handle
identifier, persistent cell and arithmetic address rather than a full reference.
Current authorization of the recovered descriptor is a separate conjunct in
`AtomicStep.authority`. -/
def AccessTarget (event : Event) (target : Queue.ManagedRef) : Prop :=
  target.handle.cell = event.object ∧
    match event.access with
    | .load reference .. | .store reference .. => target = reference
    | .rmw changed _ => target.identifier = changed.handle ∧
        target.cell.address = changed.arithmetic.event.address

/-- Recover authority from the actual load selection, committed store admission
or guarded RMW. No world invariant, graph, view, quiescence or source legality
premise is needed to establish the real worker's current access authority. -/
theorem AtomicStep.authority
    {state : State} {action : Action} {first : State × Observation}
    {profile : Profile} {position : Nat} {writers : PublishedHistory.Writers}
    {event : Event}
    (actual : AtomicStep state action first profile position writers event) :
    ∃ worker target, state.workers[event.tid]? = some worker ∧
      Queue.Current state.world worker.resources target ∧ AccessTarget event target := by
  cases actual with
  | load origin _live _read =>
      cases origin with
      | intro _issuing live _fetched _effect _shared _ordinaryAbsent _selected current
          _operand _loaded =>
          exact ⟨_, _, live, current, rfl, rfl⟩
  | store issued =>
      cases issued with
      | ordinary _issuing _success live _fetched _effect _intent admission _committed =>
          exact ⟨_, _, live, admission.valid.2, rfl, rfl⟩
  | rmw observed origin =>
      cases origin with
      | ordinary _live _running _code _caller _fetched effect =>
          cases effect with
          | intro _supported _bounds _decoded _reads _queue _executed finish =>
              cases finish <;> cases observed
      | blocked => cases observed
      | rmw live _running _code _caller _fetched _bounds _empty grant effect =>
          cases observed
          obtain ⟨handle, cell, authorized, shape, _mutation⟩ :=
            Atomics64.fetchAdd_guarded _ _ _ _ _ effect.checked
          have identity :=
            Atomics64.fetchAdd_identity _ _ _ _ _ handle cell effect.checked authorized
          refine ⟨_, ⟨_, handle, cell⟩, live, ⟨grant, authorized⟩, ?_⟩
          exact ⟨identity.1.symm, (congrArg Atomics64.FetchAddEvent.handle shape).symm,
            identity.2.symm⟩
      | drained => cases observed

/-- An actual event authenticates its target using an actual initial worker's
unchanged resource record. Backward transport uses the real prefix, preserving
the full descriptor and the event's original thread slot. -/
theorem EventAt.initial_authority
    {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {incoming : PublishedHistory.Writers}
    (actual : EventAt profile event index initial actions result offset incoming) :
    ∃ original target, initial.workers[event.tid]? = some original ∧
      Queue.Current initial.world original.resources target ∧ AccessTarget event target := by
  obtain ⟨_before, _action, _first, prefixRun, _selected, _observed, _executed, origin⟩ :=
    actual.prestate
  obtain ⟨_worker, target, live, current, related⟩ := origin.authority
  obtain ⟨original, originalLive, resources⟩ :=
    ExecutionViews.schedule_worker_origin prefixRun live
  rw [resources] at current
  exact ⟨original, target, originalLive,
    (ExecutionViews.schedule_current_iff prefixRun original.resources target).mp current, related⟩

/-- Every real access has an execution-derived view at every cut. The access
itself supplies the domain and initial worker authority; the execution supplies
the successful finite run, invariants, sequencing and final publication bound.
Offsets and incoming maps are retained without extra boundary authentication. -/
theorem EventAt.views
    {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {event : Event} {index offset : Nat} {incoming : PublishedHistory.Writers}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset incoming)
    (cut : Nat) :
    ∃ target value, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile cut event.tid
        target offset incoming value) := by
  obtain ⟨_original, target, live, current, related⟩ := actual.initial_authority
  obtain ⟨value, view⟩ :=
    ExecutionViews.exists_at execution live cut current offset incoming
  exact ⟨target, value, related, view⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
