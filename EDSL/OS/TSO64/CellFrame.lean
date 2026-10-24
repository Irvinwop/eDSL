/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.Audit

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Full RAM-cell preservation for actual issue-only production TSO64 schedules.
The target is a live initial registry entry. Every actual RMW observation must
name that target; its address follows from current checked authorization and
registry stability, rather than a supplied future operand-address premise.

The conclusion retains the whole optional AddressSpace.Cell, including stored
bytes behind inaccessible permissions, mappedness and every permission bit.
Ordinary issues (including buffered stores and RET) retain the shared world;
blocked issues retain the entire state. Only an RMW can change shared RAM in
an issue-only schedule. Drains are explicitly excluded, since their ordinary
or managed publications have a different footprint contract.

Both authority profiles and both RMW families are covered. Successful checked
execution supplies all authority needed by this conditional frame; no extra
WellFormed, quiescence, caller-only annotation or future frame is assumed.
Deriving the no-drain premise for a candidate belongs in its proof adapter,
not in an independent call-entry contract.

This is a finite modeled effect theorem. The imported coherent RAM, address,
stable-translation/no-hidden-alias and protected-resource model boundaries
remain in force; no native/physical-OS, source/compiler, lifetime, fairness,
termination, cost or corpus-acceptance result is supplied here.
-/

namespace EDSL.OS.TSO64.CellFrame
open X86

/-- Current checked authorization binds an actual RMW's observed cell identity
to its actual event address, without a world-invariant or address oracle. -/
theorem fetchAdd_address
    {before : World} {actor : Nat} {identifier : Atomics64.HandleId64}
    {delta : Word} {result : World × Atomics64.FetchAddEvent}
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : before.cells target = some cell)
    (selected : result.2.cell = target)
    (actual : Atomics64.fetchAdd before actor identifier delta = .ok result) :
    result.2.arithmetic.event.address = cell.address := by
  obtain ⟨handle, current, _handleLive, _actor, linked, _valid, eventCell, address⟩ :=
    Atomics64.fetchAdd_context _ _ _ _ _ actual
  have handleTarget : handle.cell = target := eventCell.symm.trans selected
  rw [handleTarget] at linked
  have same : current = cell := Option.some.inj (linked.symm.trans registered)
  exact address.trans (congrArg Atomics64.Cell.address same)

/-- One actual issue frames complete shared RAM cells outside its registered
target's qword. Every RMW label is checked, regardless of its tid or delta.
Ordinary enqueues change worker queues but do not publish their CPU memory. -/
theorem issue_frame
    {before : State} {tid : Nat} {af : Bool} {result : State × Observation}
    {profile : Profile} {family : RMWFamily}
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : before.world.cells target = some cell)
    (targets : ∀ thread event, result.2 = .rmw thread event → event.cell = target)
    (actual : TSO64.issue before tid af profile family = .ok result)
    (query : Word) (outside : ¬(AddressSpace.qwordRegion cell.address).Contains query) :
    result.1.world.legacy.shared.resources.space.cells query =
      before.world.legacy.shared.resources.space.cells query := by
  have stepped : TSO64.step before (.issue tid af) profile family = .ok result := actual
  cases step_origin stepped with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _executed finish =>
      cases finish <;> rfl
  | blocked => rfl
  | rmw _live _running _code _caller _fetched _bounds _empty _grant effect =>
    have arithmetic := RMWFamily.MachineEffect.arithmetic effect
    have address := fetchAdd_address registered (targets _ _ rfl) arithmetic.checked
    exact Atomics64.fetchAdd_frame _ _ _ _ _ arithmetic.checked query
      (by simpa only [address] using outside)

/-- Fold over the exact successful production schedule and its complete
observation list. No RMW is removed by a target/value filter. Current registry
stability is obtained from each actual step, preserving the initial descriptor
at every cut. The no-drain premise is solely a restriction on this effect trace.

No initial empty-FIFO premise is needed: buffered stores and blocked issues
are covered, as are empty schedules, zero-delta RMWs and repeated peer issues. -/
theorem schedule_frame
    {before : State} {actions : List Action} {result : State × List Observation}
    {profile : Profile} {family : RMWFamily}
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : before.world.cells target = some cell)
    (noDrains : ∀ thread, Action.drain thread ∉ actions)
    (targets : ∀ thread event, Observation.rmw thread event ∈ result.2 → event.cell = target)
    (actual : TSO64.schedule before actions profile family = .ok result)
    (query : Word) (outside : ¬(AddressSpace.qwordRegion cell.address).Contains query) :
    result.1.world.legacy.shared.resources.space.cells query =
      before.world.legacy.shared.resources.space.cells query := by
  induction actions generalizing before result with
  | nil =>
    have same : (before, []) = result := Except.ok.inj actual
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨head, tail, stepped, following, same⟩ := schedule_cons_ok actual
    have headTargets : ∀ thread event, head.2 = .rmw thread event → event.cell = target := by
      intro thread event label
      apply targets thread event
      rw [same, label]
      exact List.mem_cons_self
    have tailTargets : ∀ thread event, .rmw thread event ∈ tail.2 → event.cell = target := by
      intro thread event member
      apply targets thread event
      rw [same]
      exact List.mem_cons_of_mem head.2 member
    have headFrame : head.1.world.legacy.shared.resources.space.cells query =
        before.world.legacy.shared.resources.space.cells query := by
      cases action with
      | issue thread choice =>
        exact issue_frame registered headTargets stepped query outside
      | drain thread =>
        exact False.elim (noDrains thread List.mem_cons_self)
    have middleRegistered : head.1.world.cells target = some cell := by
      rw [(step_stable stepped).cells]
      exact registered
    have tailNoDrains : ∀ thread, Action.drain thread ∉ rest := by
      intro thread member
      exact noDrains thread (List.mem_cons_of_mem action member)
    have tailFrame := ih middleRegistered tailNoDrains tailTargets following
    rw [same]
    exact tailFrame.trans headFrame

#print axioms fetchAdd_address
#print axioms issue_frame
#print axioms schedule_frame

end EDSL.OS.TSO64.CellFrame

#audit_edsl
