/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort
import EDSL.OS.TSO64.Stability
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Published-byte frames for actual finite schedules of independently annotated
caller-only cohorts. The initial registry names the common cell independently
of execution. Observed RMWs need only name that cell's identifier: their actual
operand addresses follow from checked OS authorization and registry stability.
Both the authority profile and the supported arithmetic instruction family
remain those of the actual schedule.

Ordinary and RET steps consume current typed checked issue evidence to retain
the world. Cohort closure derives empty queues at each actual intermediate
state, excluding drains without a future FIFO or no-enqueue premise. Native
RMW steps use the actual production machine effect's eight-byte frame.

Entries retain the imported long-mode/CET-off, coherent WB RAM, stable
translation/no-alias, ownership, protected-loan and synchronization contracts.
This is conditional finite-run byte preservation, with no enabledness,
termination, source/compiler refinement or physical-hardware claim.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

variable {ι : Type} {profile : Profile} {family : RMWFamily}

/-- The address of an actual checked RMW is determined by its current cell
registry and observed cell identity, rather than an assumed operand address. -/
theorem registered_rmw_address
    {before : World} {actor : Nat} {identifier : Atomics64.HandleId64}
    {initial : X86.State} {instruction : family.Instruction}
    {result : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    (effect : family.MachineEffect before actor identifier initial instruction result machine)
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : before.cells target = some cell) (selected : result.2.cell = target) :
    result.2.arithmetic.event.address = cell.address := by
  obtain ⟨handle, current, _handleLive, _actor, linked, _valid, eventCell, address⟩ :=
    (RMWFamily.MachineEffect.arithmetic effect).context
  have handleTarget : handle.cell = target := eventCell.symm.trans selected
  rw [handleTarget] at linked
  have same : current = cell := Option.some.inj (linked.symm.trans registered)
  exact address.trans (congrArg Atomics64.Cell.address same)

private theorem ordinary_frame_labels
    {before : S} {tid : Nat} {worker : Worker} {instruction : Sequential.Instruction}
    {af : Bool} {result : S × O} {profile : Profile}
    (effect : OrdinaryEffect before tid worker instruction af result profile) :
    result.2 = .ordinary tid ∨ result.2 = .returned tid := by
  cases effect with
  | intro _supported _bounds _decoded _reads _queue _executed finish =>
    cases finish with
    | next => exact Or.inl rfl
    | returned => exact Or.inr rfl

/-- One actual byte frame. The current annotations supply checked caller-only
world equality; the actual RMW effect supplies both authority and byte framing.
Current empty queues exclude blocked issues and successful drains. -/
theorem Cohort.step_frame (cohort : Cohort ι profile family)
    {initial before after : S} {action : Action} {seen : O}
    (covered : cohort.Covers before) (current : cohort.Current initial before)
    (empty : Quiescent before)
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : before.world.cells target = some cell)
    (targets : ∀ tid event, seen = .rmw tid event → event.cell = target)
    (actual : TSO64.step before action profile family = .ok (after, seen))
    (query : Word) (outside : 8 ≤ (query - cell.address).toNat) :
    (published after.world).read query = (published before.world).read query := by
  cases action with
  | issue tid af =>
    cases step_origin actual with
    | ordinary live _running _code _caller _fetched effect =>
      have labels := ordinary_frame_labels effect
      obtain ⟨subject, subjectTid⟩ := covered tid _ live
      obtain ⟨_ghost, related⟩ := current subject
      have selected : TSO64.step before (.issue (cohort.descriptor subject).tid af)
          (cohort.descriptor subject).profile (cohort.descriptor subject).family =
            .ok (after, seen) := by
        simpa only [subjectTid, cohort.profile_eq subject, cohort.family_eq subject] using actual
      have ownLabels : seen = .ordinary (cohort.descriptor subject).tid ∨
          seen = .returned (cohort.descriptor subject).tid := by
        simpa only [subjectTid] using labels
      have preserved := (cohort.annotations subject).callerOnly_preserves_of_step
        related selected ownLabels (cohort.callerPolicy subject before)
        (by simpa only [subjectTid] using live)
      rw [preserved.1]
    | blocked live _running _code _caller _fetched _bounds nonempty =>
      exact False.elim (nonempty (empty _ (List.mem_of_getElem? live)))
    | rmw _live _running _code _caller _fetched _bounds _ownEmpty _grant effect =>
      have address := registered_rmw_address effect registered (targets _ _ rfl)
      have arithmetic := RMWFamily.MachineEffect.arithmetic effect
      have framed := arithmetic.frame query (by simpa only [address] using outside)
      rw [arithmetic.memory] at framed
      exact framed
  | drain _tid =>
    cases step_origin actual with
    | drained live fifo _gate _changed _effect =>
      have ownEmpty := empty _ (List.mem_of_getElem? live)
      rw [ownEmpty] at fifo
      cases fifo

/-- Fold byte preservation over the same actual steps as cohort closure.
The current registered descriptor is transported by production stability;
there is no assumed future address, byte frame or empty-FIFO oracle. -/
theorem Cohort.schedule_frame_from_current (cohort : Cohort ι profile family)
    {initial before final : S} {actions : List Action} {observations : List O}
    (covered : cohort.Covers before) (current : cohort.Current initial before)
    (empty : Quiescent before)
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : before.world.cells target = some cell)
    (targets : ∀ tid event, .rmw tid event ∈ observations → event.cell = target)
    (actual : TSO64.schedule before actions profile family = .ok (final, observations))
    (query : Word) (outside : 8 ≤ (query - cell.address).toNat) :
    (published final.world).read query = (published before.world).read query := by
  induction actions generalizing before final observations with
  | nil =>
    have same : (before, []) = (final, observations) := Except.ok.inj actual
    have finalEq : before = final := congrArg Prod.fst same
    rw [← finalEq]
  | cons action rest ih =>
    obtain ⟨⟨middle, seen⟩, ⟨last, tail⟩, stepped, scheduled, same⟩ :=
      schedule_cons_ok actual
    have observationsEq : observations = seen :: tail := congrArg Prod.snd same
    have headTargets : ∀ tid event, seen = .rmw tid event → event.cell = target := by
      intro tid event label
      apply targets tid event
      rw [observationsEq, label]
      exact List.mem_cons_self
    have tailTargets : ∀ tid event, .rmw tid event ∈ tail → event.cell = target := by
      intro tid event member
      apply targets tid event
      rw [observationsEq]
      exact List.mem_cons_of_mem seen member
    have headFrame := cohort.step_frame covered current empty registered headTargets stepped query outside
    obtain ⟨middleEmpty, middleCovered, middleCurrent, _retiring⟩ :=
      cohort.step_closed covered current empty stepped
    have middleRegistered : middle.world.cells target = some cell := by
      rw [(step_stable stepped).cells]
      exact registered
    have tailFrame := ih middleCovered middleCurrent middleEmpty middleRegistered tailTargets scheduled
    have finalEq : final = last := congrArg Prod.fst same
    rw [finalEq]
    exact tailFrame.trans headFrame

/-- Initial-state API: independent Entries, exhaustive initial slot coverage,
empty initial queues and actual observed cell targets yield a universal frame
on final published RAM outside the registered cell's modular eight-byte span. -/
theorem Cohort.schedule_frame (cohort : Cohort ι profile family)
    {initial final : S} {actions : List Action} {observations : List O}
    (covered : cohort.Covers initial) (entries : cohort.Entries initial)
    (empty : Quiescent initial)
    {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (registered : initial.world.cells target = some cell)
    (targets : ∀ tid event, .rmw tid event ∈ observations → event.cell = target)
    (actual : TSO64.schedule initial actions profile family = .ok (final, observations)) :
    ∀ query : Word, 8 ≤ (query - cell.address).toNat →
      (published final.world).read query = (published initial.world).read query :=
  cohort.schedule_frame_from_current covered (cohort.current_of_entries entries) empty
    registered targets actual

#print axioms registered_rmw_address
#print axioms ordinary_frame_labels
#print axioms Cohort.step_frame
#print axioms Cohort.schedule_frame_from_current
#print axioms Cohort.schedule_frame

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
