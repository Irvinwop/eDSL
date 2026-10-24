/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.Admission
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankBudget

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Per-slot progress for independently admitted counted calls. Each bound is the
positive measure of that slot's exact initial ghost, chosen before the actual
schedule. Arbitrary successful finite traces retain one collective checked
lift; the generic rank budget applies to those same endpoint witnesses.
Reaching the bound yields the actual returned worker. Empty queues follow
from caller-only closure of that same actual run.

Enabledness holds after any successful prefix for each current running slot
and either AF choice. It constructs one checked retiring step, without
assuming a future schedule, fairness, or a desired counter result. Bounds
count modeled own issues, not minimum instructions, native cycles or wall time.
The imported represented-memory, CET-off, protected-resource and translation
assumptions remain; this module alone does not inhabit the complete Claim.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Initial control is running at the existing checked entry, independently of
all future scheduling and AF choices. -/
theorem ghosts_running {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests)
    (slot : Fin before.workers.length) :
    ∃ (node : ((cohort pre).descriptor slot).graph.Index) (fuel : Nat),
      (ghosts pre slot).control = .running node fuel := by
  exact ⟨_, _, rfl⟩

/-- A bound selected from present inputs and entry ghosts before any trace. -/
noncomputable def ownIssueBounds {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests) :
    Fin before.workers.length → Nat := fun slot =>
  (ghosts pre slot).measure ((cohort pre).rankLaws slot).rank

/-- Even a zero-count call has a positive initial measure: its current running
entry invariant is positive and it must still retire its return path. -/
theorem ownIssueBounds_positive {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {before : TSO64.State} {requests : Spec.Requests before}
    (pre : Spec.Pre (image compiler) target cell before requests)
    (slot : Fin before.workers.length) : 0 < ownIssueBounds pre slot := by
  obtain ⟨node, _fuel, running⟩ := ghosts_running pre slot
  have invariant : ((cohort pre).rules slot).Inv node
      (ghosts pre slot).current (ghosts pre slot).history := by
    simpa only [Mixed.LocalRules.LocalAt, running] using (current pre slot).2
  have positive := ((cohort pre).rankLaws slot).positive invariant
  simpa only [ownIssueBounds, Mixed.Ghost.measure, running] using positive

/-- The full independent Claim.ownProgress obligation. A single positive
input-dependent bound works for every successful finite interleaving and AF
choice. The endpoint phase and empty queue describe the same actual worker. -/
theorem ownProgress (compiler : CounterCommon.Compiler) :
    ∀ (before : TSO64.State) (target : Atomics64.CellId64)
      (cell : Atomics64.Cell) (requests : Spec.Requests before),
      Spec.Pre (image compiler) target cell before requests →
      ∃ bounds : Fin before.workers.length → Nat,
        (∀ slot, 0 < bounds slot) ∧
        ∀ actions actual, schedule before actions .ownedOnly .arithmetic = .ok actual →
        ∀ slot : Fin before.workers.length,
          Mixed.ChoiceTrace.issues slot.val actions ≤ bounds slot ∧
          (bounds slot ≤ Mixed.ChoiceTrace.issues slot.val actions →
            ∃ worker, actual.1.workers[slot.val]? = some worker ∧
              worker.phase = .returned ∧ worker.pending = []) := by
  intro before target cell requests pre
  refine ⟨ownIssueBounds pre, ownIssueBounds_positive pre, ?_⟩
  intro actions actual run slot
  rcases actual with ⟨final, observations⟩
  obtain ⟨next, finalCurrent, trace, budgets⟩ :=
    (cohort pre).prefix_with_own_issue_budget pre.valid rfl (current pre) pre.empty run
  obtain ⟨finalEmpty, _finalCovered, _otherCurrent, _retiring⟩ :=
    (cohort pre).toCohort.schedule_from_current ((cohort pre).covers rfl)
      ((cohort pre).current_toCohort (current pre)) pre.empty run
  constructor
  · exact Nat.le_trans (Nat.le_add_right _ _) (budgets slot)
  · intro spent
    have threshold : (ghosts pre slot).measure ((cohort pre).rankLaws slot).rank ≤
        Mixed.ChoiceTrace.issues slot.val actions := spent
    obtain ⟨returned, _noIssue⟩ :=
      (cohort pre).returned_at_own_issue_budget rfl (current pre) pre.empty run
        trace finalCurrent slot threshold
    obtain ⟨worker, live, phase⟩ := returned
    exact ⟨worker, live, phase, finalEmpty worker (List.mem_of_getElem? live)⟩

/-- The full independent Claim.enabled obligation. Actual running control
excludes a retained done response; present ranked residuals then construct one
current retiring issue. This requires no selected or successful future suffix. -/
theorem enabled (compiler : CounterCommon.Compiler) :
    ∀ (before : TSO64.State) (target : Atomics64.CellId64)
      (cell : Atomics64.Cell) (requests : Spec.Requests before),
      Spec.Pre (image compiler) target cell before requests → ∀ actions actual,
      schedule before actions .ownedOnly .arithmetic = .ok actual →
      ∀ (slot : Fin before.workers.length) (worker : Worker),
      actual.1.workers[slot.val]? = some worker → worker.phase = .running → ∀ af,
      ∃ next, TSO64.step actual.1 (.issue slot.val af) .ownedOnly .arithmetic = .ok next ∧
        next.2.retired = 1 := by
  intro before target cell requests pre actions actual run slot worker live running af
  rcases actual with ⟨final, observations⟩
  obtain ⟨atCut, cutCurrent, _trace⟩ :=
    (cohort pre).prefix_from_current pre.valid (current pre) run
  obtain ⟨cutEmpty, _cutCovered, _otherCurrent, _retiring⟩ :=
    (cohort pre).toCohort.schedule_from_current ((cohort pre).covers rfl)
      ((cohort pre).current_toCohort (current pre)) pre.empty run
  have cutValid : WellFormed final .ownedOnly := schedule_wellFormed pre.valid run
  have cutCount : final.workers.length = before.workers.length := ScheduleTrace.workers_length run
  cases control : (atCut slot).control with
  | running node fuel =>
    obtain ⟨after, seen, _next, actualIssue, _afterValid, _afterCount,
      _afterEmpty, _afterCovered, _afterCurrent, _advanced, retiring, _smaller⟩ :=
      (cohort pre).enabled_step cutValid cutCount cutCurrent cutEmpty slot control af
    exact ⟨(after, seen), actualIssue, retiring.retired⟩
  | done response =>
    have zero : (atCut slot).measure ((cohort pre).rankLaws slot).rank = 0 := by
      simp only [Mixed.Ghost.measure, control]
    obtain ⟨saved, savedLive, savedPhase⟩ :=
      ((cohort pre).rankLaws slot).returned_of_measure_zero (cutCurrent slot) zero
    have atSlot : final.workers[slot.val]? = some saved := by
      simpa only [(cohort pre).tid_eq slot] using savedLive
    have same : worker = saved := Option.some.inj (live.symm.trans atSlot)
    have returned : worker.phase = .returned := (congrArg Worker.phase same).trans savedPhase
    have impossible : Phase.running = .returned := running.symm.trans returned
    cases impossible

#print axioms ghosts_running
#print axioms ownIssueBounds
#print axioms ownIssueBounds_positive
#print axioms ownProgress
#print axioms enabled

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
