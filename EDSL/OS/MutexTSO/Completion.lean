/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Outcome
import EDSL.OS.MutexTSO.Publication

namespace EDSL.OS.MutexTSO
open X86

/-- Publish the selected FIFO, then execute its next actual instruction.
The logical step is used as an internal construction witness; physical
success, exact events and the complete related state are conclusions. -/
theorem realize_dispatch {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {identifier : Nat} {checkedResult : Logical × Option AtomicEvent}
    (checked : MutexReplay.dispatch logical identifier = .ok checkedResult) :
    ∃ actions result,
      TSO.schedule physical actions = .ok result ∧ Rel config result.1 checkedResult.1 ∧
      retiredSelections result.2 = [identifier] ∧
      TSO.atomicEvents result.2 = MutexReplay.recordEvent identifier checkedResult.2 [] ∧
      blockedCount result.2 = 0 := by
  obtain ⟨worker, output, logicalLive, advanced, _⟩ := MutexReplay.dispatch_ok _ _ _ checked
  have unfinished := MutexReplay.advance_unfinished _ _ _ _ advanced
  obtain ⟨before, live, _, marked⟩ := related.logical_live logicalLive
  have running : before.returned = false := by simp [marked, unfinished]
  obtain ⟨published, current, publishedOk, publishedRel, found, empty, _, currentReturned,
    selections, _, events, blocked⟩ := publish_selected related live
  obtain ⟨after, logicalAfter, event, issued, replayed, afterRel⟩ :=
    issue_retiring_if_own_empty publishedRel closed found (currentReturned.trans running) empty
  have same := Except.ok.inj (replayed.symm.trans checked)
  have singleton : TSO.schedule published.1 [.issue identifier] =
      .ok (after, [.retired identifier event]) := by simp [TSO.schedule, TSO.step, issued]
  refine ⟨List.replicate before.buffer.length (.drain identifier) ++ [.issue identifier],
    (after, published.2 ++ [.retired identifier event]),
    TSO.schedule_append _ _ _ _ _ publishedOk singleton, ?_, ?_, ?_, ?_⟩
  · simpa only [← congrArg Prod.fst same] using afterRel
  · rw [retiredSelections_append, selections]
    rfl
  · rw [atomicEvents_append, events]
    have eventEq := congrArg Prod.snd same
    cases event <;> simp [TSO.atomicEvents, MutexReplay.recordEvent, ← eventEq]
  · rw [blockedCount_append, blocked]
    rfl

/-- A successful logical construction can be realized by actual FIFO drains
and user issues. Each logical instruction retires exactly once; publication
adds no busy exchanges or stalls. -/
theorem realize_schedule {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {selections : List Nat} {checkedResult : Logical × List (Nat × AtomicEvent)}
    (checked : MutexReplay.schedule logical selections = .ok checkedResult) :
    ∃ actions result,
      TSO.schedule physical actions = .ok result ∧ Rel config result.1 checkedResult.1 ∧
      retiredSelections result.2 = selections ∧ TSO.atomicEvents result.2 = checkedResult.2 ∧
      blockedCount result.2 = 0 := by
  induction selections generalizing physical logical checkedResult with
  | nil =>
    simp [MutexReplay.schedule] at checked
    cases checked
    exact ⟨[], (physical, []), rfl, related, rfl, rfl, rfl⟩
  | cons identifier rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := MutexReplay.schedule_cons_ok _ _ _ _ checked
    obtain ⟨firstActions, firstResult, issued, middleRel, firstSelections, firstEvents, firstBlocked⟩ :=
      realize_dispatch related closed first
    obtain ⟨tailActions, tailResult, scheduled, finalRel, tailSelections, tailEvents, tailBlocked⟩ :=
      ih middleRel following
    rw [same]
    refine ⟨firstActions ++ tailActions, (tailResult.1, firstResult.2 ++ tailResult.2),
      TSO.schedule_append _ _ _ _ _ issued scheduled, finalRel, ?_, ?_, ?_⟩
    · rw [retiredSelections_append, firstSelections, tailSelections]
      rfl
    · rw [atomicEvents_append, firstEvents, tailEvents]
      cases head.2 <;> rfl
    · rw [blockedCount_append, firstBlocked, tailBlocked]

/-- Every related paused state has a finite completing continuation with no
new busy exchange or stall. No future successful replay, fairness, or timing
premise is required; the logical continuation is constructed internally. -/
theorem completion {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config) :
    ∃ actions result,
      TSO.schedule physical actions = .ok result ∧ TSO.Finished result.1 ∧
      MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧ blockedCount result.2 = 0 ∧
      TSO.retiredCount result.2 = MutexReplay.potentialSum logical ∧
      TSO.retiredCount result.2 ≤ 15 * logical.workers.length := by
  obtain ⟨selections, checkedResult, checked, finished, noBusy, length, bound⟩ :=
    MutexReplay.cohort_completion _ _ related.invariant related.ready closed
  obtain ⟨actions, result, scheduled, finalRel, projected, events, blocked⟩ :=
    realize_schedule related closed checked
  have retired : TSO.retiredCount result.2 = selections.length := by
    rw [← retiredSelections_length, projected]
  exact ⟨actions, result, scheduled, finalRel.finished_iff.mpr finished,
    events ▸ noBusy, blocked, retired.trans length, by omega⟩

/-- An entry cohort has a completing buffered execution attaining thirteen
retired user instructions per worker. Drains count separately as model actions. -/
theorem entry_completion {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) :
    ∃ actions result,
      TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result ∧
      TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
      blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 = 13 * state.workers.length ∧
      CompletedResult config state initial result := by
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired, _⟩ :=
    completion (Rel.initial admitted.invariant admitted.ready admitted.profile) admitted.closed
  rw [MutexReplay.entry_potential _ admitted.entry] at retired
  exact ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired,
    completed_observations admitted scheduled finished.1⟩

/-- Arbitrary successful physical prefixes admit a finite completing suffix.
Its full result still satisfies the original cohort's contract, including
prefix busy retries; the suffix introduces no additional busy exchange. -/
theorem prefix_completion {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {prior : List TSO.Action}
    {middle : Physical × List TSO.Observation}
    (priorSuccess : TSO.schedule (TSO.initial (MutexReplay.erase state)) prior = .ok middle) :
    ∃ actions result,
      TSO.schedule middle.1 actions = .ok result ∧ TSO.Finished result.1 ∧
      MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧ blockedCount result.2 = 0 ∧
      TSO.retiredCount result.2 ≤ 15 * state.workers.length ∧
      CompletedResult config state initial (result.1, middle.2 ++ result.2) := by
  obtain ⟨logical, replayed, related⟩ := schedule_lifts
    (Rel.initial admitted.invariant admitted.ready admitted.profile) admitted.closed priorSuccess
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, _, bound⟩ := completion related admitted.closed
  have length := (MutexReplay.schedule_trace _ _ _ replayed).length
  refine ⟨actions, result, scheduled, finished, noBusy, noBlocked, by simpa only [length] using bound, ?_⟩
  exact completed_observations admitted (TSO.schedule_append _ _ _ _ _ priorSuccess scheduled) finished.1

end EDSL.OS.MutexTSO
