/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Issue
import EDSL.OS.MutexTSO.TraceCore

namespace EDSL.OS.MutexTSO
open X86

/-- Every actual issue or drain has a checked replay interpretation. Busy
exchanges retire; blocked issues and drains keep the entire logical state. -/
theorem step_lifts {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {action : TSO.Action} {result : Physical × TSO.Observation}
    (success : TSO.step physical action = .ok result) :
    ∃ after, Lift logical action result.2 after ∧ Rel config result.1 after := by
  cases action with
  | issue identifier =>
    cases issue_lifts related closed success with
    | blocked beforeRel => exact ⟨logical, .blocked identifier, beforeRel⟩
    | retired checked afterRel => exact ⟨_, .retired checked, afterRel⟩
  | drain identifier =>
    have drained : TSO.drain physical identifier = .ok result := success
    obtain ⟨_, store, _, _, _, _, _, same⟩ := TSO.drain_ok _ _ _ drained
    have observed : result.2 = .drained identifier store := by rw [same]
    exact ⟨logical, observed ▸ Lift.drained identifier store, related.drain drained⟩

/-- Arbitrary finite physical prefixes retain full architectural contexts,
actual queues, resources and checked replay, including every real atomic event. -/
theorem trace_lifts {config : Mutex.Config} {physical after : Physical} {logical : Logical}
    {actions : List TSO.Action} {observations : List TSO.Observation}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    (trace : TSO.Trace physical actions observations after) :
    ∃ finalState, LiftTrace logical actions observations finalState ∧ Rel config after finalState := by
  induction trace generalizing logical with
  | nil => exact ⟨logical, .nil, related⟩
  | cons first tail ih =>
    obtain ⟨middle, lifted, middleRel⟩ := step_lifts related closed first
    obtain ⟨finalState, following, finalRel⟩ := ih middleRel
    exact ⟨finalState, .cons lifted following, finalRel⟩

/-- Replay selections and events are the canonical projections of actual
observations. Successful replay is established, never supplied as admission. -/
theorem schedule_lifts {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {actions : List TSO.Action} {result : Physical × List TSO.Observation}
    (success : TSO.schedule physical actions = .ok result) :
    ∃ finalState,
      MutexReplay.schedule logical (retiredSelections result.2) = .ok (finalState, TSO.atomicEvents result.2) ∧
      Rel config result.1 finalState := by
  obtain ⟨finalState, lifted, finalRel⟩ := trace_lifts related closed (TSO.schedule_trace _ _ _ success)
  exact ⟨finalState, lifted.replay, finalRel⟩

/-- Every reachable prefix retains enabledness of live unreturned issues and
publication of each nonempty FIFO. An enabled release may actually stall. -/
theorem prefix_lifts {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {actions : List TSO.Action} {result : Physical × List TSO.Observation}
    (success : TSO.schedule physical actions = .ok result) :
    ∃ finalState,
      MutexReplay.schedule logical (retiredSelections result.2) = .ok (finalState, TSO.atomicEvents result.2) ∧
      Rel config result.1 finalState ∧
      ∀ identifier worker, result.1.workers[identifier]? = some worker →
        (worker.returned = false → ∃ next, TSO.issue result.1 identifier = .ok next) ∧
        (worker.buffer ≠ [] → ∃ next, TSO.drain result.1 identifier = .ok next) := by
  obtain ⟨finalState, replayed, finalRel⟩ := schedule_lifts related closed success
  exact ⟨finalState, replayed, finalRel, fun _ _ live =>
    ⟨fun running => issue_enabled finalRel closed live running,
      fun nonempty => finalRel.drain_enabled live nonempty⟩⟩

end EDSL.OS.MutexTSO
