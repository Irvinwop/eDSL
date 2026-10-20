/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientPhysical
import EDSL.OS.Futex.ClientPublishing

namespace EDSL.OS.Futex.Clients
open X86

/-- A current physical operation or a current service phase/queue choice.
There is no premise asserting successful managed replay. -/
inductive Demand (state : State) : Runtime.Action → Runtime.Observation → Prop where
  | issue {worker suspended observation}
      (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
      Demand state (.issue worker) (.physical observation)
  | drain {worker suspended observation}
      (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
      Demand state (.drain worker) (.physical observation)
  | service {action} (enabled : Guard state action) :
      Demand state (.service action) (.serviced action)

/-- Every current demand extends the managed execution and preserves all
current code, return-stack, FIFO and resource obligations. -/
theorem demand_enabled {cohort : Cohort} {state : State}
    {action : Runtime.Action} {observation : Runtime.Observation}
    (admitted : Admitted cohort state) (demand : Demand state action observation) :
    ∃ after, Runtime.step cohort.profile state action = .ok (after, observation) ∧
      Admitted cohort after := by
  cases demand with
  | issue actual =>
    obtain ⟨after, enabled, _, valid⟩ := issue_lift admitted actual
    exact ⟨after, by simp [Runtime.step, enabled], valid⟩
  | drain actual =>
    obtain ⟨after, enabled, _, valid⟩ := drain_lift admitted actual
    exact ⟨after, by simp [Runtime.step, enabled], valid⟩
  | service guard =>
    obtain ⟨after, enabled, valid⟩ := service_lift admitted guard
    exact ⟨after, by simp [Runtime.step, enabled, Except.mapError], valid⟩

/-- Any accepted finite prefix can be extended by a newly chosen current
demand. Its extension's success is a conclusion, not a replay premise. -/
theorem extend_prefix {cohort : Cohort} {initial current : State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    {action : Runtime.Action} {observation : Runtime.Observation}
    (admitted : Admitted cohort initial)
    (history : Runtime.Trace cohort.profile initial actions observations current)
    (demand : Demand current action observation) :
    ∃ after, Runtime.Trace cohort.profile initial (actions ++ [action])
      (observations ++ [observation]) after ∧ Admitted cohort after := by
  obtain ⟨after, enabled, valid⟩ := demand_enabled (admitted.trace history) demand
  have last : Runtime.schedule cohort.profile current [action] = .ok (after, [observation]) := by
    simp [Runtime.schedule, enabled]
  exact ⟨after, Runtime.schedule_trace _ _ _ _
    (Runtime.schedule_append _ _ _ _ _ _ history.schedule last), valid⟩

/-- Actual physical issue/drain prefixes, before resource replay. Service
resumption is intentionally absent: it requires a current typed service call. -/
inductive MachineTrace : Suspend.State → List Runtime.Action → List Runtime.Observation → Suspend.State → Prop where
  | nil {state} : MachineTrace state [] [] state
  | issue {before middle after worker observation actions observations}
      (actual : Suspend.issue before worker = .ok (middle, observation))
      (tail : MachineTrace middle actions observations after) :
      MachineTrace before (.issue worker :: actions) (.physical observation :: observations) after
  | drain {before middle after worker observation actions observations}
      (actual : Suspend.drain before worker = .ok (middle, observation))
      (tail : MachineTrace middle actions observations after) :
      MachineTrace before (.drain worker :: actions) (.physical observation :: observations) after

/-- A whole finite physical prefix has an exact managed lift. No successful
managed trace or schedule is supplied to this theorem. -/
theorem MachineTrace.lift {cohort : Cohort} {before after : Suspend.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (trace : MachineTrace before actions observations after) {state : State}
    (admitted : Admitted cohort state) (same : state.suspended = before) :
    ∃ final, Runtime.Trace cohort.profile state actions observations final ∧
      final.suspended = after ∧ Admitted cohort final := by
  induction trace generalizing state with
  | nil => exact ⟨state, .nil, same, admitted⟩
  | issue actual tail ih =>
    have current := same ▸ actual
    obtain ⟨middle, enabled, physical, valid⟩ := issue_lift admitted current
    obtain ⟨final, lifted, physicalFinal, finalValid⟩ := ih valid physical
    exact ⟨final, .cons (by simp [Runtime.step, enabled]) lifted, physicalFinal, finalValid⟩
  | drain actual tail ih =>
    have current := same ▸ actual
    obtain ⟨middle, enabled, physical, valid⟩ := drain_lift admitted current
    obtain ⟨final, lifted, physicalFinal, finalValid⟩ := ih valid physical
    exact ⟨final, .cons (by simp [Runtime.step, enabled]) lifted, physicalFinal, finalValid⟩

/-- Once a publisher actually exchanges W to one, no supported later issue,
drain (including returned producers), or service transition resets it. -/
theorem published_word_step {cohort : Cohort} {state : State}
    {action : Runtime.Action} {result : State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (actual : Runtime.step cohort.profile state action = .ok result) :
    loadDWord result.1.suspended.machine.memory cohort.registration.address = .ok 1 := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      exact issue_preserves_published_word admitted published (Physical.issue_projection _ _ _ _ issued)
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      exact (drain_preserves_word admitted (Physical.drain_projection _ _ _ _ drained)).trans published
  | service action =>
    cases serviced : Futex.step cohort.profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      rw [service_memory serviced]
      exact published

theorem published_word_trace {cohort : Cohort} {before after : State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 := by
  induction trace with
  | nil => exact published
  | cons first tail ih =>
    exact ih (admitted_step admitted first) (published_word_step admitted published first)

end EDSL.OS.Futex.Clients
