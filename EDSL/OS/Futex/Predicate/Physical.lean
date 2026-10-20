/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Control
import EDSL.OS.Futex.ClientCoverage

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86

/-- Actual instruction/service effects prove post-control and the signal
domain separately; resource history then rebuilds current admission. -/
theorem admitted_step {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result) : Admitted cohort result.1 := by
  apply admitted.advance actual ?_ (word_domain_step admitted actual)
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      exact issue_control admitted (Physical.issue_projection _ _ _ _ issued)
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      exact drain_control admitted (Physical.drain_projection _ _ _ _ drained)
  | service serviceAction =>
    cases serviced : Futex.step cohort.profile.service state serviceAction with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      exact service_control admitted.control admitted.static admitted.runtime.service serviced

theorem Admitted.trace {cohort : Cohort} {before after : Futex.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (trace : Runtime.Trace cohort.profile before actions observations after) : Admitted cohort after := by
  induction trace with
  | nil => exact admitted
  | cons first tail ih => exact ih (admitted_step admitted first)

theorem Admitted.schedule {cohort : Cohort} {state : Futex.State}
    {actions : List Runtime.Action} {result : Futex.State × List Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.schedule cohort.profile state actions = .ok result) : Admitted cohort result.1 :=
  admitted.trace (Runtime.schedule_trace _ _ _ _ actual)

/-- Universal accepted infinite behavior requires no fairness premise. -/
theorem Admitted.infinite {cohort : Cohort} {states : Nat → Futex.State}
    {actions : Nat → Runtime.Action} {observations : Nat → Runtime.Observation}
    (admitted : Admitted cohort (states 0))
    (execution : Runtime.Infinite cohort.profile states actions observations) :
    ∀ index, Admitted cohort (states index) := by
  intro index
  induction index with
  | zero => exact admitted
  | succ index ih => exact admitted_step ih (execution index)

/-- Every successful actual raw issue has an enabled managed step with the
identical suspended output and observation. No managed success is a premise. -/
theorem issue_lift {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.issue cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Admitted cohort after := by
  obtain ⟨after, issued, physical, _, _⟩ := issue_enabled admitted actual
  have runtime : Runtime.step cohort.profile state (.issue worker) =
      .ok (after, .physical observation) := by simp [Runtime.step, issued]
  exact ⟨after, issued, physical, admitted_step admitted runtime⟩

theorem drain_lift {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.drain cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Admitted cohort after := by
  obtain ⟨after, drained, physical, _, _⟩ := drain_enabled admitted actual
  have runtime : Runtime.step cohort.profile state (.drain worker) =
      .ok (after, .physical observation) := by simp [Runtime.step, drained]
  exact ⟨after, drained, physical, admitted_step admitted runtime⟩

/-- Current loop guards construct a real issue at every live cut, including
capture and RET. Already returned is the only terminal alternative. -/
theorem Admitted.loop_enabled {cohort : Cohort} {state : Futex.State}
    {worker : Nat} {client : Client} {before : TSO.Worker}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (found : state.suspended.machine.workers[worker]? = some before) :
    before.returned = true ∨ ∃ after observation selected,
      Suspend.issue state.suspended worker = .ok (after.suspended, observation) ∧
      Physical.issue cohort.profile state worker = .ok (after, observation) ∧
      after.suspended.machine.workers[worker]? = some selected ∧
      LoopControl cohort.registration.address client worker after.suspended selected ∧
      Admitted cohort after := by
  obtain ⟨kind, atKind, control⟩ := admitted.control worker before found
  cases Option.some.inj (atKind.symm.trans member)
  rcases LoopControl.enabled control found (admitted.currentCode worker _ member)
      (admitted.static.descriptors worker _ member).1 admitted.word
      (fun point _ => admitted.loop_ready member point) with returned |
        ⟨suspended, observation, selected, actual, selectedAt, next⟩
  · exact Or.inl returned
  · obtain ⟨after, issued, same, valid⟩ := issue_lift admitted actual
    exact Or.inr ⟨after, observation, selected, by rw [same]; exact actual,
      issued, by rw [same]; exact selectedAt, by rw [same]; exact next, valid⟩

abbrev Guard := Clients.LiftCore.Guard

/-- Present typed phases and queue eligibility construct actual service
success; the full ready result comes from the current call. -/
theorem service_lift {cohort : Cohort} {state : Futex.State} {action : Futex.Action}
    (admitted : Admitted cohort state) (enabled : Guard state action) :
    ∃ after, Futex.step cohort.profile.service state action = .ok after ∧ Admitted cohort after := by
  obtain ⟨after, serviced, _, _⟩ := Clients.LiftCore.service_enabled admitted.runtime enabled
  have runtime : Runtime.step cohort.profile state (.service action) = .ok (after, .serviced action) := by
    simp [Runtime.step, serviced, Except.mapError]
  exact ⟨after, serviced, admitted_step admitted runtime⟩

abbrev Demand := Clients.Demand

theorem demand_enabled {cohort : Cohort} {state : Futex.State}
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

/-- Any accepted finite mixed prefix extends by a current demand, without a
promise of future replay or a source/opcode gate. -/
theorem extend_prefix {cohort : Cohort} {initial current : Futex.State}
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

/-- Reuse only the generic raw issue/drain trace data. Its old-cohort lift is
not used; this induction proves admission for the actual heterogeneous slots. -/
abbrev MachineTrace := Clients.MachineTrace

theorem MachineTrace.lift {cohort : Cohort} {before after : Suspend.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (trace : MachineTrace before actions observations after) {state : Futex.State}
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

theorem published_word_trace {cohort : Cohort} {before after : Futex.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 := by
  induction trace with
  | nil => exact published
  | cons first tail ih =>
    exact ih (admitted_step admitted first) (published_word_step admitted published first)

end EDSL.OS.Futex.Predicate

#audit_edsl
