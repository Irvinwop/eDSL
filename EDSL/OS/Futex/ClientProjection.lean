/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.LoanFrames

namespace EDSL.OS.Futex
open X86

/-- The resource adapter retains exactly the suspension and observation
produced by actual physical instruction execution. -/
theorem Physical.issue_projection (profile : Physical.Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) (success : Physical.issue profile state worker = .ok result) :
    Suspend.issue state.suspended worker = .ok (result.1.suspended, result.2) := by
  cases issued : Suspend.issue state.suspended worker with
  | error fault => simp [Physical.issue, issued, Except.mapError] at success
  | ok actual =>
    rcases actual with ⟨suspended, observation⟩
    cases synced : Physical.synchronize profile state.authority observation with
    | error fault => simp [Physical.issue, issued, synced, Except.mapError] at success
    | ok authority =>
      cases observation with
      | entered selected invocation =>
        have authorityEq : authority = state.authority := by simpa [Physical.synchronize] using synced.symm
        subst authority
        cases captured : captureEntered profile.service {state with suspended := suspended} selected invocation with
        | error fault => simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
        | ok after =>
          simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
          subst result
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := captureEntered_effect captured
          rw [same]
          rfl
      | machine observed =>
        simp [Physical.issue, issued, synced, Except.mapError] at success
        subst result
        rfl
      | parked selected invocation | resumed selected invocation raw | idle =>
        simp [Physical.issue, issued, Physical.synchronize, Except.mapError] at success
        subst result
        rfl

theorem Physical.drain_projection (profile : Physical.Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) (success : Physical.drain profile state worker = .ok result) :
    Suspend.drain state.suspended worker = .ok (result.1.suspended, result.2) := by
  cases drained : Suspend.drain state.suspended worker with
  | error fault => simp [Physical.drain, drained, Except.mapError] at success
  | ok actual =>
    cases synced : Physical.synchronize profile state.authority actual.2 with
    | error fault => simp [Physical.drain, drained, synced, Except.mapError] at success
    | ok authority =>
      simp [Physical.drain, drained, synced, Except.mapError] at success
      subst result
      rfl

theorem suspend_step_worker_count {state : Suspend.State} {action : Suspend.Action}
    {result : Suspend.State × Suspend.Observation}
    (success : Suspend.step state action = .ok result) :
    result.1.machine.workers.length = state.machine.workers.length := by
  cases action with
  | issue worker =>
    cases Suspend.issue_effect _ _ _ success with
    | entered => rfl
    | parked => rfl
    | machine pending issued =>
      obtain ⟨_, _, _, _, _, _, effect⟩ := TSO.issue_effect _ _ _ issued
      cases effect <;> simp [TSO.install]
  | drain worker =>
    obtain ⟨machine, observation, drained, same⟩ := Suspend.drain_ok _ _ _ success
    obtain ⟨_, _, _, _, _, _, _, installed⟩ := TSO.drain_ok _ _ _ drained
    rw [same]
    have projected := congrArg Prod.fst installed
    dsimp only at projected
    rw [projected]
    simp [TSO.install]
  | resume worker invocation raw flags rcx r11 =>
    cases resumed : Suspend.resume state worker invocation raw flags rcx r11 with
    | error fault => simp [Suspend.step, resumed] at success
    | ok after =>
      simp [Suspend.step, resumed] at success
      subst result
      obtain ⟨_, _, _, _, _, _, _, _, same⟩ := Suspend.resume_ok _ _ _ _ _ _ _ _ resumed
      rw [same]
      simp [TSO.install]
  | idle => simp [Suspend.step] at success; subst result; rfl

namespace Runtime

/-- Every mixed adapter step projects to an actual issue, drain, resume or
idle step. Neither resource records nor service phases replace decoding. -/
theorem step_projection {profile : Physical.Profile} {state : State}
    {action : Action} {result : State × Observation} (success : step profile state action = .ok result) :
    ∃ actual observed, Suspend.step state.suspended actual = .ok (result.1.suspended, observed) := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue profile state worker with
    | error fault => simp [step, issued] at success
    | ok actual =>
      simp [step, issued] at success
      subst result
      exact ⟨.issue worker, actual.2, Physical.issue_projection _ _ _ _ issued⟩
  | drain worker =>
    cases drained : Physical.drain profile state worker with
    | error fault => simp [step, drained] at success
    | ok actual =>
      simp [step, drained] at success
      subst result
      exact ⟨.drain worker, actual.2, Physical.drain_projection _ _ _ _ drained⟩
  | service action =>
    cases serviced : Futex.step profile.service state action with
    | error fault => simp [step, serviced, Except.mapError] at success
    | ok after =>
      simp [step, serviced, Except.mapError] at success
      subst result
      exact service_suspend_step serviced

theorem step_memory_frame {profile : Physical.Profile} {state : State}
    {action : Action} {result : State × Observation} (valid : Invariant profile state)
    (success : step profile state action = .ok result) :
    TSO.MemoryFrame state.suspended.machine.memory result.1.suspended.machine.memory := by
  obtain ⟨actual, observed, projected⟩ := step_projection success
  exact valid.service.suspended.step_memory_frame projected

theorem step_worker_count {profile : Physical.Profile} {state : State}
    {action : Action} {result : State × Observation} (success : step profile state action = .ok result) :
    result.1.suspended.machine.workers.length = state.suspended.machine.workers.length := by
  obtain ⟨actual, observed, projected⟩ := step_projection success
  exact suspend_step_worker_count projected

theorem Trace.memory_frame {profile : Physical.Profile} {before after : State}
    {actions : List Action} {observations : List Observation}
    (trace : Trace profile before actions observations after) (valid : Invariant profile before) :
    TSO.MemoryFrame before.suspended.machine.memory after.suspended.machine.memory := by
  induction trace with
  | nil => exact .refl _
  | cons first tail ih =>
    exact (step_memory_frame valid first).trans (ih (step_invariant valid first).1)

theorem schedule_memory_frame {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation} (valid : Invariant profile state)
    (success : schedule profile state actions = .ok result) :
    TSO.MemoryFrame state.suspended.machine.memory result.1.suspended.machine.memory :=
  (schedule_trace _ _ _ _ success).memory_frame valid

/-- Lower-userspace/non-executable admission remains true across every
accepted active prefix even when no service call currently exists. -/
theorem target_preserved {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation} (valid : Invariant profile state)
    (success : schedule profile state actions = .ok result) (address : Word) :
    targetSupported profile.service result.1.authority address = targetSupported profile.service state.authority address := by
  have frame := schedule_memory_frame valid success
  have afterInv := (schedule_invariant valid success).1
  simp only [targetSupported, valid.memory, afterInv.memory, TSO.dataOnly, frame.executable]

end Runtime
end EDSL.OS.Futex
