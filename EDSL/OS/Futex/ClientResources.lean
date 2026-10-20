/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientProjection
import EDSL.OS.Futex.ClientCalls

namespace EDSL.OS.Futex.Clients
open X86

/-- Fixed cohort handles precede this resource frontier; every actual call pin
is allocated at or above it. Invocation IDs have a different frontier. -/
structure PinDiscipline (floor : Nat) (state : State) : Prop where
  frontier : floor ≤ state.authority.nextHandle
  calls : ∀ identifier call, state.calls identifier = some call → floor ≤ call.pin

def HandlesBelow (floor : Nat) (before after : Atomics.State) : Prop :=
  ∀ identifier, identifier < floor → after.handles identifier = before.handles identifier

theorem capture_discipline {config : Config} {state after : State} {worker invocation floor : Nat}
    (pins : PinDiscipline floor state)
    (success : captureEntered config state worker invocation = .ok after) :
    PinDiscipline floor after ∧ HandlesBelow floor state.authority after.authority ∧
      after.registration = state.registration := by
  obtain ⟨saved, operation, registration, retained, _, _, _, _, _, _, _, keeping, same⟩ :=
    captureEntered_effect success
  have issued := (Resources.retainCall_ok _ _ _ _ keeping).2
  obtain ⟨_, _, _, _, _, _, _, retainedEq⟩ := Atomics.issue_ok _ _ _ _ _ _ issued
  rw [same, retainedEq]
  refine ⟨⟨by have bound := pins.frontier; dsimp [putCall, Atomics.install]; omega, ?_⟩, ?_, rfl⟩
  · intro identifier call found
    by_cases newCall : identifier = invocation
    · subst identifier
      have equal : call = ⟨worker, operation, state.authority.nextHandle, .entered⟩ := by
        simpa [putCall] using found.symm
      subst call
      exact pins.frontier
    · apply pins.calls identifier call
      simpa [putCall, newCall] using found
  · intro identifier below
    have different : identifier ≠ state.authority.nextHandle := by have bound := pins.frontier; omega
    simp [putCall, Atomics.install, different]

theorem Physical.issue_discipline (profile : Physical.Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) {floor : Nat} (pins : PinDiscipline floor state)
    (success : Physical.issue profile state worker = .ok result) :
    PinDiscipline floor result.1 ∧ HandlesBelow floor state.authority result.1.authority ∧
      result.1.registration = state.registration := by
  cases issued : Suspend.issue state.suspended worker with
  | error fault => simp [Physical.issue, issued, Except.mapError] at success
  | ok actual =>
    rcases actual with ⟨suspended, observation⟩
    cases synced : Physical.synchronize profile state.authority observation with
    | error fault => simp [Physical.issue, issued, synced, Except.mapError] at success
    | ok authority =>
      have frames := Physical.synchronize_frames profile state.authority authority observation synced
      cases observation with
      | entered selected invocation =>
        have authorityEq : authority = state.authority := by simpa [Physical.synchronize] using synced.symm
        subst authority
        cases captured : captureEntered profile.service {state with suspended := suspended} selected invocation with
        | error fault => simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
        | ok after =>
          simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
          subst result
          exact capture_discipline (state := {state with suspended := suspended})
            ⟨pins.frontier, pins.calls⟩ captured
      | machine observed =>
        simp [Physical.issue, issued, synced, Except.mapError] at success
        subst result
        exact ⟨⟨by rw [frames.2.1]; exact pins.frontier, pins.calls⟩,
          fun _ _ => congrFun frames.1 _, rfl⟩
      | parked selected invocation | resumed selected invocation raw | idle =>
        simp [Physical.issue, issued, Physical.synchronize, Except.mapError] at success
        subst result
        exact ⟨⟨pins.frontier, pins.calls⟩, fun _ _ => rfl, rfl⟩

theorem Physical.drain_discipline (profile : Physical.Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) {floor : Nat} (pins : PinDiscipline floor state)
    (success : Physical.drain profile state worker = .ok result) :
    PinDiscipline floor result.1 ∧ HandlesBelow floor state.authority result.1.authority ∧
      result.1.registration = state.registration := by
  cases drained : Suspend.drain state.suspended worker with
  | error fault => simp [Physical.drain, drained, Except.mapError] at success
  | ok actual =>
    cases synced : Physical.synchronize profile state.authority actual.2 with
    | error fault => simp [Physical.drain, drained, synced, Except.mapError] at success
    | ok authority =>
      simp [Physical.drain, drained, synced, Except.mapError] at success
      subst result
      have frames := Physical.synchronize_frames profile state.authority authority actual.2 synced
      exact ⟨⟨by rw [frames.2.1]; exact pins.frontier, pins.calls⟩,
        fun _ _ => congrFun frames.1 _, rfl⟩

theorem service_discipline {config : Config} {state after : State} {action : Futex.Action} {floor : Nat}
    (pins : PinDiscipline floor state) (success : Futex.step config state action = .ok after) :
    PinDiscipline floor after ∧ HandlesBelow floor state.authority after.authority ∧
      after.registration = state.registration := by
  have advanced := (service_resources_step success).advances
  have discipline : PinDiscipline floor after := by
    refine ⟨Nat.le_trans pins.frontier advanced.1, ?_⟩
    intro identifier call found
    obtain ⟨original, prior, _, _, pin⟩ := service_preimage success identifier call found
    rw [pin]
    exact pins.calls identifier original prior
  refine ⟨discipline, ?_, service_registration success⟩
  cases action with
  | compare invocation => rw [(compareWait_stutter success).2.1]; exact fun _ _ => rfl
  | wake invocation selected => rw [(wakeOne_stutter success).2.1]; exact fun _ _ => rfl
  | retry invocation => rw [(retryQueued_stutter success).2.1]; exact fun _ _ => rfl
  | spurious invocation => rw [(spuriousReady_stutter success).2.1]; exact fun _ _ => rfl
  | idle => simp [Futex.step] at success; subst after; exact fun _ _ => rfl
  | resume invocation flags rcx r11 =>
    obtain ⟨call, _, _, registration, _, closed, found, _, _, _, closing, same⟩ := resumeReady_effect success
    obtain ⟨_, _, actual⟩ := Resources.closeCall_ok _ _ _ _ _ closing
    obtain ⟨_, _, exactClosed⟩ := Atomics.close_ok _ _ _ _ actual
    rw [same, exactClosed]
    intro identifier below
    have different : identifier ≠ call.pin := by have bound := pins.calls _ _ found; omega
    simp [different]

end EDSL.OS.Futex.Clients

namespace EDSL.OS.Futex.Runtime
open X86 Clients

theorem step_discipline {profile : Physical.Profile} {state : State} {action : Runtime.Action}
    {result : State × Runtime.Observation} {floor : Nat} (pins : PinDiscipline floor state)
    (success : Runtime.step profile state action = .ok result) :
    PinDiscipline floor result.1 ∧ HandlesBelow floor state.authority result.1.authority ∧
      result.1.registration = state.registration := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue profile state worker with
    | error fault => simp [Runtime.step, issued] at success
    | ok actual =>
      simp [Runtime.step, issued] at success
      subst result
      exact Physical.issue_discipline _ _ _ _ pins issued
  | drain worker =>
    cases drained : Physical.drain profile state worker with
    | error fault => simp [Runtime.step, drained] at success
    | ok actual =>
      simp [Runtime.step, drained] at success
      subst result
      exact Physical.drain_discipline _ _ _ _ pins drained
  | service action =>
    cases serviced : Futex.step profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at success
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at success
      subst result
      exact service_discipline pins serviced

theorem trace_discipline {profile : Physical.Profile} {before after : State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation} {floor : Nat}
    (trace : Runtime.Trace profile before actions observations after) (pins : PinDiscipline floor before) :
    PinDiscipline floor after ∧ HandlesBelow floor before.authority after.authority ∧
      after.registration = before.registration := by
  induction trace with
  | nil => exact ⟨pins, fun _ _ => rfl, rfl⟩
  | cons first tail ih =>
    obtain ⟨middle, headFrame, headReg⟩ := step_discipline pins first
    obtain ⟨last, tailFrame, tailReg⟩ := ih middle
    exact ⟨last, fun identifier below => (tailFrame identifier below).trans (headFrame identifier below),
      tailReg.trans headReg⟩

theorem schedule_discipline {profile : Physical.Profile} {state : State}
    {actions : List Runtime.Action} {result : State × List Runtime.Observation} {floor : Nat}
    (pins : PinDiscipline floor state) (success : Runtime.schedule profile state actions = .ok result) :
    PinDiscipline floor result.1 ∧ HandlesBelow floor state.authority result.1.authority ∧
      result.1.registration = state.registration :=
  trace_discipline (Runtime.schedule_trace _ _ _ _ success) pins

end EDSL.OS.Futex.Runtime
