/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.RuntimeInvariant

namespace EDSL.OS.Futex
open X86

/-- Capture adds only a handle; it never changes the live loan registry. -/
theorem captureEntered_shared {config : Config} {state after : State} {worker invocation : Nat}
    (success : captureEntered config state worker invocation = .ok after) :
    after.authority.shared = state.authority.shared := by
  obtain ⟨_, _, registration, retained, _, _, _, _, _, _, _, keeping, same⟩ := captureEntered_effect success
  have issued := (Resources.retainCall_ok _ _ _ _ keeping).2
  obtain ⟨_, _, _, _, _, _, _, exactResult⟩ := Atomics.issue_ok _ _ _ _ _ _ issued
  rw [same, exactResult]
  rfl

theorem Physical.issue_loans (profile : Physical.Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) (success : Physical.issue profile state worker = .ok result) :
    result.1.authority.shared.loans = state.authority.shared.loans := by
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
        cases captured : captureEntered profile.service { state with suspended := suspended } selected invocation with
        | error fault => simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
        | ok after =>
          simp [Physical.issue, issued, Physical.synchronize, captured, Except.mapError] at success
          subst result
          rw [captureEntered_shared captured]
      | machine observed =>
        simp [Physical.issue, issued, synced, Except.mapError] at success
        subst result
        exact frames.2.2.1
      | parked selected invocation | resumed selected invocation raw | idle =>
        simp [Physical.issue, issued, Physical.synchronize, Except.mapError] at success
        subst result
        rfl

theorem Physical.drain_loans (profile : Physical.Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) (success : Physical.drain profile state worker = .ok result) :
    result.1.authority.shared.loans = state.authority.shared.loans := by
  cases drained : Suspend.drain state.suspended worker with
  | error fault => simp [Physical.drain, drained, Except.mapError] at success
  | ok actual =>
    cases synced : Physical.synchronize profile state.authority actual.2 with
    | error fault => simp [Physical.drain, drained, synced, Except.mapError] at success
    | ok authority =>
      simp [Physical.drain, drained, synced, Except.mapError] at success
      subst result
      exact (Physical.synchronize_frames _ _ _ _ synced).2.2.1

namespace Runtime

theorem step_loans {profile : Physical.Profile} {state : State} {action : Action}
    {result : State × Observation} (success : step profile state action = .ok result) :
    result.1.authority.shared.loans = state.authority.shared.loans := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue profile state worker with
    | error fault => simp [step, issued] at success
    | ok actual =>
      simp [step, issued] at success
      subst result
      exact Physical.issue_loans _ _ _ _ issued
  | drain worker =>
    cases drained : Physical.drain profile state worker with
    | error fault => simp [step, drained] at success
    | ok actual =>
      simp [step, drained] at success
      subst result
      exact Physical.drain_loans _ _ _ _ drained
  | service action =>
    cases serviced : Futex.step profile.service state action with
    | error fault => simp [step, serviced, Except.mapError] at success
    | ok after =>
      simp [step, serviced, Except.mapError] at success
      subst result
      rw [service_shared serviced]

theorem Trace.loans {profile : Physical.Profile} {before after : State}
    {actions : List Action} {observations : List Observation}
    (trace : Trace profile before actions observations after) :
    after.authority.shared.loans = before.authority.shared.loans := by
  induction trace with
  | nil => rfl
  | cons first tail ih => exact ih.trans (step_loans first)

theorem schedule_loans {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation}
    (success : schedule profile state actions = .ok result) :
    result.1.authority.shared.loans = state.authority.shared.loans :=
  (schedule_trace _ _ _ _ success).loans

/-- Actual cohort code/stack loans survive every active runtime prefix. There
is no assumed final successful return or assumed surviving-loan premise. -/
theorem loan_frame {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation} (valid : Invariant profile state)
    (success : schedule profile state actions = .ok result)
    {borrower loanId : Nat} {region : AddressSpace.Region}
    (loan : Threads.HasLoan state.authority.shared borrower loanId region) :
    Threads.HasLoan result.1.authority.shared borrower loanId region ∧
      AddressSpace.AgreesOn result.1.authority.shared.resources.space state.authority.shared.resources.space region.base region.length :=
  surviving_loan_frame valid success loan (congrFun (schedule_loans success) loanId)

end Runtime
end EDSL.OS.Futex
