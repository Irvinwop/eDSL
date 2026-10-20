/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Runtime
import EDSL.OS.Futex.PhysicalInvariant
import EDSL.OS.Futex.ServiceStorage
import EDSL.OS.Threads.Framing

namespace EDSL.OS.Futex.Runtime
open X86 AddressSpace

/-- Service consistency and equality of the entire physical and resource RAM.
This is a present-state contract, with no eventual service or trace premise. -/
structure Invariant (profile : Physical.Profile) (state : State) : Prop where
  service : WellFormed profile.service state
  memory : toMemory state.authority.shared.resources.space = state.suspended.machine.memory

/-- Start a fresh cohort against the actual current managed cells. This does
not fabricate an already entered service record or an already queued caller. -/
def initial (authority : Atomics.State) (registration : Option Resources.Registration)
    (workers : List TSO.Worker) : State :=
  ⟨Suspend.initial ⟨toMemory authority.shared.resources.space, workers⟩,
    authority, registration, fun _ => none, []⟩

theorem initial_invariant (profile : Physical.Profile) (authority : Atomics.State)
    (registration : Option Resources.Registration) (workers : List TSO.Worker)
    (valid : Atomics.WellFormed authority)
    (buffers : TSO.BuffersValid ⟨toMemory authority.shared.resources.space, workers⟩) :
    Invariant profile (initial authority registration workers) := by
  refine ⟨⟨Suspend.WellFormed.initial buffers, valid, ?_, ?_, by simp [initial], ?_, ?_⟩, rfl⟩
  · intro identifier call found
    cases found
  · intro worker saved pending
    cases pending
  · intro identifier
    simp [initial]
  · intro left a right b first
    cases first

theorem history_trans {before middle after : Atomics.State}
    (first : Atomics.History before middle) (last : Atomics.History middle after) :
    Atomics.History before after := by
  induction first with
  | refl => exact last
  | next first tail ih => exact .next first (ih last)

/-- All successful actual instructions, drains and service transitions retain
both invariants. This is safety; enabledness has its own current-guard theorems. -/
theorem step_invariant {profile : Physical.Profile} {state : State}
    {action : Action} {result : State × Observation} (valid : Invariant profile state)
    (success : step profile state action = .ok result) :
    Invariant profile result.1 ∧ Atomics.History state.authority result.1.authority := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue profile state worker with
    | error fault => simp [step, issued] at success
    | ok actual =>
      simp [step, issued] at success
      subst result
      obtain ⟨service, memory, history⟩ := Physical.issue_sound _ _ _ _ valid.service valid.memory issued
      exact ⟨⟨service, memory⟩, history⟩
  | drain worker =>
    cases drained : Physical.drain profile state worker with
    | error fault => simp [step, drained] at success
    | ok actual =>
      simp [step, drained] at success
      subst result
      obtain ⟨service, memory, history⟩ := Physical.drain_sound _ _ _ _ valid.service valid.memory drained
      exact ⟨⟨service, memory⟩, history⟩
  | service action =>
    cases serviced : Futex.step profile.service state action with
    | error fault => simp [step, serviced, Except.mapError] at success
    | ok after =>
      simp [step, serviced, Except.mapError] at success
      subst result
      obtain ⟨physical, shared, history⟩ := service_storage serviced
      exact ⟨⟨valid.service.service_step serviced, by rw [shared, physical]; exact valid.memory⟩, history⟩

theorem Trace.invariant {profile : Physical.Profile} {before after : State}
    {actions : List Action} {observations : List Observation}
    (trace : Trace profile before actions observations after) (valid : Invariant profile before) :
    Invariant profile after ∧ Atomics.History before.authority after.authority := by
  induction trace with
  | nil => exact ⟨valid, .refl⟩
  | cons first tail ih =>
    obtain ⟨middle, head⟩ := step_invariant valid first
    obtain ⟨finalState, suffix⟩ := ih middle
    exact ⟨finalState, history_trans head suffix⟩

theorem schedule_invariant {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation} (valid : Invariant profile state)
    (success : schedule profile state actions = .ok result) :
    Invariant profile result.1 ∧ Atomics.History state.authority result.1.authority :=
  (schedule_trace _ _ _ _ success).invariant valid

/-- Prefix invariants retain managed revocation permanently, even while peer
workers execute, calls queue/retry, and later invocation IDs are allocated. -/
theorem revoked_for_schedule {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation} (valid : Invariant profile state)
    (success : schedule profile state actions = .ok result) {identifier : Nat}
    (closed : Atomics.Revoked state.authority identifier) :
    Atomics.Revoked result.1.authority identifier :=
  closed.persists (schedule_invariant valid success).2

/-- A surviving current read loan gives an exact byte/permission frame across
all runtime steps. Mutable futex words use pins and are never given read loans. -/
theorem surviving_loan_frame {profile : Physical.Profile} {state : State}
    {actions : List Action} {result : State × List Observation} (valid : Invariant profile state)
    (success : schedule profile state actions = .ok result)
    {borrower loanId : Nat} {region : Region}
    (loan : Threads.HasLoan state.authority.shared borrower loanId region)
    (retained : result.1.authority.shared.loans loanId = state.authority.shared.loans loanId) :
    Threads.HasLoan result.1.authority.shared borrower loanId region ∧
      AgreesOn result.1.authority.shared.resources.space state.authority.shared.resources.space region.base region.length :=
  loan.frame valid.service.authority.shared (schedule_invariant valid success).2.borrowing retained

end EDSL.OS.Futex.Runtime
