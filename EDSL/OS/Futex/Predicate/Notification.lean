/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Physical
import EDSL.OS.Futex.Predicate.CallFacts
import EDSL.OS.Futex.ClientNotification.Base

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate.Notification
open X86

/-- An arbitrary mixed step cannot requeue the designated WAIT after
notification. Physical queue preservation is independent of word preservation;
service comparison uses the current RAM and actual captured request family. -/
theorem runtime_preserves {cohort : Cohort} {state : State}
    {action : Runtime.Action} {result : State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state cohort.waiter)
    (actual : Runtime.step cohort.profile state action = .ok result) :
    Futex.Notification.NoQueuedWait result.1 cohort.waiter := by
  cases action with
  | issue selected =>
    cases issued : Physical.issue cohort.profile state selected with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      exact Clients.Notification.issue_preserves clear issued
  | drain selected =>
    cases drained : Physical.drain cohort.profile state selected with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      exact Clients.Notification.drain_preserves clear drained
  | service action =>
    cases serviced : Futex.step cohort.profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      exact Futex.Notification.service_preserves admitted.runtime.service (admitted.currentWord published)
        (by decide : (1 : BitVec 32) ≠ 0) admitted.expectedFor clear serviced

/-- All later accepted mixed prefixes remain clear under the actual code's
persistent publication. Issue/drain/service order, retries, spurious readiness
and arbitrary resume clobbers are unrestricted. -/
theorem trace_preserves {cohort : Cohort} {before after : State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait before cohort.waiter)
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    Futex.Notification.NoQueuedWait after cohort.waiter ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort after := by
  induction trace with
  | nil => exact ⟨clear, published, admitted⟩
  | cons first tail ih =>
    exact ih (admitted_step admitted first) (published_word_step admitted published first)
      (runtime_preserves admitted published clear first)

/-- Actual physical prefixes lift with identical observations before using
managed trace composition. Their success is derived from current resources;
no successful resource replay is a premise. -/
theorem machineTrace_lift {cohort : Cohort} {state : State} {physical : Suspend.State}
    {actions : List Runtime.Action}
    {observations : List Runtime.Observation}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state cohort.waiter)
    (trace : MachineTrace state.suspended actions observations physical) :
    ∃ after, Runtime.Trace cohort.profile state actions observations after ∧
      after.suspended = physical ∧ Futex.Notification.NoQueuedWait after cohort.waiter ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort after := by
  obtain ⟨after, lifted, same, _⟩ := trace.lift admitted rfl
  obtain ⟨safe, word, valid⟩ := trace_preserves admitted published clear lifted
  exact ⟨after, lifted, same, safe, word, valid⟩

/-- A successful WAKE1 after publication clears the sole WAIT, whether it was
queued before XCHG, compared in a mixed prefix, retried, or already ready.
The arbitrary suffix cannot requeue it under persistent mismatch. -/
theorem wake_then_trace {cohort : Cohort} {before afterWake after : State}
    {invocation : Nat} {selected : Option Nat}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (wake : wakeOne before invocation selected = .ok afterWake)
    (suffix : Runtime.Trace cohort.profile afterWake actions observations after) :
    Futex.Notification.NoQueuedWait after cohort.waiter ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort after := by
  have actual : Runtime.step cohort.profile before (.service (.wake invocation selected)) =
      .ok (afterWake, .serviced (.wake invocation selected)) := by
    simp [Runtime.step, Futex.step, wake, Except.mapError]
  have valid := admitted_step admitted actual
  have clear := Futex.Notification.wake_clears admitted.runtime.service admitted.onlyWaiter wake
  exact trace_preserves valid (published_word_step admitted published actual) clear suffix

/-- Exact actual XCHG and its current resources positively enable the managed
publication step. RAM publication is a conclusion of retirement, not a seed
condition or a value read from a syscall capture snapshot. -/
theorem exchange_lift {cohort : Cohort} {state : State} {suspended : Suspend.State}
    {publisher : Nat} {event : AtomicEvent} (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended publisher =
      .ok (suspended, .machine (.retired publisher (some event)))) :
    ∃ exchanged client,
      Physical.issue cohort.profile state publisher =
        .ok (exchanged, .machine (.retired publisher (some event))) ∧
      exchanged.suspended = suspended ∧ Admitted cohort exchanged ∧
      cohort.clients[publisher]? = some (.legacy client) ∧ client.role = .publishPayloadWake ∧
      event.address = cohort.registration.address ∧ event.after = 1 ∧
      loadDWord exchanged.suspended.machine.memory cohort.registration.address = .ok 1 := by
  obtain ⟨exchanged, enabled, same, valid⟩ := issue_lift admitted actual
  obtain ⟨client, member, role, address, value, _, _, word⟩ :=
    publisher_exchange_publishes_payload admitted actual
  exact ⟨exchanged, client, enabled, same, valid, member, role, address, value, by rw [same]; exact word⟩

/-- Already visible payloads survive every accepted mixed prefix, even while
WAIT remains queued. Notification clearance is not a premise of this frame. -/
theorem trace_payload {cohort : Cohort} {before after : State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    PayloadFrame cohort before.suspended.machine.memory after.suspended.machine.memory := by
  induction trace with
  | nil => exact PayloadFrame.refl _ _
  | cons first tail ih =>
    intro worker client member published
    exact ih (admitted_step admitted first) worker client member
      (runtime_payload_frame admitted first worker client member published)

/-- The same actual publisher retires XCHG and owns the associated pending
WAKE1 invocation. Any mixed prefix may intervene, and every later mixed suffix
is safe. The invocation is bound by the invariant to its actual saved syscall;
this theorem assumes only observed execution, never future successful service
as a cohort admission field. -/
theorem exchange_wake_trace {cohort : Cohort} {before exchanged waking afterWake after : State}
    {publisher invocation pin : Nat} {event : AtomicEvent}
    {selected : Option Nat} {middleActions laterActions : List Runtime.Action}
    {prefixObs suffixObs : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (exchange : Physical.issue cohort.profile before publisher =
      .ok (exchanged, .machine (.retired publisher (some event))))
    (between : Runtime.Trace cohort.profile exchanged middleActions prefixObs waking)
    (associated : waking.calls invocation = some ⟨publisher, .wakeOne, pin, .entered⟩)
    (wake : wakeOne waking invocation selected = .ok afterWake)
    (later : Runtime.Trace cohort.profile afterWake laterActions suffixObs after) :
    (∃ client saved, cohort.clients[publisher]? = some (.legacy client) ∧ client.role = .publishPayloadWake ∧
      waking.suspended.pending publisher = some saved ∧ saved.identifier = invocation ∧
      client.Family saved.request ∧
      loadDWord after.suspended.machine.memory client.store.address = .ok client.store.value) ∧
    Futex.Notification.NoQueuedWait after cohort.waiter ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort after := by
  have actual := Physical.issue_projection _ _ _ _ exchange
  obtain ⟨client, member, role, _, _, _, payload, word⟩ :=
    publisher_exchange_publishes_payload admitted actual
  have first : Runtime.step cohort.profile before (.issue publisher) =
      .ok (exchanged, .physical (.machine (.retired publisher (some event)))) := by
    simp [Runtime.step, exchange]
  have exchangedValid := admitted_step admitted first
  have wakingValid := exchangedValid.trace between
  have current := published_word_trace exchangedValid word between
  obtain ⟨saved, pending, identifier, _, _⟩ := (wakingValid.runtime.service.calls _ _ associated).saved
  obtain ⟨captured, atCaptured, family⟩ := wakingValid.pending_family pending
  have equal : captured = .legacy client := Option.some.inj (atCaptured.symm.trans member)
  subst captured
  have wakeStep : Runtime.step cohort.profile waking (.service (.wake invocation selected)) =
      .ok (afterWake, .serviced (.wake invocation selected)) := by
    simp [Runtime.step, Futex.step, wake, Except.mapError]
  have wakingPayload := trace_payload exchangedValid between publisher client member payload
  have wakePayload := runtime_payload_frame wakingValid wakeStep publisher client member wakingPayload
  have finalPayload := trace_payload (admitted_step wakingValid wakeStep) later
    publisher client member wakePayload
  exact ⟨⟨client, saved, member, role, pending, identifier, family, finalPayload⟩,
    wake_then_trace wakingValid current wake later⟩


/-- A current associated entered WAKE1 is enabled by actual resources and the
structural sole-WAIT policy. No future success or favorable target choice is
assumed; an eligible choice is constructed from the present queue. -/
theorem wake_enabled {cohort : Cohort} {state : State} {invocation publisher pin : Nat}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (found : state.calls invocation = some ⟨publisher, .wakeOne, pin, .entered⟩) :
    ∃ selected after,
      Runtime.step cohort.profile state (.service (.wake invocation selected)) =
        .ok (after, .serviced (.wake invocation selected)) ∧
      after.queue = [] ∧ Futex.Notification.NoQueuedWait after cohort.waiter ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort after := by
  obtain ⟨selected, after, actual, empty, clear⟩ :=
    Futex.Notification.wake_enabled_clears admitted.runtime.service admitted.onlyWaiter found
  have success : Runtime.step cohort.profile state (.service (.wake invocation selected)) =
      .ok (after, .serviced (.wake invocation selected)) := by
    simp [Runtime.step, Futex.step, actual, Except.mapError]
  exact ⟨selected, after, success, empty, clear,
    published_word_step admitted published success, admitted_step admitted success⟩

/-- Notification safety holds at every index of any actual infinite mixed
execution. This supplies no fairness: an execution which idles forever remains
covered without claiming that its ready worker ever returns. -/
theorem infinite_preserves {cohort : Cohort}
    {states : Nat → State} {actions : Nat → Runtime.Action}
    {observations : Nat → Runtime.Observation}
    (admitted : Admitted cohort (states 0))
    (published : loadDWord (states 0).suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait (states 0) cohort.waiter)
    (execution : Runtime.Infinite cohort.profile states actions observations) :
    ∀ index, Futex.Notification.NoQueuedWait (states index) cohort.waiter ∧
      loadDWord (states index).suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort (states index) := by
  intro index
  induction index with
  | zero => exact ⟨clear, published, admitted⟩
  | succ index ih =>
    obtain ⟨safe, current, valid⟩ := ih
    have actual := execution index
    exact ⟨runtime_preserves valid current safe actual,
      published_word_step valid current actual, admitted_step valid actual⟩

end EDSL.OS.Futex.Predicate.Notification

#audit_edsl
