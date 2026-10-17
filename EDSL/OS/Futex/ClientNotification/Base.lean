/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientCoverage
import EDSL.OS.Futex.Notification

set_option warningAsError true

namespace EDSL.OS.Futex.Clients.Notification
open X86

/-- Structural cohort restriction for private-word notification. The declared
WAIT compares a value different from the publisher's one, and no other client
can submit a WAIT. This says nothing about current queue contents or progress. -/
structure Policy (cohort : Cohort) (worker : Nat) (expected : BitVec 32) : Prop where
  designated : ∃ client, cohort.clients[worker]? = some client ∧ client.role = .wait expected
  sole : ∀ index client value, cohort.clients[index]? = some client →
    client.role = .wait value → index = worker
  mismatch : expected ≠ 1

/-- Actual service records inherit their operation from the current pending
request and the concrete client's immutable request family. In particular this
is not an admission premise asserting that future service will succeed. -/
theorem call_family {cohort : Cohort} {state : State}
    (admitted : Admitted cohort state) {identifier : Nat} {call : Call}
    (found : state.calls identifier = some call) :
    ∃ client, cohort.clients[call.worker]? = some client ∧
      client.role ≠ .payloadPeer ∧ client.operation = call.op := by
  obtain ⟨saved, pending, _, _, classified⟩ := (admitted.runtime.service.calls _ _ found).saved
  obtain ⟨client, member, family⟩ := admitted.pending_family pending
  have actual := (Client.family_classifies (admitted.static.descriptors _ _ member) family).1
  exact ⟨client, member, family.1, Except.ok.inj (actual.symm.trans classified)⟩

theorem Policy.expectedFor {cohort : Cohort} {state : State} {worker : Nat} {expected : BitVec 32}
    (policy : Policy cohort worker expected) (admitted : Admitted cohort state) :
    Futex.Notification.ExpectedFor state worker expected := by
  intro identifier call observed found same operation
  obtain ⟨client, member, _, actual⟩ := call_family admitted found
  obtain ⟨designated, atDesignated, role⟩ := policy.designated
  rw [same] at member
  cases Option.some.inj (member.symm.trans atDesignated)
  have equal : Op.wait expected = .wait observed := by
    simpa only [Client.operation, role] using actual.trans operation
  exact (Op.wait.inj equal).symm

theorem Policy.onlyWaiter {cohort : Cohort} {state : State} {worker : Nat} {expected : BitVec 32}
    (policy : Policy cohort worker expected) (admitted : Admitted cohort state) :
    Futex.Notification.OnlyWaiter state worker := by
  intro identifier call observed found operation
  obtain ⟨client, member, _, actual⟩ := call_family admitted found
  have role : client.role = .wait observed := by
    cases kind : client.role with
    | wait value =>
      have equal : Op.wait value = .wait observed := by
        simpa only [Client.operation, kind] using actual.trans operation
      exact congrArg Role.wait (Op.wait.inj equal)
    | publishPayloadWake | payloadPeer =>
      simp [Client.operation, kind] at actual
      rw [← actual] at operation
      cases operation
  exact policy.sole _ _ _ member role

/-- Resource RAM equals all actual machine RAM, so the publication read has
its exact current registered-cell interpretation at every admitted prefix. -/
theorem currentWord {cohort : Cohort} {state : State} (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1) :
    Futex.Notification.CurrentWord state cohort.registration 1 :=
  ⟨admitted.registration, by rw [admitted.runtime.memory]; exact published⟩

/-- Physical capture only adds an entered record; it cannot enqueue the new
invocation or rephase any previously pending invocation. -/
theorem capture_preserves {config : Config} {state after : State} {selected invocation worker : Nat}
    (clear : Futex.Notification.NoQueuedWait state worker)
    (actual : captureEntered config state selected invocation = .ok after) :
    Futex.Notification.NoQueuedWait after worker := by
  obtain ⟨saved, operation, registration, retained, _, _, _, _, _, _, _, _, same⟩ :=
    captureEntered_effect actual
  rw [same]
  exact Futex.Notification.NoQueuedWait.put_entered clear

/-- Arbitrary accepted physical issue retains queue safety, including actual
SYSCALL entry and parked calls. No service scheduling choice is assumed. -/
theorem issue_preserves {profile : Physical.Profile} {state : State} {selected worker : Nat}
    {result : State × Suspend.Observation} (clear : Futex.Notification.NoQueuedWait state worker)
    (actual : Physical.issue profile state selected = .ok result) :
    Futex.Notification.NoQueuedWait result.1 worker := by
  cases issued : Suspend.issue state.suspended selected with
  | error fault => simp [Physical.issue, issued, Except.mapError] at actual
  | ok output =>
    rcases output with ⟨suspended, observation⟩
    cases synced : Physical.synchronize profile state.authority observation with
    | error fault => simp [Physical.issue, issued, synced, Except.mapError] at actual
    | ok authority =>
      cases observation with
      | entered owner invocation =>
        cases captured : captureEntered profile.service
            {state with suspended := suspended, authority := authority} owner invocation with
        | error fault => simp [Physical.issue, issued, synced, captured, Except.mapError] at actual
        | ok after =>
          simp [Physical.issue, issued, synced, captured, Except.mapError] at actual
          subst result
          exact capture_preserves (state := {state with suspended := suspended, authority := authority}) clear captured
      | machine observed | parked owner invocation | resumed owner invocation raw | idle =>
        simp [Physical.issue, issued, synced, Except.mapError] at actual
        subst result
        exact clear

/-- A drain changes physical/resource RAM, not service records or phases. -/
theorem drain_preserves {profile : Physical.Profile} {state : State} {selected worker : Nat}
    {result : State × Suspend.Observation} (clear : Futex.Notification.NoQueuedWait state worker)
    (actual : Physical.drain profile state selected = .ok result) :
    Futex.Notification.NoQueuedWait result.1 worker := by
  cases drained : Suspend.drain state.suspended selected with
  | error fault => simp [Physical.drain, drained, Except.mapError] at actual
  | ok output =>
    cases synced : Physical.synchronize profile state.authority output.2 with
    | error fault => simp [Physical.drain, drained, synced, Except.mapError] at actual
    | ok authority =>
      simp [Physical.drain, drained, synced, Except.mapError] at actual
      subst result
      exact clear


theorem Policy.call_operation {cohort : Cohort} {state : State} {worker identifier : Nat}
    {expected : BitVec 32} {call : Call} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state) (found : state.calls identifier = some call)
    (same : call.worker = worker) : call.op = .wait expected := by
  obtain ⟨client, member, _, actual⟩ := call_family admitted found
  obtain ⟨designated, atDesignated, role⟩ := policy.designated
  rw [same] at member
  cases Option.some.inj (member.symm.trans atDesignated)
  simpa only [Client.operation, role] using actual.symm

/-- Pending actual worker state determines the current invocation, operation
and phase via the service bijection. No fabricated service record is supplied. -/
theorem Policy.pending_call {cohort : Cohort} {state : State} {worker : Nat}
    {expected : BitVec 32} {saved : Suspend.Saved} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state)
    (pending : state.suspended.pending worker = some saved) :
    ∃ pin phase, state.calls saved.identifier = some ⟨worker, .wait expected, pin, phase⟩ := by
  obtain ⟨call, found, same⟩ := admitted.runtime.service.pending _ _ pending
  have operation := policy.call_operation admitted found same
  rcases call with ⟨owner, op, pin, phase⟩
  dsimp only at same operation
  subst owner
  subst op
  exact ⟨pin, phase, found⟩

end EDSL.OS.Futex.Clients.Notification
