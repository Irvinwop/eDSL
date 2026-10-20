/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexClient
import EDSL.OS.Futex.ClientNotification.Base
import EDSL.Audit

namespace EDSL.Examples.FutexNotification
open X86 OS OS.Futex.Clients

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! A genuine three-client cohort. The loader, preparation history, current
authority, grants, exact code loans and complete return-word loans are those
of FutexClient. Its fourth WAIT client is absent from the machine and cohort;
its unused resource loans remain live. Admission contains no future execution
or notification assumption. -/

abbrev profile := FutexClient.profile
abbrev registration := FutexClient.registration

def clients : List Client := [FutexClient.waiter, FutexClient.publisher, FutexClient.peer]

def initial : OS.Futex.State :=
  OS.Futex.Runtime.initial FutexClient.authority (some registration)
    (clients.map fun client => ⟨client.entry, false, []⟩)

def cohort : Cohort :=
  ⟨initial, profile, registration, clients, FutexClient.cohort.pinFloor,
    FutexClient.cohort.fixedHandles⟩

/-- Membership transfers only for an actual member of the smaller cohort. -/
theorem original_member {worker : Nat} {client : Client}
    (found : cohort.clients[worker]? = some client) :
    FutexClient.cohort.clients[worker]? = some client := by
  cases worker with
  | zero => exact found
  | succ worker =>
    cases worker with
    | zero => exact found
    | succ worker =>
      cases worker with
      | zero => exact found
      | succ worker => simp [cohort, clients] at found

theorem static : Static cohort := by
  refine ⟨FutexClient.static.frontier, FutexClient.static.fixedBelow,
    FutexClient.static.keeperFixed, ?_, FutexClient.static.payloadSeparate⟩
  intro worker client found
  exact FutexClient.static.descriptors worker client (original_member found)

theorem initial_control : Control cohort initial.suspended := by
  intro worker actual live
  change (clients.map fun client => (⟨client.entry, false, []⟩ : TSO.Worker))[worker]? = some actual at live
  rw [List.getElem?_map] at live
  cases atClient : clients[worker]? with
  | none => simp [atClient] at live
  | some client =>
    simp only [atClient, Option.map_some, Option.some.injEq] at live
    subst actual
    refine ⟨client, atClient, .running .start (by cases client.role <;> trivial) ?_ rfl rfl ?_⟩
    · simp [Stage.context, Stage.offset]
    · cases kind : client.role <;> simp [Stage.FIFO, Stage.bufferCondition, kind]

theorem initial_runtime : OS.Futex.Runtime.Invariant profile initial := by
  apply OS.Futex.Runtime.initial_invariant profile FutexClient.authority (some registration) _
    FutexClient.authority_valid
  intro worker member store queued
  obtain ⟨client, _, same⟩ := List.mem_map.mp member
  subst worker
  cases queued

theorem initial_protection : Protected cohort initial := by
  intro worker client found
  exact FutexClient.initial_protection worker client (original_member found)

theorem initial_admitted : Admitted cohort initial := by
  refine ⟨static, initial_runtime, rfl, initial_control, rfl,
    FutexClient.initial_admitted.fixed, ⟨Nat.le_refl _, fun _ _ found => by cases found⟩,
    FutexClient.initial_admitted.target, FutexClient.initial_admitted.payload, ?_, initial_protection⟩
  intro worker actual live store queued
  change (clients.map fun client => (⟨client.entry, false, []⟩ : TSO.Worker))[worker]? = some actual at live
  rw [List.getElem?_map] at live
  cases atClient : clients[worker]? with
  | none => simp [atClient] at live
  | some client =>
    simp only [atClient, Option.map_some, Option.some.injEq] at live
    subst actual
    cases queued

theorem policy : OS.Futex.Clients.Notification.Policy cohort 0 0 := by
  refine ⟨⟨FutexClient.waiter, rfl, rfl⟩, ?_, by decide⟩
  intro worker client value found role
  rcases FutexClient.client_cases (original_member found) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · cases role
  · cases role
  · simp [cohort, clients] at found

open OS.Futex
open Examples.Futex (checked checked_ok)

def waiterEntry : List Runtime.Action := [.issue 0, .issue 0, .issue 0]
def publisherEntry : List Runtime.Action := [.issue 1, .issue 1, .issue 1, .issue 1]

/-- The peer returns with its FIFO nonempty. The publisher's own FIFO first
blocks XCHG, then actually drains. The atomic instruction is still next. -/
def prepare : List Runtime.Action :=
  [.issue 2, .issue 2, .issue 2, .issue 1, .issue 1, .issue 1, .issue 1, .drain 1]

def prepared : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile initial prepare) (by rfl)

def entered : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile prepared.1 waiterEntry) (by rfl)

def queued : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile entered.1 [.service (.compare 0)]) (by rfl)

def queuedExchange : OS.Futex.State × Suspend.Observation :=
  checked (Physical.issue profile queued.1 1) (by rfl)

def queuedWaking : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queuedExchange.1 publisherEntry) (by rfl)

def queuedWoken : OS.Futex.State := checked (wakeOne queuedWaking.1 1 (some 0)) (by rfl)

def enteredExchange : OS.Futex.State × Suspend.Observation :=
  checked (Physical.issue profile entered.1 1) (by rfl)

def betweenActions : List Runtime.Action := [.service (.compare 0)] ++ publisherEntry

def betweenWaking : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile enteredExchange.1 betweenActions) (by rfl)

def betweenWoken : OS.Futex.State := checked (wakeOne betweenWaking.1 1 none) (by rfl)

def lateExchange : OS.Futex.State × Suspend.Observation :=
  checked (Physical.issue profile prepared.1 1) (by rfl)

def lateWaking : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateExchange.1 publisherEntry) (by rfl)

def lateWoken : OS.Futex.State := checked (wakeOne lateWaking.1 0 none) (by rfl)

def lateEntered : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateWoken waiterEntry) (by rfl)

def lateCompared : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateEntered.1 [.service (.compare 1)]) (by rfl)

/-- Retry drops the first comparison, retaining the real invocation and pin;
the next comparison occurs against the now-published current word. -/
def retryActions : List Runtime.Action :=
  [.service (.retry 0), .service (.compare 0)] ++ publisherEntry

def retryWaking : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queuedExchange.1 retryActions) (by rfl)

def retryWoken : OS.Futex.State := checked (wakeOne retryWaking.1 1 none) (by rfl)

def spurious : OS.Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile queued.1 [.service (.spurious 0)]) (by rfl)

theorem prepared_admitted : Admitted cohort prepared.1 := initial_admitted.schedule (checked_ok _ _)
theorem entered_admitted : Admitted cohort entered.1 := prepared_admitted.schedule (checked_ok _ _)
theorem queued_admitted : Admitted cohort queued.1 := entered_admitted.schedule (checked_ok _ _)

end EDSL.Examples.FutexNotification

#audit_edsl
