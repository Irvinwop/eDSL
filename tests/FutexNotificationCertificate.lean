/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexNotificationCertificate
import EDSL.Examples.FutexNotification
import EDSL.Audit

namespace EDSL.Tests.FutexNotificationCertificate
open X86 OS OS.Futex OS.Futex.Clients
open Examples.FutexNotification
open Examples.Futex (checked checked_ok)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Literal publication ABI, independently written with its protected RET. -/
def candidate : List Byte :=
  [0xb8, 0x44, 0x33, 0x22, 0x11, 0x89, 0x06,
   0xb8, 1, 0, 0, 0, 0x87, 0x07,
   0xb8, 202, 0, 0, 0, 0xbe, 129, 0, 0, 0,
   0xba, 1, 0, 0, 0, 0x0f, 0x05, 0xc3]

abbrev publisher := Examples.FutexClient.publisher

/-- Initial current code/resources and the actual sole-WAIT cohort suffice;
no successful future notification is supplied to the certificate. -/
theorem initial_certificate :
    EDSL.FutexNotificationCertificate.Specification candidate cohort initial 1 publisher 0 0 := by
  apply EDSL.FutexNotificationCertificate.sound candidate (by decide) initial_admitted rfl rfl
    ((initial_protection 1 publisher rfl).2.2.1) policy

/-- This contract observes the retained exact current-code binding and actual
published RAM after the same publisher's XCHG and captured WAKE1. The trace may
contain further physical instructions, returned-peer drains and service steps. -/
theorem notification_suffix {actions : List Runtime.Action} {observations : List Runtime.Observation}
    {after : Futex.State}
    (suffix : Runtime.Trace profile lateWoken actions observations after) :
    (∃ saved, lateWaking.1.suspended.pending 1 = some saved ∧ saved.identifier = 0 ∧
      publisher.Family saved.request) ∧
    Futex.Notification.NoQueuedWait after 0 ∧
    loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
    loadDWord after.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    CodeAt after.suspended.machine.memory 8192 candidate ∧
    EDSL.FutexNotificationCertificate.Specification candidate cohort after 1 publisher 0 0 := by
  have certificate := initial_certificate.of_admitted prepared_admitted
  have exchange : Physical.issue profile prepared.1 1 =
      .ok (lateExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile lateExchange.1 publisherEntry lateWaking (checked_ok _ _)
  have associated : lateWaking.1.calls 0 = some ⟨1, .wakeOne, 2, .entered⟩ := rfl
  obtain ⟨family, clear, word, payload, retained⟩ := certificate.notification exchange between associated
    (checked_ok (wakeOne lateWaking.1 0 none) (by rfl)) suffix
  exact ⟨family, clear, word, payload rfl, retained.binding.code, retained⟩

/-- A nonempty suffix actually drains the already-returned peer, then advances
an unentered WAIT by one decoded MOV. Certificate retention is obtained from
the notification API, rather than recertifying final fixture assignments. -/
def mixedActions : List Runtime.Action := [.drain 2, .issue 0]

def mixed : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateWoken mixedActions) (by rfl)

theorem mixed_notification_retains_binding :
    Futex.Notification.NoQueuedWait mixed.1 0 ∧
    loadDWord mixed.1.suspended.machine.memory 65536 = .ok 1 ∧
    loadDWord mixed.1.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    CodeAt mixed.1.suspended.machine.memory 8192 candidate ∧
    EDSL.FutexNotificationCertificate.Specification candidate cohort mixed.1 1 publisher 0 0 := by
  exact (notification_suffix (Runtime.schedule_trace profile lateWoken mixedActions mixed (checked_ok _ _))).2


/-- The concrete cuts cover pre-entry, immediately before SYSCALL, currently
pending, already resumed and already returned execution. -/
def beforeSyscall : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateWoken [.issue 0, .issue 0]) (by rfl)

def resumedActions : List Runtime.Action := waiterEntry ++
  [.service (.compare 1), .service (.resume 1 0x123456789abcdef0 0xfedcba9876543210 0x8877665544332211)]

def resumed : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateWoken resumedActions) (by rfl)

def returnedActions : List Runtime.Action := resumedActions ++ [.issue 0]

def returned : Futex.State × List Runtime.Observation :=
  checked (Runtime.schedule profile lateWoken returnedActions) (by rfl)

/-- These are observations of actual execution, rather than fabricated states
with a desired control constructor or assumed successful completion. -/
theorem lifecycle_cuts :
    (lateWoken.suspended.machine.workers[0]?).map (fun worker => worker.context.rip) = some 4096 ∧
    (mixed.1.suspended.machine.workers[0]?).map (fun worker => worker.context.rip) = some 4101 ∧
    (beforeSyscall.1.suspended.machine.workers[0]?).map (fun worker => worker.context.rip) = some 4106 ∧
    beforeSyscall.1.suspended.pending 0 = none ∧
    (lateEntered.1.suspended.pending 0).map Suspend.Saved.identifier = some 1 ∧
    resumed.1.suspended.pending 0 = none ∧
    (resumed.1.suspended.machine.workers[0]?).map TSO.Worker.returned = some false ∧
    (returned.1.suspended.machine.workers[0]?).map TSO.Worker.returned = some true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The root artifact certificate constructs a bounded actual suffix at every
accepted current cut, retaining its exact publisher binding. -/
def CertifiedCompletion (state : Futex.State) : Prop :=
  ∃ after, Clients.Notification.CompletesWithin 6 cohort 0 0 state after ∧
    EDSL.FutexNotificationCertificate.Specification candidate cohort after 1 publisher 0 0

theorem certified_suffix_completes {actions : List Runtime.Action}
    {observations : List Runtime.Observation} {state : Futex.State}
    (trace : Runtime.Trace profile lateWoken actions observations state) : CertifiedCompletion state := by
  obtain ⟨_, clear, word, _, _, certificate⟩ := notification_suffix trace
  exact certificate.complete word clear

/-- A pending-only regression would miss the real unentered, intermediate,
resumed and returned members of this list. Bounds count runtime transitions. -/
theorem every_current_certificate_completes :
    CertifiedCompletion lateWoken ∧ CertifiedCompletion mixed.1 ∧
    CertifiedCompletion beforeSyscall.1 ∧ CertifiedCompletion lateEntered.1 ∧
    CertifiedCompletion lateCompared.1 ∧ CertifiedCompletion resumed.1 ∧
    CertifiedCompletion returned.1 := by
  have compared : Runtime.Trace profile lateWoken (waiterEntry ++ [.service (.compare 1)])
      (lateEntered.2 ++ lateCompared.2) lateCompared.1 :=
    Runtime.schedule_trace profile lateWoken (waiterEntry ++ [.service (.compare 1)])
      ⟨lateCompared.1, lateEntered.2 ++ lateCompared.2⟩ (by rfl)
  exact ⟨certified_suffix_completes Runtime.Trace.nil,
    certified_suffix_completes (Runtime.schedule_trace profile lateWoken mixedActions mixed (checked_ok _ _)),
    certified_suffix_completes (Runtime.schedule_trace profile lateWoken [.issue 0, .issue 0]
      beforeSyscall (checked_ok _ _)),
    certified_suffix_completes (Runtime.schedule_trace profile lateWoken waiterEntry lateEntered (checked_ok _ _)),
    certified_suffix_completes compared,
    certified_suffix_completes (Runtime.schedule_trace profile lateWoken resumedActions resumed (checked_ok _ _)),
    certified_suffix_completes (Runtime.schedule_trace profile lateWoken returnedActions returned (checked_ok _ _))⟩

/-- The older pending-only completion API retains its stronger arbitrary
full-width private clobber contract while also retaining the artifact binding. -/
theorem pending_private_certificate (flags rcx r11 : Word) :
    ∃ after, Clients.Notification.FinishesWithin 3 cohort 0 0 flags rcx r11 lateEntered.1 after ∧
      EDSL.FutexNotificationCertificate.Specification candidate cohort after 1 publisher 0 0 := by
  obtain ⟨_, clear, word, _, _, certificate⟩ := notification_suffix
    (Runtime.schedule_trace profile lateWoken waiterEntry lateEntered (checked_ok _ _))
  exact certificate.complete_pending word clear
    (show lateEntered.1.suspended.pending 0 = some
      ((lateEntered.1.suspended.pending 0).get (by rfl)) from rfl) flags rcx r11

/-- Once resume has happened, the enabled RET preserves the complete actual
historical context. No new private clobber is requested or silently substituted. -/
theorem resumed_keeps_history :
    ∃ after actual,
      Clients.Notification.CompletesWithin 1 cohort 0 0 resumed.1 after ∧
      after.suspended.machine.workers[0]? = some actual ∧
      actual.context = Examples.FutexClient.waiter.returned
        ((resumed.1.suspended.machine.workers[0]?).get (by rfl)).context ∧
      EDSL.FutexNotificationCertificate.Specification candidate cohort after 1 publisher 0 0 := by
  obtain ⟨_, _, _, _, _, certificate⟩ := notification_suffix
    (Runtime.schedule_trace profile lateWoken resumedActions resumed (checked_ok _ _))
  obtain ⟨after, actual, completion, found, history⟩ := Clients.Notification.resumed_completes (client := Examples.FutexClient.waiter)
    certificate.admitted
    (show cohort.clients[0]? = some Examples.FutexClient.waiter from rfl) rfl
    (show resumed.1.suspended.machine.workers[0]? = some
      ((resumed.1.suspended.machine.workers[0]?).get (by rfl)) from rfl)
    (outcome := .waitAgain)
    (flags := 0x123456789abcdef0) (rcx := 0xfedcba9876543210) (r11 := 0x8877665544332211)
    (by
      change Threads.Context.mk _ _ _ = Threads.Context.mk _ _ _
      congr 1
      funext register
      cases register <;> rfl) rfl rfl rfl
  have admitted : Admitted cohort after := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, valid⟩ := completion
    exact valid
  exact ⟨after, actual, completion, found, history, certificate.of_admitted admitted⟩

/-- An already returned actual worker needs zero steps, so its complete private
context (including high historical clobbers) is literally the same worker. -/
theorem returned_keeps_history :
    Clients.Notification.CompletesWithin 0 cohort 0 0 returned.1 returned.1 ∧
    EDSL.FutexNotificationCertificate.Specification candidate cohort returned.1 1 publisher 0 0 := by
  obtain ⟨_, _, _, _, _, certificate⟩ := notification_suffix
    (Runtime.schedule_trace profile lateWoken returnedActions returned (checked_ok _ _))
  refine ⟨?_, certificate⟩
  apply Clients.Notification.returned_completes certificate.admitted
    (show cohort.clients[0]? = some Examples.FutexClient.waiter from rfl) rfl
    (show returned.1.suspended.machine.workers[0]? = some
      ((returned.1.suspended.machine.workers[0]?).get (by rfl)) from rfl)
  rfl

end EDSL.Tests.FutexNotificationCertificate

#audit_edsl
