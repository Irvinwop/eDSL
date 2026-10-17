/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexClientCertificate
import EDSL.OS.Futex.ClientNotification

set_option warningAsError true

namespace EDSL.FutexNotificationCertificate
open X86 OS OS.Futex OS.Futex.Clients

/-- Add the independent single-waiter policy to the existing exact publisher
certificate. The older certificate and its admission keep their meanings.
Notification consequences are supplied by the trace theorems below; this
structure adds no future-execution or scheduler-success premise. -/
structure Specification (candidate : List Byte) (cohort : Cohort) (state : Futex.State)
    (publisher : Nat) (client : Client) (waiter : Nat) (expected : BitVec 32) : Prop
    extends FutexClientCertificate.Specification candidate cohort state publisher client where
  policy : Clients.Notification.Policy cohort waiter expected

theorem sound (candidate : List Byte)
    (accepted : FutexClientCertificate.accepts candidate = true)
    {cohort : Cohort} {state : Futex.State} {publisher waiter : Nat} {client : Client}
    {expected : BitVec 32}
    (admitted : Admitted cohort state)
    (member : cohort.clients[publisher]? = some client)
    (publishes : client.role = .publishPayloadWake)
    (code : CodeAt state.suspended.machine.memory client.entry.rip candidate)
    (policy : Clients.Notification.Policy cohort waiter expected) :
    Specification candidate cohort state publisher client waiter expected :=
  ⟨FutexClientCertificate.sound candidate accepted admitted member publishes code, policy⟩

/-- Current protected code and the immutable cohort retain the same artifact
binding after any supported transition. No byte equality is used as a substitute
for current code/resource admission. -/
theorem Specification.of_admitted
    {candidate : List Byte} {cohort : Cohort} {before after : Futex.State}
    {publisher waiter : Nat} {client : Client} {expected : BitVec 32}
    (certificate : Specification candidate cohort before publisher client waiter expected)
    (admitted : Admitted cohort after) :
    Specification candidate cohort after publisher client waiter expected := by
  have accepted : FutexClientCertificate.accepts candidate = true := by
    simp [FutexClientCertificate.accepts, certificate.binding.exactBytes]
  have code : CodeAt after.suspended.machine.memory client.entry.rip candidate := by
    rw [certificate.binding.exactBytes]
    simpa only [certificate.binding.publisher, Role.bytes] using
      (admitted.protected publisher client certificate.binding.member).2.2.1
  exact sound candidate accepted admitted certificate.binding.member
    certificate.binding.publisher code certificate.policy

private theorem publication_trace {cohort : Cohort} {before after : Futex.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    PublicationFrame cohort before.suspended.machine.memory after.suspended.machine.memory := by
  induction trace with
  | nil => exact fun _ _ _ published => published
  | cons first tail ih =>
    have frame := Clients.runtime_publication admitted first
    have rest := ih (Clients.admitted_step admitted first)
    intro worker client member published
    exact rest worker client member (frame worker client member published)

/-- Actual retirement by the bound publisher, any mixed prefix, its associated
captured WAKE1, and any later mixed suffix establish notification safety. The
actual saved request identifies that publisher's invocation. Both W=1 and its
payload remain current, including across drains from returned peers. -/
theorem Specification.notification
    {candidate : List Byte} {cohort : Cohort}
    {before exchanged waking afterWake after : Futex.State}
    {publisher waiter invocation pin : Nat} {client : Client} {expected : BitVec 32}
    {event : AtomicEvent} {selected : Option Nat}
    {middleActions laterActions : List Runtime.Action}
    {prefixObs suffixObs : List Runtime.Observation}
    (certificate : Specification candidate cohort before publisher client waiter expected)
    (exchange : Physical.issue cohort.profile before publisher =
      .ok (exchanged, .machine (.retired publisher (some event))))
    (between : Runtime.Trace cohort.profile exchanged middleActions prefixObs waking)
    (associated : waking.calls invocation = some ⟨publisher, .wakeOne, pin, .entered⟩)
    (wake : wakeOne waking invocation selected = .ok afterWake)
    (later : Runtime.Trace cohort.profile afterWake laterActions suffixObs after) :
    (∃ saved, waking.suspended.pending publisher = some saved ∧ saved.identifier = invocation ∧
      client.Family saved.request) ∧
    OS.Futex.Notification.NoQueuedWait after waiter ∧
    loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧
    client.Published after.suspended.machine.memory ∧
    Specification candidate cohort after publisher client waiter expected := by
  obtain ⟨⟨observed, saved, member, _, pending, identity, family⟩, clear, word, admitted⟩ :=
    Clients.Notification.exchange_wake_trace certificate.policy certificate.admitted
      exchange between associated wake later
  have same : observed = client := Option.some.inj (member.symm.trans certificate.binding.member)
  subst observed
  have actual := Physical.issue_projection _ _ _ _ exchange
  obtain ⟨publishing, atPublishing, _, _, _, _, payload, _⟩ :=
    Clients.publisher_exchange_publishes_payload certificate.admitted actual
  have samePublisher : publishing = client :=
    Option.some.inj (atPublishing.symm.trans certificate.binding.member)
  subst publishing
  have first : Runtime.step cohort.profile before (.issue publisher) =
      .ok (exchanged, .physical (.machine (.retired publisher (some event)))) := by
    simp [Runtime.step, exchange]
  have exchangedAdmitted := Clients.admitted_step certificate.admitted first
  have published : client.Published exchanged.suspended.machine.memory := fun _ => payload
  have middlePublished := publication_trace exchangedAdmitted between
    publisher client certificate.binding.member published
  have wakingAdmitted := exchangedAdmitted.trace between
  have wakeStep : Runtime.step cohort.profile waking (.service (.wake invocation selected)) =
      .ok (afterWake, .serviced (.wake invocation selected)) := by
    simp [Runtime.step, Futex.step, wake, Except.mapError]
  have afterPublished := Clients.runtime_publication wakingAdmitted wakeStep
    publisher client certificate.binding.member middlePublished
  have finalPublished := publication_trace (Clients.admitted_step wakingAdmitted wakeStep) later
    publisher client certificate.binding.member afterPublished
  exact ⟨⟨saved, pending, identity, family⟩, clear, word, finalPublished,
    certificate.of_admitted admitted⟩

/-- A currently pending designated WAIT has an actual suffix of at most three
service/issue transitions after notification. Its typed call is derived from
the captured request; flags, RCX and R11 are arbitrary full private clobbers.
This existential enabled suffix imposes no fairness on an arbitrary scheduler. -/
theorem Specification.complete_pending
    {candidate : List Byte} {cohort : Cohort} {state : Futex.State}
    {publisher waiter : Nat} {client : Client} {expected : BitVec 32} {saved : Suspend.Saved}
    (certificate : Specification candidate cohort state publisher client waiter expected)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : OS.Futex.Notification.NoQueuedWait state waiter)
    (pending : state.suspended.pending waiter = some saved) (flags rcx r11 : Word) :
    ∃ after, Clients.Notification.FinishesWithin 3 cohort waiter expected flags rcx r11 state after ∧
      Specification candidate cohort after publisher client waiter expected := by
  obtain ⟨after, completion, admitted⟩ := Clients.Notification.pending_worker_finishes
    certificate.policy certificate.admitted published clear pending flags rcx r11
  exact ⟨after, completion, certificate.of_admitted admitted⟩

/-- Every current designated WAIT stage has an actual suffix through RET after
notification. The bound counts at most six runtime transitions; resumed or
returned workers retain their historical private context. Current resources
derive enabledness without a future-success or scheduler-fairness premise. -/
theorem Specification.complete
    {candidate : List Byte} {cohort : Cohort} {state : Futex.State}
    {publisher waiter : Nat} {client : Client} {expected : BitVec 32}
    (certificate : Specification candidate cohort state publisher client waiter expected)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : OS.Futex.Notification.NoQueuedWait state waiter) :
    ∃ after, Clients.Notification.CompletesWithin 6 cohort waiter expected state after ∧
      Specification candidate cohort after publisher client waiter expected := by
  obtain ⟨after, completion⟩ := Clients.Notification.worker_completes
    certificate.policy certificate.admitted published clear
  have admitted : Admitted cohort after := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, valid⟩ := completion
    exact valid
  exact ⟨after, completion, certificate.of_admitted admitted⟩

/-- Restricted ELF loading binds the same literal publisher bytes and entry.
The current cohort/resources and independent waiter policy remain explicit
caller obligations; loading establishes no whole-process or kernel theorem. -/
theorem loaded_sound (file candidate : List Byte) (image : ELF.Image)
    (parsed : ELF.parse file = .ok image) (checked : ELF.checkEntry file image candidate = true)
    (accepted : FutexClientCertificate.accepts candidate = true) (prior : AddressSpace.Space)
    (free : ELF.fresh image prior = true)
    {cohort : Cohort} {state : Futex.State} {publisher waiter : Nat} {client : Client}
    {expected : BitVec 32}
    (admitted : Admitted cohort state)
    (member : cohort.clients[publisher]? = some client)
    (publishes : client.role = .publishPayloadWake)
    (memory : state.suspended.machine.memory = AddressSpace.toMemory (ELF.install file image prior))
    (entry : client.entry.rip = ELF.codeAddress image)
    (policy : Clients.Notification.Policy cohort waiter expected) :
    ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
      Specification candidate cohort state publisher client waiter expected := by
  obtain ⟨loaded, bound⟩ := FutexClientCertificate.loaded_sound file candidate image parsed checked
    accepted prior free admitted member publishes memory entry
  exact ⟨loaded, ⟨bound, policy⟩⟩

end EDSL.FutexNotificationCertificate
