/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientCoverage
import EDSL.ELF.Loader

namespace EDSL.FutexClientCertificate
open X86 OS OS.Futex OS.Futex.Clients

/-- This profile is separate from the invocation-only futex stub profiles. -/
def accepts (candidate : List Byte) : Bool := decide (candidate = publishingBytes)

/-- Exact artifact bytes at the current code of this actual publishing member.
Equality to a byte list alone does not establish this binding. -/
structure Binding (candidate : List Byte) (cohort : Cohort) (state : Futex.State)
    (worker : Nat) (client : Client) : Prop where
  exactBytes : candidate = publishingBytes
  length : candidate.length = 32
  member : cohort.clients[worker]? = some client
  publisher : client.role = .publishPayloadWake
  code : CodeAt state.suspended.machine.memory client.entry.rip candidate

theorem bind (candidate : List Byte) (accepted : accepts candidate = true)
    {cohort : Cohort} {state : Futex.State} {worker : Nat} {client : Client}
    (member : cohort.clients[worker]? = some client) (publisher : client.role = .publishPayloadWake)
    (code : CodeAt state.suspended.machine.memory client.entry.rip candidate) :
    Binding candidate cohort state worker client := by
  have exactBytes : candidate = publishingBytes := of_decide_eq_true accepted
  refine ⟨exactBytes, ?_, member, publisher, code⟩
  rw [exactBytes]
  decide

/-- All actual supported issue/drain demands and current service guards have
positive physical lifts. Successful replay or future service is not a premise. -/
structure Coverage (cohort : Cohort) (state : Futex.State) : Prop where
  issue : ∀ worker suspended observation,
    Suspend.issue state.suspended worker = .ok (suspended, observation) →
    ∃ after, Physical.issue cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Admitted cohort after
  drain : ∀ worker suspended observation,
    Suspend.drain state.suspended worker = .ok (suspended, observation) →
    ∃ after, Physical.drain cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Admitted cohort after
  service : ∀ action, Clients.Guard state action →
    ∃ after, Futex.step cohort.profile.service state action = .ok after ∧ Admitted cohort after
  demand : ∀ action observation, Clients.Demand state action observation →
    ∃ after, Runtime.step cohort.profile state action = .ok (after, observation) ∧ Admitted cohort after

/-- A current typed ready call for the bound publishing worker enables both
resume and its actual protected RET. Full raw RAX, arbitrary private clobbers,
present RAM and every peer record are included in the conclusion. This does
not promise that the service will eventually make a call ready. -/
def ReadyReturn (cohort : Cohort) (state : Futex.State) (worker : Nat) (client : Client) : Prop :=
  ∀ (invocation : Nat) (call : Call) (outcome : Outcome call.op) (origin : Origin),
    state.calls invocation = some call → call.worker = worker → call.phase = .ready outcome origin →
    ∀ flags rcx r11 : Word, ∃ resumed after returned,
      resumeReady cohort.profile.service state invocation flags rcx r11 = .ok resumed ∧
      Physical.issue cohort.profile resumed worker = .ok (after, .machine (.retired worker none)) ∧
      after.suspended.machine.workers[worker]? = some returned ∧
      returned.returned = true ∧ returned.buffer = [] ∧
      returned.context.registers .rax = outcome.raw ∧ returned.context.rip = client.returnTarget ∧
      returned.context.registers .rsp = client.entry.registers .rsp + 8 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      after.suspended.machine.memory = state.suspended.machine.memory ∧
      (∀ query, query ≠ worker →
        after.suspended.machine.workers[query]? = state.suspended.machine.workers[query]? ∧
        after.suspended.pending query = state.suspended.pending query) ∧
      Admitted cohort resumed ∧ Admitted cohort after

/-- An actual retired XCHG at this bound member has its prescribed payload
already visible, publishes W=1, and positively lifts to the managed machine.
The publication facts come from the checked generic client theorem. -/
def Publication (cohort : Cohort) (state : Futex.State) (worker : Nat) (client : Client) : Prop :=
  ∀ suspended event,
    Suspend.issue state.suspended worker = .ok (suspended, .machine (.retired worker (some event))) →
    event.address = cohort.registration.address ∧ event.after = 1 ∧
    loadDWord state.suspended.machine.memory (client.entry.registers .rsi) = .ok 0x11223344 ∧
    ∃ after, Physical.issue cohort.profile state worker = .ok (after, .machine (.retired worker (some event))) ∧
      after.suspended = suspended ∧
      loadDWord after.suspended.machine.memory (client.entry.registers .rsi) = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 ∧ Admitted cohort after

structure Specification (candidate : List Byte) (cohort : Cohort) (state : Futex.State)
    (worker : Nat) (client : Client) : Prop where
  binding : Binding candidate cohort state worker client
  admitted : Admitted cohort state
  coverage : Coverage cohort state
  returns : ReadyReturn cohort state worker client
  publication : Publication cohort state worker client

theorem sound (candidate : List Byte) (accepted : accepts candidate = true)
    {cohort : Cohort} {state : Futex.State} {worker : Nat} {client : Client}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some client) (publisher : client.role = .publishPayloadWake)
    (code : CodeAt state.suspended.machine.memory client.entry.rip candidate) :
    Specification candidate cohort state worker client := by
  refine ⟨bind candidate accepted member publisher code, admitted,
    ⟨fun _ _ _ actual => Clients.issue_lift admitted actual,
     fun _ _ _ actual => Clients.drain_lift admitted actual,
     fun _ enabled => Clients.service_lift admitted enabled,
     fun _ _ demand => Clients.demand_enabled admitted demand⟩, ?_, ?_⟩
  · intro invocation call outcome origin found owner ready flags rcx r11
    obtain ⟨resumed, after, returned, actualClient, actualMember, resume, issue, live, done, empty,
      raw, target, stackPointer, privateFlags, privateRcx, privateR11, memory, peers, resumedAd, afterAd⟩ :=
      Clients.ready_ret_enabled admitted found ready flags rcx r11
    rw [owner, member] at actualMember
    cases Option.some.inj actualMember
    exact ⟨resumed, after, returned, resume, by simpa only [owner] using issue,
      by simpa only [owner] using live, done, empty, raw, target, stackPointer,
      privateFlags, privateRcx, privateR11, memory, by simpa only [owner] using peers, resumedAd, afterAd⟩
  · intro suspended event actual
    obtain ⟨actualClient, actualMember, _, address, replacement, beforePayload, afterPayload, word⟩ :=
      Clients.publisher_exchange_publishes_payload admitted actual
    have same : actualClient = client := Option.some.inj (actualMember.symm.trans member)
    subst actualClient
    obtain ⟨after, issued, physical, afterAd⟩ := Clients.issue_lift admitted actual
    refine ⟨address, replacement, ?_, after, issued, physical, ?_, ?_, afterAd⟩
    · simpa only [Client.store, Role.value, publisher] using beforePayload
    · rw [physical]
      simpa only [Client.store, Role.value, publisher] using afterPayload
    · rw [physical]
      exact word

/-- Exact artifact binding and its positive contracts survive a whole actual
physical prefix. A successful managed replay is a conclusion of the generic
prefix lift, rather than an assumption supplied by the certificate caller. -/
theorem Specification.lift_prefix {candidate : List Byte} {cohort : Cohort} {state : Futex.State}
    {worker : Nat} {client : Client} (certificate : Specification candidate cohort state worker client)
    {actions : List Runtime.Action} {observations : List Runtime.Observation} {suspended : Suspend.State}
    (trace : Clients.MachineTrace state.suspended actions observations suspended) :
    ∃ after, Runtime.Trace cohort.profile state actions observations after ∧ after.suspended = suspended ∧
      Specification candidate cohort after worker client := by
  obtain ⟨after, lifted, physical, afterAd⟩ := trace.lift certificate.admitted rfl
  have accepted : accepts candidate = true := by simp [accepts, certificate.binding.exactBytes]
  have code : CodeAt after.suspended.machine.memory client.entry.rip candidate := by
    rw [certificate.binding.exactBytes]
    simpa only [certificate.binding.publisher, Role.bytes] using
      (afterAd.protected worker client certificate.binding.member).2.2.1
  exact ⟨after, lifted, physical,
    sound candidate accepted afterAd certificate.binding.member certificate.binding.publisher code⟩

/-- The generic no-reset theorem applies to later covered runtime prefixes,
including drains from producers which have already returned. -/
theorem Specification.published_word_trace {candidate : List Byte} {cohort : Cohort} {state : Futex.State}
    {worker : Nat} {client : Client} (certificate : Specification candidate cohort state worker client)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    {actions : List Runtime.Action} {observations : List Runtime.Observation} {after : Futex.State}
    (trace : Runtime.Trace cohort.profile state actions observations after) :
    loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 :=
  Clients.published_word_trace certificate.admitted published trace

/-- Full literal ELF parsing/loading and exact entry code are tied to the same
current admitted publishing member. Loading itself does not create admission;
its resource, cohort and environmental obligations remain explicit. -/
theorem loaded_sound (file candidate : List Byte) (image : ELF.Image)
    (parsed : ELF.parse file = .ok image) (checked : ELF.checkEntry file image candidate = true)
    (accepted : accepts candidate = true) (prior : AddressSpace.Space)
    (free : ELF.fresh image prior = true)
    {cohort : Cohort} {state : Futex.State} {worker : Nat} {client : Client}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some client) (publisher : client.role = .publishPayloadWake)
    (memory : state.suspended.machine.memory = AddressSpace.toMemory (ELF.install file image prior))
    (entry : client.entry.rip = ELF.codeAddress image) :
    ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
      Specification candidate cohort state worker client := by
  refine ⟨ELF.load_success file prior image parsed free, sound candidate accepted admitted member publisher ?_⟩
  rw [memory, entry]
  exact ELF.checked_entry_code file image candidate prior checked

end EDSL.FutexClientCertificate
