/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientLiftCore
import EDSL.OS.Futex.ClientModel
import EDSL.OS.Futex.ClientControl
import EDSL.OS.Futex.ClientAdmission
import EDSL.OS.Futex.ClientAdmissionFrames
import EDSL.OS.Futex.ClientPublication

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

/-- Actual FIFO heads carry their current ordinary-store grant, including
heads belonging to returned workers. No peer is required to be quiescent. -/
theorem drain_ready_of_fifo {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (fifo : FIFOAuthorized cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    Physical.Ready cohort.profile state.authority observation := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, live, buffer, committed, installed⟩ :=
    TSO.drain_ok _ _ _ drained
  have observedEq := congrArg Prod.snd same
  have drainedEq := congrArg Prod.snd installed
  dsimp only at observedEq drainedEq
  rw [observedEq, drainedEq]
  exact fifo worker selected live head (by simp [buffer])

/-- An immutable family checks the service's complete register ABI while
retaining the request's own historical capture RAM. -/
theorem Client.family_classifies {cohort : Cohort} {worker : Nat} {client : Client}
    {request : SyscallRequest} (descriptor : Descriptor cohort worker client)
    (family : client.Family request) :
    classify request = .ok client.operation ∧
      request.user.registers .rdi = cohort.registration.address := by
  obtain ⟨caller, same⟩ := family
  have canonical : ∀ memory, classify (client.request memory) = .ok client.operation ∧
      (client.request memory).user.registers .rdi = cohort.registration.address := by
    intro memory
    obtain ⟨address, fourth, fifth, sixth, role⟩ := descriptor
    cases kind : client.role with
    | wait expected =>
      rw [kind] at role
      have expectedValue : client.entry.registers .rdx = expected.setWidth 64 := by
        exact role.1
      simp [Client.request, Client.callContext, Client.callStage, Stage.context, Stage.offset,
        Client.operation, kind, MachineThreads.contextState, classify, address,
        fourth, fifth, sixth, expectedValue]
    | publishPayloadWake =>
      simp [Client.request, Client.callContext, Client.callStage, Stage.context, Stage.offset,
        Client.operation, kind, MachineThreads.contextState, classify, address,
        fourth, fifth, sixth]
    | payloadPeer => exact (caller kind).elim
  simpa only [← same] using canonical request.user.memory

theorem Client.family_rsp {client : Client} {request : SyscallRequest}
    (family : client.Family request) :
    request.user.registers .rsp = client.entry.registers .rsp := by
  rw [family.2]
  simp [Client.request, Client.callContext, Client.callStage, Stage.context, MachineThreads.contextState]

/-- Exact client bytes protect the actual saved continuation's RET, including
the publisher's suffix at offset fourteen. No physical decoder gate is added. -/
theorem Client.family_ret_code {client : Client} {request : SyscallRequest} {memory : Memory}
    (family : client.Family request) (code : CodeAt memory client.entry.rip client.role.bytes) :
    CodeAt memory request.continuation [0xc3] := by
  obtain ⟨caller, same⟩ := family
  have next : request.continuation = client.entry.rip +
      BitVec.ofNat 64 (if client.role = .publishPayloadWake then 31 else 12) := by
    rw [same]
    cases kind : client.role with
    | wait expected =>
      simp [Client.request, Client.callContext, Client.callStage, Stage.context, Stage.offset,
        kind, BitVec.add_assoc]
    | publishPayloadWake =>
      simp [Client.request, Client.callContext, Client.callStage, Stage.context, Stage.offset,
        kind, BitVec.add_assoc]
    | payloadPeer => exact (caller kind).elim
  rw [next]
  cases kind : client.role with
  | wait expected =>
    simp only [kind, reduceCtorEq, ↓reduceIte] at code ⊢
    apply code.window 12 (by simp [Role.bytes, Examples.FutexStubs.Profile.bytes])
    · have bound := code.1
      change client.entry.rip.toNat + 13 ≤ 2^64 at bound
      omega
    · intro index byte present
      cases index with
      | zero => simpa [Role.bytes, Examples.FutexStubs.Profile.bytes] using present
      | succ index => simp at present
  | publishPayloadWake =>
    simp only [kind, ↓reduceIte] at code ⊢
    apply code.window 31 (by simp [Role.bytes, publishingBytes, Examples.FutexStubs.Profile.bytes])
    · have bound := code.1
      change client.entry.rip.toNat + 32 ≤ 2^64 at bound
      omega
    · intro index byte present
      cases index with
      | zero => simpa [Role.bytes, publishingBytes, Examples.FutexStubs.Profile.bytes] using present
      | succ index => simp at present
  | payloadPeer => exact (caller kind).elim

/-- The concrete exact request family and current full code/return loans
positively enable ready completion and the subsequent physical RET. Current
RAM, full raw RAX and arbitrary full private clobbers survive the return. -/
theorem ready_ret_enabled_of_family {cohort : Cohort} {state : Futex.State}
    {invocation : Nat} {call : Call} {outcome : Outcome call.op} {origin : Origin}
    (valid : Runtime.Invariant cohort.profile state) (protection : Protected cohort state)
    (families : ∀ saved, state.suspended.pending call.worker = some saved →
      CallFamily cohort call.worker saved.request)
    (found : state.calls invocation = some call) (ready : call.phase = .ready outcome origin)
    (flags rcx r11 : Word) :
    ∃ resumed after returned client,
      cohort.clients[call.worker]? = some client ∧
      resumeReady cohort.profile.service state invocation flags rcx r11 = .ok resumed ∧
      Physical.issue cohort.profile resumed call.worker = .ok (after, .machine (.retired call.worker none)) ∧
      after.suspended.machine.workers[call.worker]? = some returned ∧
      returned.returned = true ∧ returned.buffer = [] ∧
      returned.context.registers .rax = outcome.raw ∧ returned.context.rip = client.returnTarget ∧
      returned.context.registers .rsp = client.entry.registers .rsp + 8 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      after.suspended.machine.memory = state.suspended.machine.memory ∧
      (∀ query, query ≠ call.worker →
        after.suspended.machine.workers[query]? = state.suspended.machine.workers[query]? ∧
        after.suspended.pending query = state.suspended.pending query) ∧
      Runtime.Invariant cohort.profile resumed ∧ Runtime.Invariant cohort.profile after := by
  obtain ⟨saved, pending, _⟩ := (valid.service.calls _ _ found).saved
  obtain ⟨client, member, family⟩ := families saved pending
  obtain ⟨codeLoan, stackLoan, code, stack, canonicalTarget, codeFrame, stackFrame⟩ :=
    protection call.worker client member
  have savedStack : readWord state.suspended.machine.memory (saved.request.user.registers .rsp) =
      .ok client.returnTarget := by rw [client.family_rsp family]; exact stack
  obtain ⟨resumed, after, returned, resume, issue, live, done, empty, raw, target,
    stackPointer, privateFlags, privateRcx, privateR11, memory, peers, resumedInv, afterInv⟩ :=
    LiftCore.resume_ret_enabled valid found ready pending (client.family_ret_code family code)
      savedStack canonicalTarget flags rcx r11
  exact ⟨resumed, after, returned, client, member, resume, issue, live, done, empty, raw,
    target, by simpa only [client.family_rsp family] using stackPointer,
    privateFlags, privateRcx, privateR11, memory, peers, resumedInv, afterInv⟩

/-- Atomic replay rights come from actual decoded finite control and the
current fixed producer handle. Ordinary retirements do not substitute for
the independent enqueue-authorization theorem. -/
theorem issue_ready {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    Physical.Ready cohort.profile state.authority observation := by
  have code : CurrentCode cohort state.suspended := fun i client member =>
    (admitted.protected i client member).2.2.1
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running free decoded empty executed stepped user continuation => trivial
  | parked live running pending => trivial
  | @machine machine observation free issued =>
    obtain ⟨selected, instruction, live, running, decoded, executed, effect⟩ :=
      TSO.issue_effect _ _ _ issued
    cases effect with
    | queued pending aligned data executed writable output => trivial
    | ordinary pending unlocked loads executed memory => trivial
    | returned pending unlocked instruction executed memory => trivial
    | blocked pending classified nonempty => trivial
    | atomic pending classified empty data executed transition address accumulator =>
      obtain ⟨client, atClient, publisher, operand, accumulator, instructionEq⟩ :=
        producer_exchange admitted.control code admitted.static.descriptors live running free decoded classified
      have descriptor := (admitted.static.descriptors worker client atClient).2.2.2.2
      rw [publisher] at descriptor
      obtain ⟨_, access, handle, atAccess, fixed, actor, target, owner, ticket⟩ := descriptor
      refine ⟨access, handle, atAccess, ?_, target.trans (operand.symm.trans address.symm)⟩
      simp [Atomics.authorize, admitted.fixed _ _ fixed, actor]

theorem drain_ready {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    Physical.Ready cohort.profile state.authority observation :=
  drain_ready_of_fifo admitted.fifo actual

/-- Present concrete client control discharges the core's full entry ABI.
Request RAM remains the current RAM at this actual instruction. -/
theorem entry_support {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : LiftCore.EntrySupport cohort.profile state := by
  refine ⟨cohort.registration, admitted.registration, admitted.keeper, admitted.target, ?_⟩
  intro worker selected live running free decoded
  obtain ⟨client, atClient, controlled⟩ := admitted.control worker selected live
  have code := (admitted.protected worker client atClient).2.2.1
  have family : client.Family (LiftCore.entryRequest state.suspended selected) := by
    cases controlled with
    | running stage supported context _ _ fifo =>
      have expected := decode_stage client stage state.suspended.machine.memory supported code
      rw [TSO.sharedState, context] at decoded
      have same := Except.ok.inj (expected.symm.trans decoded)
      obtain ⟨caller, callContext⟩ := stage_syscall supported same
      refine ⟨caller, ?_⟩
      simp only [LiftCore.entryRequest, Client.request, TSO.sharedState, context, callContext]
      rfl
    | entered saved pending _ _ _ _ _ _ => simp [free] at pending
    | resumed outcome flags rcx r11 caller context _ _ _ _ =>
      have expected := decode_resumed client state.suspended.machine.memory outcome.raw flags rcx r11 caller code
      rw [TSO.sharedState, context] at decoded
      cases expected.symm.trans decoded
    | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [running] at done
  exact ⟨client.operation, client.family_classifies (admitted.static.descriptors _ _ atClient) family⟩

/-- Current admission positively enables the exact physical issue. This
intermediate theorem is independent of admission's preservation proof. -/
theorem issue_enabled {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.issue cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Runtime.Invariant cohort.profile after ∧
      Atomics.History state.authority after.authority :=
  LiftCore.issue_enabled admitted.runtime (entry_support admitted) (issue_ready admitted actual) actual

theorem drain_enabled {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.drain cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Runtime.Invariant cohort.profile after ∧
      Atomics.History state.authority after.authority :=
  LiftCore.drain_enabled admitted.runtime (drain_ready admitted actual) actual

/-- Rebuild all current admission resources after an actual accepted runtime
step and its proved concrete control. This is a theorem, not an admission
field or a callback promising that admission preserves itself. -/
theorem admitted_frame {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result)
    (control : Control cohort result.1.suspended) : Admitted cohort result.1 :=
  admitted.advance actual control

/-- Every accepted actual adapter step preserves the finite controls, all
current grants and every cohort loan. The read-frame premises for control
are derived from the actual physical footprints and current resources. -/
theorem admitted_step {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result) : Admitted cohort result.1 := by
  apply admitted_frame admitted actual
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      have physical := Physical.issue_projection _ _ _ _ issued
      exact issue_control admitted.control
        (fun i client member => (admitted.protected i client member).2.2.1)
        admitted.stackViews (fun i client member => (admitted.protected i client member).2.2.2.2.1)
        (issue_publication admitted physical) physical
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      have physical := Physical.drain_projection _ _ _ _ drained
      exact drain_control admitted.control (drain_publication admitted physical) physical
  | service serviceAction =>
    cases serviced : Futex.step cohort.profile.service state serviceAction with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      exact service_control admitted.control admitted.static.descriptors admitted.runtime.service serviced

theorem Admitted.trace {cohort : Cohort} {before after : Futex.State}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (trace : Runtime.Trace cohort.profile before actions observations after) : Admitted cohort after := by
  induction trace with
  | nil => exact admitted
  | cons first tail ih => exact ih (admitted_step admitted first)

theorem Admitted.schedule {cohort : Cohort} {state : Futex.State}
    {actions : List Runtime.Action} {result : Futex.State × List Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.schedule cohort.profile state actions = .ok result) : Admitted cohort result.1 :=
  admitted.trace (Runtime.schedule_trace _ _ _ _ actual)

/-- Every supported actual issue has an enabled lift with the identical
physical output and observation, and current admission survives it. -/
theorem issue_lift {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.issue cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Admitted cohort after := by
  obtain ⟨after, issued, physical, invariant, history⟩ := issue_enabled admitted actual
  have runtime : Runtime.step cohort.profile state (.issue worker) =
      .ok (after, .physical observation) := by simp [Runtime.step, issued]
  exact ⟨after, issued, physical, admitted_step admitted runtime⟩

theorem drain_lift {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.drain cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Admitted cohort after := by
  obtain ⟨after, drained, physical, invariant, history⟩ := drain_enabled admitted actual
  have runtime : Runtime.step cohort.profile state (.drain worker) =
      .ok (after, .physical observation) := by simp [Runtime.step, drained]
  exact ⟨after, drained, physical, admitted_step admitted runtime⟩

abbrev Guard := LiftCore.Guard

/-- Current service phase and eligibility guards suffice for a checked step;
neither successful future service nor a caller-chosen raw result is assumed. -/
theorem service_lift {cohort : Cohort} {state : Futex.State} {action : Futex.Action}
    (admitted : Admitted cohort state) (enabled : Guard state action) :
    ∃ after, Futex.step cohort.profile.service state action = .ok after ∧ Admitted cohort after := by
  obtain ⟨after, serviced, invariant, history⟩ := LiftCore.service_enabled admitted.runtime enabled
  have runtime : Runtime.step cohort.profile state (.service action) = .ok (after, .serviced action) := by
    simp [Runtime.step, serviced, Except.mapError]
  exact ⟨after, serviced, admitted_step admitted runtime⟩

/-- The current actual ready call, exact captured family and current protected
resources suffice for actual completion and RET. No future success is assumed. -/
theorem ready_ret_enabled {cohort : Cohort} {state : Futex.State}
    {invocation : Nat} {call : Call} {outcome : Outcome call.op} {origin : Origin}
    (admitted : Admitted cohort state)
    (found : state.calls invocation = some call) (ready : call.phase = .ready outcome origin)
    (flags rcx r11 : Word) :
    ∃ resumed after returned client,
      cohort.clients[call.worker]? = some client ∧
      resumeReady cohort.profile.service state invocation flags rcx r11 = .ok resumed ∧
      Physical.issue cohort.profile resumed call.worker = .ok (after, .machine (.retired call.worker none)) ∧
      after.suspended.machine.workers[call.worker]? = some returned ∧
      returned.returned = true ∧ returned.buffer = [] ∧
      returned.context.registers .rax = outcome.raw ∧ returned.context.rip = client.returnTarget ∧
      returned.context.registers .rsp = client.entry.registers .rsp + 8 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      after.suspended.machine.memory = state.suspended.machine.memory ∧
      (∀ query, query ≠ call.worker →
        after.suspended.machine.workers[query]? = state.suspended.machine.workers[query]? ∧
        after.suspended.pending query = state.suspended.pending query) ∧
      Admitted cohort resumed ∧ Admitted cohort after := by
  obtain ⟨resumed, after, returned, client, member, resume, issue, live, done, empty, raw,
    target, stackPointer, privateFlags, privateRcx, privateR11, memory, peers, resumedInv, afterInv⟩ :=
    ready_ret_enabled_of_family admitted.runtime admitted.protected
      (fun _ pending => admitted.pending_family pending) found ready flags rcx r11
  have runtimeResume : Runtime.step cohort.profile state (.service (.resume invocation flags rcx r11)) =
      .ok (resumed, .serviced (.resume invocation flags rcx r11)) := by
    simp [Runtime.step, Futex.step, resume, Except.mapError]
  have resumedAd := admitted_step admitted runtimeResume
  have runtimeRet : Runtime.step cohort.profile resumed (.issue call.worker) =
      .ok (after, .physical (.machine (.retired call.worker none))) := by simp [Runtime.step, issue]
  exact ⟨resumed, after, returned, client, member, resume, issue, live, done, empty, raw,
    target, stackPointer, privateFlags, privateRcx, privateR11, memory, peers,
    resumedAd, admitted_step resumedAd runtimeRet⟩

end EDSL.OS.Futex.Clients
