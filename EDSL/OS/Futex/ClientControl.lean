/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientControlProgress

set_option linter.unusedSimpArgs false

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

abbrev CurrentCode (cohort : Cohort) (state : Suspend.State) : Prop :=
  ∀ (worker : Nat) (client : Client), cohort.clients[worker]? = some client →
    CodeAt state.machine.memory client.entry.rip client.role.bytes

theorem current_syscall_family {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    {worker : Nat} {actual : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some actual) (running : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok .syscall) :
    CallFamily cohort worker ⟨TSO.sharedState state.machine actual, actual.context.rip + 2⟩ := by
  obtain ⟨client, atClient, controlled⟩ := control worker actual atWorker
  refine ⟨client, atClient, ?_⟩
  cases controlled with
  | running stage supported context _ _ _ =>
    have expected := decode_stage client stage state.machine.memory supported (code _ _ atClient)
    rw [TSO.sharedState, context] at decoded
    have same := Except.ok.inj (expected.symm.trans decoded)
    obtain ⟨caller, callContext⟩ := stage_syscall supported same
    refine ⟨caller, ?_⟩
    simp only [Client.request, TSO.sharedState, context, callContext, MachineThreads.contextState]
  | entered saved pending _ _ _ _ _ _ => simp [free] at pending
  | resumed outcome flags rcx r11 caller context _ _ _ _ =>
    have expected := decode_resumed client state.machine.memory outcome.raw flags rcx r11 caller (code _ _ atClient)
    rw [TSO.sharedState, context] at decoded
    cases expected.symm.trans decoded
  | returned _ _ _ _ _ _ done _ _ _ => simp [running] at done
  | peerReturned _ _ done _ _ => simp [running] at done

theorem current_syscall_abi {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    {worker : Nat} {actual : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some actual) (running : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok .syscall) :
    ∃ operation, classify ⟨TSO.sharedState state.machine actual, actual.context.rip + 2⟩ = .ok operation ∧
      actual.context.registers .rdi = cohort.registration.address := by
  obtain ⟨client, atClient, family⟩ := current_syscall_family control code atWorker running free decoded
  exact ⟨client.operation, family_classifies (descriptors _ _ atClient) family⟩

/-- Authorization at enqueue is derived from actual decoding, even though an
ordinary STORE's retirement has no atomic event in Physical.Ready. -/
theorem store_intent_address {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction} {store : StoreBuffer.Store}
    (atWorker : state.machine.workers[worker]? = some actual) (running : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok instruction)
    (intent : TSO.pendingStore actual.context instruction = some store) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = store.address := by
  obtain ⟨client, atClient, controlled⟩ := control worker actual atWorker
  cases controlled with
  | running stage supported context _ _ _ =>
    have expected := decode_stage client stage state.machine.memory supported (code _ _ atClient)
    have instructionEq : instruction = stage.instruction client.role := by
      rw [TSO.sharedState, context] at decoded
      exact Except.ok.inj (decoded.symm.trans expected)
    rw [context, instructionEq] at intent
    obtain ⟨producer, same⟩ := stage_store supported intent
    obtain ⟨_, _, _, _, descriptor⟩ := descriptors _ _ atClient
    rw [same]
    rcases producer with publisher | peer
    · rw [publisher] at descriptor
      exact descriptor.1
    · rw [peer] at descriptor
      exact descriptor.1
  | entered saved pending _ _ _ _ _ _ => simp [free] at pending
  | resumed outcome flags rcx r11 caller context _ _ _ _ =>
    have expected := decode_resumed client state.machine.memory outcome.raw flags rcx r11 caller (code _ _ atClient)
    rw [TSO.sharedState, context] at decoded
    have same := Except.ok.inj (decoded.symm.trans expected)
    simp [same, TSO.pendingStore] at intent
  | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [running] at done

theorem store_intent_authorized {cohort : Cohort} {state : Futex.State}
    (control : Control cohort state.suspended) (code : CurrentCode cohort state.suspended)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    (payload : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid state.authority)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction} {store : StoreBuffer.Store}
    (atWorker : state.suspended.machine.workers[worker]? = some actual) (running : actual.returned = false)
    (free : state.suspended.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.suspended.machine actual) = .ok instruction)
    (intent : TSO.pendingStore actual.context instruction = some store) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = store.address ∧ grant.Valid state.authority := by
  obtain ⟨grant, atGrant, address⟩ := store_intent_address control code descriptors atWorker running free decoded intent
  exact ⟨grant, atGrant, address, payload _ _ atGrant⟩

/-- Every admitted locked instruction is the publisher's actual XCHG of one
at the registered word. There is no expected-opcode gate in execution. -/
theorem producer_exchange {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction}
    (atWorker : state.machine.workers[worker]? = some actual) (running : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok instruction)
    (locked : TSO.locked instruction = true) :
    ∃ client, cohort.clients[worker]? = some client ∧ client.role = .publishPayloadWake ∧
      actual.context.registers .rdi = cohort.registration.address ∧
      actual.context.registers .rax = 1 ∧ instruction = .exchangeEaxRdi := by
  obtain ⟨client, atClient, controlled⟩ := control worker actual atWorker
  cases controlled with
  | running stage supported context _ _ _ =>
    have expected := decode_stage client stage state.machine.memory supported (code _ _ atClient)
    rw [TSO.sharedState, context] at decoded
    have same := Except.ok.inj (decoded.symm.trans expected)
    rw [same] at locked
    obtain ⟨publisher, _, address, accumulator, instructionEq⟩ := stage_locked supported locked
    exact ⟨client, atClient, publisher, by rw [context, address]; exact (descriptors _ _ atClient).1,
      by rw [context]; exact accumulator, same.trans instructionEq⟩
  | entered saved pending _ _ _ _ _ _ => simp [free] at pending
  | resumed outcome flags rcx r11 caller context _ _ _ _ =>
    have expected := decode_resumed client state.machine.memory outcome.raw flags rcx r11 caller (code _ _ atClient)
    rw [TSO.sharedState, context] at decoded
    have same := Except.ok.inj (decoded.symm.trans expected)
    simp [same, TSO.locked] at locked
  | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [running] at done

/-- Actual XCHG retirement requires the publisher's own payload token to have
drained. The payload is current at retirement and survives the disjoint atomic
effect. This conclusion is not inferred from a past program counter alone. -/
theorem control_exchange_publishes_payload {cohort : Cohort} {state after : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    (frame : PublicationFrame cohort state.machine.memory after.machine.memory)
    {worker : Nat} {event : AtomicEvent}
    (actual : Suspend.issue state worker = .ok (after, .machine (.retired worker (some event)))) :
    ∃ client, cohort.clients[worker]? = some client ∧ client.role = .publishPayloadWake ∧
      event.address = cohort.registration.address ∧ event.after = 1 ∧
      loadDWord state.machine.memory client.store.address = .ok 0x11223344 ∧
      loadDWord after.machine.memory client.store.address = .ok 0x11223344 := by
  cases Suspend.issue_effect _ _ _ actual with
  | @machine machine observation free issued =>
    obtain ⟨selected, instruction, output, atWorker, running, decoded, locked, empty,
      _, executed, _, _, address, _⟩ := TSO.issue_atomic_effect issued
    obtain ⟨client, atClient, controlled⟩ := control worker selected atWorker
    cases controlled with
    | running stage supported context _ _ fifo =>
      have expected : decodeAt (TSO.sharedState state.machine selected) = .ok (stage.instruction client.role) := by
        rw [TSO.sharedState, context]
        exact decode_stage _ _ _ supported (code _ _ atClient)
      have instructionEq := Except.ok.inj (decoded.symm.trans expected)
      rw [instructionEq] at locked executed
      obtain ⟨publisher, phase, _, _, isExchange⟩ := stage_locked supported locked
      subst stage
      have update := exchange_context publisher (by simpa only [TSO.sharedState, context, isExchange] using executed)
      have publication : client.Published state.machine.memory := by
        simp only [Stage.FIFO, Stage.bufferCondition, publisher] at fifo
        rcases fifo with token | visible
        · simp [empty] at token
        · exact visible.2
      have operand : selected.context.registers .rdi = cohort.registration.address := by
        rw [context]
        simpa [Stage.context] using (descriptors _ _ atClient).1
      refine ⟨client, atClient, publisher, address.trans operand, update.2, ?_, ?_⟩
      · simpa only [Client.store, publisher, Role.value] using publication publisher
      · simpa only [Client.store, publisher, Role.value] using (frame _ _ atClient publication) publisher
    | entered saved pending _ _ _ _ _ _ => simp [free] at pending
    | resumed outcome flags rcx r11 caller context _ _ _ _ =>
      have expected := decode_resumed client state.machine.memory outcome.raw flags rcx r11 caller (code _ _ atClient)
      rw [TSO.sharedState, context] at decoded
      have instructionEq := Except.ok.inj (decoded.symm.trans expected)
      simp [instructionEq, TSO.locked] at locked
    | returned _ _ _ _ _ _ done _ _ _ => simp [running] at done
    | peerReturned _ _ done _ _ => simp [running] at done

theorem entered_family {cohort : Cohort} {state after : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    {worker invocation : Nat}
    (actual : Suspend.issue state worker = .ok (after, .entered worker invocation)) :
    ∃ saved, after.pending worker = some saved ∧ saved.identifier = invocation ∧
      CallFamily cohort worker saved.request := by
  cases Suspend.issue_effect _ _ _ actual with
  | @entered selected request atWorker running free decoded _ _ _ user continuation =>
    obtain ⟨client, atClient, controlled⟩ := control worker selected atWorker
    have family : client.Family request := by
      cases controlled with
      | running stage supported context _ _ _ =>
        have expected := decode_stage client stage state.machine.memory supported (code _ _ atClient)
        rw [TSO.sharedState, context] at decoded
        have same := Except.ok.inj (expected.symm.trans decoded)
        obtain ⟨caller, callContext⟩ := stage_syscall supported same
        refine ⟨caller, ?_⟩
        rw [Suspend.request_eq_entry user continuation]
        have memory : request.user.memory = state.machine.memory := congrArg X86.State.memory user
        simp only [Client.request, TSO.sharedState, context, callContext, memory, MachineThreads.contextState]
      | entered saved pending _ _ _ _ _ _ => simp [free] at pending
      | resumed outcome flags rcx r11 caller context _ _ _ _ =>
        have expected := decode_resumed client state.machine.memory outcome.raw flags rcx r11 caller (code _ _ atClient)
        rw [TSO.sharedState, context] at decoded
        cases expected.symm.trans decoded
      | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [running] at done
    exact ⟨⟨state.nextCall, worker, request⟩, by simp [Suspend.capture], rfl, client, atClient, family⟩

/-- The actual forwarded RET stack follows from current ownership and FIFO
rights. No condition mentions the returned flag or emptiness of peer FIFOs. -/
theorem stack_views {cohort : Cohort} {state : Futex.State}
    (valid : Atomics.WellFormed state.authority) (protection : Protected cohort state)
    (fifo : FIFOAuthorized cohort state) : StackViews cohort state.suspended := by
  intro worker actual client atWorker atClient
  have protectedClient := protection worker client atClient
  rw [StoreBuffer.view_readWord_frame]
  · exact protectedClient.2.2.2.1
  · intro store member
    obtain ⟨grant, _, address, ready⟩ := fifo worker actual atWorker store member
    rw [← address]
    exact ready.disjoint_hasLoan valid protectedClient.2.1

theorem issue_pending_peer {state after : Suspend.State} {worker query : Nat}
    {observation : Suspend.Observation} (different : worker ≠ query)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    after.pending query = state.pending query := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered => simp [Suspend.capture, Ne.symm different]
  | parked => rfl
  | machine => rfl

theorem issue_control {cohort : Cohort} {state after : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    (stacks : StackViews cohort state)
    (targets : ∀ (worker : Nat) (client : Client), cohort.clients[worker]? = some client → canonical client.returnTarget = true)
    (frame : PublicationFrame cohort state.machine.memory after.machine.memory)
    {worker : Nat} {observation : Suspend.Observation}
    (actual : Suspend.issue state worker = .ok (after, observation)) : Control cohort after := by
  cases atWorker : state.machine.workers[worker]? with
  | none => simp [Suspend.issue, atWorker] at actual
  | some before =>
    obtain ⟨client, atClient, controlled⟩ := control worker before atWorker
    obtain ⟨selected, selectedAt, selectedControl⟩ := controlled.issue_selected atWorker
      (code _ _ atClient) (stacks _ _ _ atWorker atClient) (targets _ _ atClient)
      (frame _ _ atClient) actual
    intro query current atAfter
    by_cases own : worker = query
    · subst query
      cases Option.some.inj (selectedAt.symm.trans atAfter)
      exact ⟨client, atClient, selectedControl⟩
    · have peer := Suspend.issue_peer own actual
      have atBefore := peer.symm.trans atAfter
      obtain ⟨other, otherAt, otherControl⟩ := control query current atBefore
      exact ⟨other, otherAt, otherControl.frame (issue_pending_peer own actual) (frame _ _ otherAt)⟩

theorem drain_control {cohort : Cohort} {state after : Suspend.State}
    (control : Control cohort state)
    (frame : PublicationFrame cohort state.machine.memory after.machine.memory)
    {worker : Nat} {observation : Suspend.Observation}
    (actual : Suspend.drain state worker = .ok (after, observation)) : Control cohort after := by
  obtain ⟨_, _, drained, _⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨before, _, _, _, atWorker, _⟩ := TSO.drain_ok _ _ _ drained
  obtain ⟨client, atClient, controlled⟩ := control worker before atWorker
  obtain ⟨selected, selectedAt, selectedControl⟩ := controlled.drain_selected atWorker actual
  intro query current atAfter
  by_cases own : worker = query
  · subst query
    cases Option.some.inj (selectedAt.symm.trans atAfter)
    exact ⟨client, atClient, selectedControl⟩
  · have peer := Suspend.drain_peer own actual
    have atBefore := peer.symm.trans atAfter
    obtain ⟨other, otherAt, otherControl⟩ := control query current atBefore
    exact ⟨other, otherAt, otherControl.frame (by rw [Suspend.drain_pending actual]) (frame _ _ otherAt)⟩

/-- Resume installs only an operation-typed full raw result. Its flags and
SYSCALL clobbers are arbitrary, and every peer record/FIFO remains represented. -/
theorem resume_control {cohort : Cohort} {state after : Suspend.State} {operation : Op}
    (control : Control cohort state)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    (outcome : Outcome operation) {worker invocation : Nat} {flags rcx r11 : Word}
    (classified : ∀ saved, state.pending worker = some saved → classify saved.request = .ok operation)
    (actual : Suspend.resume state worker invocation outcome.raw flags rcx r11 = .ok after) :
    Control cohort after := by
  obtain ⟨before, saved, atWorker, running, pending, identity, owner, empty, same⟩ :=
    Suspend.resume_ok _ _ _ _ _ _ _ _ actual
  obtain ⟨client, atClient, controlled⟩ := control worker before atWorker
  have family : client.Family saved.request := by
    cases controlled with
    | running _ _ _ _ free _ => simp [free] at pending
    | resumed _ _ _ _ _ _ _ free _ _ => simp [free] at pending
    | returned _ _ _ _ _ _ _ free _ _ => simp [free] at pending
    | peerReturned _ _ _ free _ => simp [free] at pending
    | entered captured savedAt _ family _ _ _ _ =>
      cases Option.some.inj (savedAt.symm.trans pending)
      exact family
  have operationEq : client.operation = operation :=
    Except.ok.inj ((family_classifies (descriptors _ _ atClient) family).1.symm.trans (classified saved pending))
  cases operationEq
  have publication : client.Published state.machine.memory := by
    cases controlled with
    | running _ _ _ _ free _ => simp [free] at pending
    | resumed _ _ _ _ _ _ _ free _ _ => simp [free] at pending
    | returned _ _ _ _ _ _ _ free _ _ => simp [free] at pending
    | peerReturned _ _ _ free _ => simp [free] at pending
    | entered _ _ _ _ _ _ _ published => exact published
  have selectedAt : after.machine.workers[worker]? = some
      ⟨client.resumed outcome.raw flags rcx r11, false, []⟩ := by
    rw [same, family_resume family state.machine.memory outcome.raw flags rcx r11]
    exact List.getElem?_set_self (List.getElem_of_getElem? atWorker).1
  intro query current atAfter
  by_cases own : worker = query
  · subst query
    cases Option.some.inj (selectedAt.symm.trans atAfter)
    refine ⟨client, atClient, .resumed outcome flags rcx r11 family.1 rfl rfl
      (Suspend.resume_consumed actual) rfl ?_⟩
    rw [Suspend.resume_memory actual]
    exact publication
  · have peer := Suspend.resume_peer own actual
    obtain ⟨other, otherAt, otherControl⟩ := control query current (peer.symm.trans atAfter)
    refine ⟨other, otherAt, otherControl.frame ?_ ?_⟩
    · simp [Suspend.resume_pending actual, Ne.symm own]
    · rw [Suspend.resume_memory actual]
      exact id

theorem service_control {cohort : Cohort} {state after : Futex.State} {action : Futex.Action}
    (control : Control cohort state.suspended)
    (descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client)
    (valid : Futex.WellFormed cohort.profile.service state)
    (actual : Futex.step cohort.profile.service state action = .ok after) : Control cohort after.suspended := by
  cases action with
  | compare invocation => rw [(compareWait_stutter actual).1]; exact control
  | wake invocation selected => rw [(wakeOne_stutter actual).1]; exact control
  | retry invocation => rw [(retryQueued_stutter actual).1]; exact control
  | spurious invocation => rw [(spuriousReady_stutter actual).1]; exact control
  | idle => cases Except.ok.inj actual; exact control
  | resume invocation flags rcx r11 =>
    obtain ⟨call, outcome, _, _, resumed, _, atCall, _, _, completed, _, same⟩ := resumeReady_effect actual
    have typed : ∀ saved, state.suspended.pending call.worker = some saved →
        classify saved.request = .ok call.op := by
      obtain ⟨captured, atSaved, _, _, classified⟩ := (valid.calls invocation call atCall).saved
      intro saved pending
      cases Option.some.inj (atSaved.symm.trans pending)
      exact classified
    rw [same]
    exact resume_control control descriptors outcome typed completed

end EDSL.OS.Futex.Clients

#audit_edsl
