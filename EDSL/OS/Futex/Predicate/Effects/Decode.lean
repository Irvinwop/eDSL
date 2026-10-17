/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Guards

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

abbrev CurrentCode (cohort : Cohort) (state : Suspend.State) : Prop :=
  ∀ (worker : Nat) (kind : Kind), cohort.clients[worker]? = some kind →
    CodeAt state.machine.memory kind.binding.entry.rip kind.binding.bytes

theorem Admitted.currentCode {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : CurrentCode cohort state.suspended :=
  fun worker kind member => (admitted.protected worker kind member).2.2.1

/-- Inverting the actual current decoder excludes both an enqueue and a
locked instruction for the loop. No instruction is selected by this proof. -/
theorem LoopControl.decoded_effects {address : Word} {client : Client} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker} {instruction : Instruction}
    (control : LoopControl address client worker state actual)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (live : actual.returned = false) (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok instruction) :
    TSO.pendingStore actual.context instruction = none ∧ TSO.locked instruction = false := by
  cases control with
  | running point current _ _ _ _ =>
    have expected := decode_point current code
    have same : instruction = point.instruction := Except.ok.inj (decoded.symm.trans expected)
    rw [same]
    exact ⟨Point.no_store point actual.context, Point.unlocked point⟩
  | entered saved pending _ _ _ _ _ => simp [free] at pending
  | returned _ _ _ _ _ done _ _ => simp [live] at done

/-- Successful raw loop issues only retire a non-atomic instruction, capture
a fresh call, or park at an existing call. In all cases the entire RAM is the
current RAM, with no hidden flush, enqueue, atomic write or memory rollback. -/
theorem LoopControl.issue_effects {address : Word} {client : Client} {worker : Nat}
    {state after : Suspend.State} {selected : TSO.Worker} {observation : Suspend.Observation}
    (control : LoopControl address client worker state selected)
    (found : state.machine.workers[worker]? = some selected)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    after.machine.memory = state.machine.memory ∧
      (observation = .machine (.retired worker none) ∨
        observation = .entered worker state.nextCall ∨
          ∃ invocation, observation = .parked worker invocation) := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running pending decoded empty executed stepped user continuation =>
    exact ⟨rfl, .inr (.inl rfl)⟩
  | parked live running pending => exact ⟨rfl, .inr (.inr ⟨_, rfl⟩)⟩
  | @machine machine observed free issued =>
    obtain ⟨current, instruction, currentAt, live, decoded, executed, effect⟩ := TSO.issue_effect _ _ _ issued
    cases Option.some.inj (currentAt.symm.trans found)
    obtain ⟨noStore, unlocked⟩ := control.decoded_effects code live free decoded
    cases effect with
    | queued pending aligned data executed writable output => rw [noStore] at pending; cases pending
    | ordinary pending unlocked loads executed memory => exact ⟨rfl, .inl rfl⟩
    | returned pending unlocked instruction executed memory => exact ⟨rfl, .inl rfl⟩
    | atomic pending classified empty data executed transition address accumulator =>
      rw [unlocked] at classified
      cases classified
    | blocked pending classified nonempty => rw [unlocked] at classified; cases classified

/-- Exact STORE inversion retains both the actual legacy member identity and
its prescribed address/value. It does not use a whole old-cohort control. -/
theorem producer_store {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction} {store : StoreBuffer.Store}
    (found : state.machine.workers[worker]? = some actual) (live : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok instruction)
    (intent : TSO.pendingStore actual.context instruction = some store) :
    ∃ client : Clients.Client, cohort.clients[worker]? = some (.legacy client) ∧
      Clients.PayloadRole client.role ∧ store = client.store := by
  obtain ⟨kind, member, controlled⟩ := control worker actual found
  have currentCode := code worker kind member
  cases kind with
  | waitLoop client =>
    have absent := (LoopControl.decoded_effects controlled currentCode live free decoded).1
    rw [absent] at intent
    cases intent
  | legacy client =>
    cases controlled with
    | running stage supported context _ _ _ =>
      have expected := Clients.decode_stage client stage state.machine.memory supported currentCode
      have instructionEq : instruction = stage.instruction client.role := by
        rw [TSO.sharedState, context] at decoded
        exact Except.ok.inj (decoded.symm.trans expected)
      rw [context, instructionEq] at intent
      obtain ⟨producer, same⟩ := Clients.stage_store supported intent
      exact ⟨client, member, producer, same⟩
    | entered saved pending _ _ _ _ _ _ => simp [free] at pending
    | resumed outcome flags rcx r11 caller context _ _ _ _ =>
      have expected := Clients.decode_resumed client state.machine.memory
        outcome.raw flags rcx r11 caller currentCode
      rw [TSO.sharedState, context] at decoded
      have same := Except.ok.inj (decoded.symm.trans expected)
      simp [same, TSO.pendingStore] at intent
    | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [live] at done

/-- A real decoded STORE carries the exact profile destination. The returned
peer's later FIFO is covered by current FIFO authority. -/
theorem store_intent_address {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state) (static : Static cohort)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction} {store : StoreBuffer.Store}
    (found : state.machine.workers[worker]? = some actual) (live : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok instruction)
    (intent : TSO.pendingStore actual.context instruction = some store) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = store.address := by
  obtain ⟨client, member, producer, same⟩ := producer_store control code found live free decoded intent
  obtain ⟨_, _, _, _, descriptor⟩ := (static.descriptors worker (.legacy client) member).1
  rw [same]
  rcases producer with publisher | peer
  · rw [publisher] at descriptor
    exact descriptor.1
  · rw [peer] at descriptor
    exact descriptor.1

theorem store_intent_authorized {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction} {store : StoreBuffer.Store}
    (found : state.suspended.machine.workers[worker]? = some actual) (live : actual.returned = false)
    (free : state.suspended.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.suspended.machine actual) = .ok instruction)
    (intent : TSO.pendingStore actual.context instruction = some store) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = store.address ∧
      grant.Valid state.authority := by
  obtain ⟨grant, atGrant, address⟩ := store_intent_address admitted.control admitted.currentCode
    admitted.static found live free decoded intent
  exact ⟨grant, atGrant, address, admitted.payload worker grant atGrant⟩

/-- Every actual current locked instruction is the same member's legacy
publisher XCHG of one at W, established from its real code and local stage. -/
theorem producer_exchange {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) (code : CurrentCode cohort state) (static : Static cohort)
    {worker : Nat} {actual : TSO.Worker} {instruction : Instruction}
    (found : state.machine.workers[worker]? = some actual) (live : actual.returned = false)
    (free : state.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok instruction)
    (locked : TSO.locked instruction = true) :
    ∃ client : Clients.Client, cohort.clients[worker]? = some (.legacy client) ∧
      client.role = .publishPayloadWake ∧ actual.context.registers .rdi = cohort.registration.address ∧
      actual.context.registers .rax = 1 ∧ instruction = .exchangeEaxRdi := by
  obtain ⟨kind, member, controlled⟩ := control worker actual found
  have currentCode := code worker kind member
  cases kind with
  | waitLoop client =>
    have unlocked := (LoopControl.decoded_effects controlled currentCode live free decoded).2
    rw [unlocked] at locked
    cases locked
  | legacy client =>
    cases controlled with
    | running stage supported context _ _ _ =>
      have expected := Clients.decode_stage client stage state.machine.memory supported currentCode
      rw [TSO.sharedState, context] at decoded
      have same := Except.ok.inj (decoded.symm.trans expected)
      rw [same] at locked
      obtain ⟨publisher, _, address, accumulator, instructionEq⟩ := Clients.stage_locked supported locked
      exact ⟨client, member, publisher,
        by rw [context, address]; exact (static.descriptors worker (.legacy client) member).1.1,
        by rw [context]; exact accumulator, same.trans instructionEq⟩
    | entered saved pending _ _ _ _ _ _ => simp [free] at pending
    | resumed outcome flags rcx r11 caller context _ _ _ _ =>
      have expected := Clients.decode_resumed client state.machine.memory
        outcome.raw flags rcx r11 caller currentCode
      rw [TSO.sharedState, context] at decoded
      have same := Except.ok.inj (decoded.symm.trans expected)
      simp [same, TSO.locked] at locked
    | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [live] at done

/-- Ready contains present authorization only. Synchronization and fresh
call capture are consequences supplied by the generic lift theorem. -/
theorem issue_ready {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    Physical.Ready cohort.profile state.authority observation := by
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
      obtain ⟨client, member, publisher, operand, _, _⟩ :=
        producer_exchange admitted.control admitted.currentCode admitted.static
          live running free decoded classified
      have descriptor := (admitted.static.descriptors worker (.legacy client) member).1.2.2.2.2
      rw [publisher] at descriptor
      obtain ⟨_, access, handle, atAccess, fixed, actor, target, _, _⟩ := descriptor
      refine ⟨access, handle, atAccess, ?_, target.trans (operand.symm.trans address.symm)⟩
      simp [Atomics.authorize, admitted.fixed _ _ fixed, actor]

/-- Exact managed replay of the successful raw issue, with actual output and
observation unchanged. No managed success or post-control is a premise. -/
theorem issue_enabled {cohort : Cohort} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.issue cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Runtime.Invariant cohort.profile after ∧
      Atomics.History state.authority after.authority :=
  Clients.LiftCore.issue_enabled admitted.runtime (entry_support admitted) (issue_ready admitted actual) actual

end EDSL.OS.Futex.Predicate

#audit_edsl
