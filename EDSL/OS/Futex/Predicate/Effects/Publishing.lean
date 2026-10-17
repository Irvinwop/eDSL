/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Effects.Frames

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

/-- Actual XCHG retirement belongs to this legacy member, and its own FIFO
has already drained the prescribed payload. Neither a past program counter
nor a promised successful service suffix supplies publication. -/
theorem publisher_exchange_publishes_payload {cohort : Cohort} {state : Futex.State}
    {worker : Nat} {after : Suspend.State} {event : AtomicEvent}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, .machine (.retired worker (some event)))) :
    ∃ client : Clients.Client, cohort.clients[worker]? = some (.legacy client) ∧
      client.role = .publishPayloadWake ∧
      event.address = cohort.registration.address ∧ event.after = 1 ∧
      loadDWord state.suspended.machine.memory client.store.address = .ok client.store.value ∧
      loadDWord after.machine.memory client.store.address = .ok client.store.value ∧
      loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
  obtain ⟨free, issued, _, _⟩ := Suspend.issue_machine_effect actual
  obtain ⟨selected, instruction, output, found, live, decoded, locked, empty,
    data, architectural, installed, transition, address, accumulator⟩ := TSO.issue_atomic_effect issued
  obtain ⟨client, member, publisher, operand, _, _⟩ := producer_exchange admitted.control
    admitted.currentCode admitted.static found live free decoded locked
  obtain ⟨kind, selectedMember, controlled⟩ := admitted.control worker selected found
  have sameKind := Option.some.inj (selectedMember.symm.trans member)
  subst kind
  have code := admitted.currentCode worker (.legacy client) member
  cases controlled with
  | running stage supported context _ _ fifo =>
    have expected := Clients.decode_stage client stage state.suspended.machine.memory supported code
    have instructionEq : instruction = stage.instruction client.role := by
      rw [TSO.sharedState, context] at decoded
      exact Except.ok.inj (decoded.symm.trans expected)
    have classified : TSO.locked (stage.instruction client.role) = true := by
      rw [← instructionEq]
      exact locked
    obtain ⟨_, atExchange, _, _, exactInstruction⟩ := Clients.stage_locked supported classified
    subst stage
    have published : client.Published state.suspended.machine.memory := by
      simp only [Clients.Stage.FIFO, Clients.Stage.bufferCondition, publisher] at fifo
      rcases fifo with token | visible
      · simp [empty] at token
      · exact visible.2
    have exchanged : event.after = 1 :=
      (Clients.exchange_context publisher
        (by simpa only [TSO.sharedState, context, instructionEq, exactInstruction] using architectural)).2
    have word : event.address = cohort.registration.address := address.trans operand
    have afterPublished := issue_publication admitted actual worker (.legacy client) member published
    have wordRead : loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
      simpa only [word, exchanged] using transition.readback
    exact ⟨client, member, publisher, word, exchanged, published publisher, afterPublished publisher, wordRead⟩
  | entered saved pending _ _ _ _ _ _ => simp [free] at pending
  | resumed outcome flags rcx r11 caller context _ _ _ _ =>
    have expected := Clients.decode_resumed client state.suspended.machine.memory
      outcome.raw flags rcx r11 caller code
    rw [TSO.sharedState, context] at decoded
    have same := Except.ok.inj (decoded.symm.trans expected)
    simp [same, TSO.locked] at locked
  | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [live] at done

/-- The checked adapter projects to that identical raw retirement and keeps
the same publisher identity, payload, registered address and written value. -/
theorem physical_publisher_exchange_publishes_payload {cohort : Cohort} {state after : Futex.State}
    {worker : Nat} {event : AtomicEvent} (admitted : Admitted cohort state)
    (actual : Physical.issue cohort.profile state worker =
      .ok (after, .machine (.retired worker (some event)))) :
    ∃ client : Clients.Client, cohort.clients[worker]? = some (.legacy client) ∧
      client.role = .publishPayloadWake ∧
      event.address = cohort.registration.address ∧ event.after = 1 ∧
      loadDWord state.suspended.machine.memory client.store.address = .ok client.store.value ∧
      loadDWord after.suspended.machine.memory client.store.address = .ok client.store.value ∧
      loadDWord after.suspended.machine.memory cohort.registration.address = .ok 1 :=
  publisher_exchange_publishes_payload admitted (Physical.issue_projection _ _ _ _ actual)

end EDSL.OS.Futex.Predicate

#audit_edsl
