/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientPublication
import EDSL.OS.Futex.ClientControlStages

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

/-- Actual XCHG retirement establishes same-worker payload publication. Its
own FIFO really is empty; decoding and the concrete stage establish that the
prescribed store preceded it. No syscall flush or peer quiescence is assumed. -/
theorem publisher_exchange_publishes_payload {cohort : Cohort} {state : State}
    {worker : Nat} {after : Suspend.State} {event : AtomicEvent}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, .machine (.retired worker (some event)))) :
    ∃ client, cohort.clients[worker]? = some client ∧ client.role = .publishPayloadWake ∧
      event.address = cohort.registration.address ∧ event.after = 1 ∧
      loadDWord state.suspended.machine.memory client.store.address = .ok client.store.value ∧
      loadDWord after.machine.memory client.store.address = .ok client.store.value ∧
      loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
  obtain ⟨free, issued, _, _⟩ := Suspend.issue_machine_effect actual
  obtain ⟨selected, instruction, output, live, running, decoded, locked, empty,
    data, architectural, installed, transition, address, accumulator⟩ := TSO.issue_atomic_effect issued
  obtain ⟨client, atClient, controlled⟩ := admitted.control worker selected live
  have code := (admitted.protected worker client atClient).2.2.1
  cases controlled with
  | running stage supported context _ _ fifo =>
    have expected := decode_stage client stage state.suspended.machine.memory supported code
    have instructionEq : instruction = stage.instruction client.role := by
      rw [TSO.sharedState, context] at decoded
      exact Except.ok.inj (decoded.symm.trans expected)
    have classified : TSO.locked (stage.instruction client.role) = true := by rw [← instructionEq]; exact locked
    obtain ⟨publisher, atExchange, _, _, exactInstruction⟩ := stage_locked supported classified
    subst stage
    have published : client.Published state.suspended.machine.memory := by
      simp only [Stage.FIFO, Stage.bufferCondition, publisher] at fifo
      rcases fifo with token | visible
      · simp [empty] at token
      · exact visible.2
    have exchanged : event.after = 1 :=
      (exchange_context publisher (by simpa [TSO.sharedState, context, instructionEq, exactInstruction] using architectural)).2
    have word : event.address = cohort.registration.address := by
      rw [address, context]
      simpa [Stage.context] using (admitted.static.descriptors worker client atClient).1
    have afterPublished := issue_publication admitted actual worker client atClient published publisher
    have wordRead : loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
      rw [← word, transition.2.2.2, exchanged]
      exact load_after_write _ _ _ ((Bool.and_eq_true_iff.mp transition.1).1)
    exact ⟨client, atClient, publisher, word, exchanged, published publisher, afterPublished, wordRead⟩
  | entered saved pending owner family context live empty published => simp [free] at pending
  | resumed outcome flags rcx r11 caller context _ _ _ _ =>
    have expected := decode_resumed client state.suspended.machine.memory outcome.raw flags rcx r11 caller code
    rw [TSO.sharedState, context] at decoded
    have same := Except.ok.inj (decoded.symm.trans expected)
    simp [same, TSO.locked] at locked
  | returned _ _ _ _ _ _ done _ _ _ | peerReturned _ _ done _ _ => simp [running] at done

/-- A later actual drain, including a previously buffered write owned by a
returned producer, cannot reset W. Its current grant and live keeper establish
separation of the complete four-byte footprints. -/
theorem drain_preserves_word {cohort : Cohort} {state : State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation} (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address =
      loadDWord state.suspended.machine.memory cohort.registration.address := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, live, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have queued : head ∈ selected.buffer := by rw [buffer]; simp
  obtain ⟨grant, _, grantAddress, ready⟩ := admitted.fifo worker selected live head queued
  have separate : DWordDisjoint head.address cohort.registration.address 4 := by
    rw [← grantAddress]
    exact ready.disjoint_keeper_word admitted.runtime.service.authority admitted.keeper
  have memoryEq : memory = writeDWordUnchecked state.suspended.machine.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact Except.ok.inj committed.symm
    · cases committed
  have afterEq := congrArg Prod.fst same
  have machineEq := congrArg Prod.fst installed
  dsimp only at afterEq machineEq
  rw [afterEq, machineEq]
  change loadDWord memory _ = _
  rw [memoryEq]
  exact loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ separate)

/-- Every actual issue either leaves W's RAM unchanged or performs one of the
supported writes of one. The absence of reset writes is derived from code. -/
theorem issue_preserves_published_word {cohort : Cohort} {state : State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation} (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running pending decoded empty executed stepped user continuation => exact published
  | parked live running pending => exact published
  | @machine machine observed free issued =>
    obtain ⟨selected, instruction, live, running, decoded, executed, effect⟩ := TSO.issue_effect _ _ _ issued
    cases effect with
    | queued pending aligned data executed writable output => exact published
    | ordinary pending unlocked loads executed memory => exact published
    | returned pending unlocked instruction executed memory => exact published
    | blocked pending classified nonempty => exact published
    | atomic pending classified empty data executed transition address accumulator =>
      obtain ⟨_, _, _, _, _, _, _, word⟩ := publisher_exchange_publishes_payload admitted actual
      exact word

end EDSL.OS.Futex.Clients
