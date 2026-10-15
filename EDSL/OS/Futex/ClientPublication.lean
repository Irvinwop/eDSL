/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientAdmission
import EDSL.OS.Futex.ClientControl
import EDSL.OS.Futex.ClientFIFO
import EDSL.X86.MemoryTransport

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

private theorem publication_refl (cohort : Cohort) (memory : Memory) : PublicationFrame cohort memory memory :=
  fun _ _ _ published => published

private theorem publisher_grant {cohort : Cohort} (static : Static cohort)
    {worker : Nat} {client : Client} (atClient : cohort.clients[worker]? = some client)
    (publisher : client.role = .publishPayloadWake) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = client.store.address := by
  have descriptor := (static.descriptors worker client atClient).2.2.2.2
  rw [publisher] at descriptor
  exact descriptor.1

/-- Actual retired atomic instructions target W, so their complete RAM write
cannot overwrite any separately granted publisher payload. -/
theorem issue_publication {cohort : Cohort} {state : State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation} (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    PublicationFrame cohort state.suspended.machine.memory after.machine.memory := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running pending decoded empty executed stepped user continuation => exact publication_refl _ _
  | parked live running pending => exact publication_refl _ _
  | @machine machine observed free issued =>
    obtain ⟨selected, instruction, live, running, decoded, executed, effect⟩ := TSO.issue_effect _ _ _ issued
    cases effect with
    | queued pending aligned data executed writable output => exact publication_refl _ _
    | ordinary pending unlocked loads executed memory => exact publication_refl _ _
    | returned pending unlocked instruction executed memory => exact publication_refl _ _
    | blocked pending classified nonempty => exact publication_refl _ _
    | @atomic event output pending classified empty data executed transition address accumulator =>
      obtain ⟨client, atClient, publisher, operand, replacement, instructionEq⟩ :=
        producer_exchange admitted.control
          (fun i c member => (admitted.protected i c member).2.2.1)
          admitted.static.descriptors live running free decoded classified
      have atWord : event.address = cohort.registration.address := address.trans operand
      intro query publishing atPublishing published kind
      obtain ⟨grant, atGrant, grantAddress⟩ := publisher_grant admitted.static atPublishing kind
      have separate := (admitted.payload query grant atGrant).separate_keeper_word
        admitted.runtime.service.authority admitted.keeper
      have disjoint : DWordDisjoint event.address publishing.store.address 4 := by
        rw [atWord, ← grantAddress]
        exact (StoreBuffer.separate_symm separate).disjoint
      change loadDWord output.memory publishing.store.address = .ok publishing.store.value
      rw [transition.2.2.2]
      exact (loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ disjoint)).trans (published kind)

/-- A FIFO drain either publishes this client's own prescribed payload value,
or updates a disjoint grant. Returned producers remain covered. -/
theorem drain_publication {cohort : Cohort} {state : State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation} (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    PublicationFrame cohort state.suspended.machine.memory after.machine.memory := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, live, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have afterEq := congrArg Prod.fst same
  have machineEq := congrArg Prod.fst installed
  dsimp only at afterEq machineEq
  rw [afterEq, machineEq]
  have queued : head ∈ selected.buffer := by rw [buffer]; simp
  have allowed := (admitted.runtime.service.suspended.buffers selected (List.mem_of_getElem? live) head queued).2.1
  have memoryEq : memory = writeDWordUnchecked state.suspended.machine.memory head.address head.value :=
    Except.ok.inj (committed.symm.trans (store_sound _ _ _ allowed).1)
  intro query publishing atPublishing published kind
  change loadDWord memory publishing.store.address = .ok publishing.store.value
  rw [memoryEq]
  by_cases own : query = worker
  · subst query
    obtain ⟨client, atClient, controlled⟩ := admitted.control worker selected live
    have sameClient := Option.some.inj (atClient.symm.trans atPublishing)
    subst client
    have exactStore := (controlled.queued_store queued).2
    rw [exactStore]
    exact load_after_write _ _ _ ((Bool.and_eq_true_iff.mp (exactStore ▸ allowed)).1)
  · obtain ⟨source, atSource, sourceAddress, sourceReady⟩ := admitted.fifo worker selected live head queued
    obtain ⟨grant, atGrant, grantAddress⟩ := publisher_grant admitted.static atPublishing kind
    have separate := admitted.static.payloadSeparate worker source query grant (Ne.symm own) atSource atGrant
    have disjoint : DWordDisjoint head.address publishing.store.address 4 := by
      rw [← sourceAddress, ← grantAddress]
      exact separate.disjoint
    exact (loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ disjoint)).trans (published kind)

/-- Bookkeeping and actual current-RAM resumption leave published payloads
unchanged; they do not supply a publication or acquisition effect. -/
theorem service_publication {cohort : Cohort} {state after : State} {action : Futex.Action}
    (actual : Futex.step cohort.profile.service state action = .ok after) :
    PublicationFrame cohort state.suspended.machine.memory after.suspended.machine.memory := by
  rw [service_memory actual]
  exact publication_refl _ _

theorem runtime_publication {cohort : Cohort} {state : State}
    {action : Runtime.Action} {result : State × Runtime.Observation}
    (admitted : Admitted cohort state) (success : Runtime.step cohort.profile state action = .ok result) :
    PublicationFrame cohort state.suspended.machine.memory result.1.suspended.machine.memory := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at success
    | ok actual =>
      simp [Runtime.step, issued] at success
      subst result
      exact issue_publication admitted (Physical.issue_projection _ _ _ _ issued)
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at success
    | ok actual =>
      simp [Runtime.step, drained] at success
      subst result
      exact drain_publication admitted (Physical.drain_projection _ _ _ _ drained)
  | service action =>
    cases serviced : Futex.step cohort.profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at success
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at success
      subst result
      exact service_publication serviced

end EDSL.OS.Futex.Clients
