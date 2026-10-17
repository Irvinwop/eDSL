/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Effects.Decode
import EDSL.X86.MemoryTransport

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

/-- The physical RAM effect retains every legacy payload already current.
The loop has no payload publication obligation of its own. -/
def PublicationFrame (cohort : Cohort) (before after : Memory) : Prop :=
  ∀ (worker : Nat) (kind : Kind), cohort.clients[worker]? = some kind →
    kind.Published before → kind.Published after

/-- The stronger read frame covers both actual legacy roles, including the
payload of a peer which has returned while retaining an ordinary FIFO entry. -/
def PayloadFrame (cohort : Cohort) (before after : Memory) : Prop :=
  ∀ (worker : Nat) (client : Clients.Client), cohort.clients[worker]? = some (.legacy client) →
    loadDWord before client.store.address = .ok client.store.value →
      loadDWord after client.store.address = .ok client.store.value

theorem PayloadFrame.refl (cohort : Cohort) (memory : Memory) : PayloadFrame cohort memory memory :=
  fun _ _ _ published => published

theorem PayloadFrame.publication {cohort : Cohort} {before after : Memory}
    (frame : PayloadFrame cohort before after) : PublicationFrame cohort before after := by
  intro worker kind member published
  cases kind with
  | waitLoop client => trivial
  | legacy client => exact fun publisher => frame worker client member (published publisher)

theorem PublicationFrame.refl (cohort : Cohort) (memory : Memory) :
    PublicationFrame cohort memory memory := fun _ _ _ published => published

theorem PublicationFrame.trans {cohort : Cohort} {before middle after : Memory}
    (first : PublicationFrame cohort before middle) (second : PublicationFrame cohort middle after) :
    PublicationFrame cohort before after :=
  fun worker kind member published => second worker kind member (first worker kind member published)

theorem Static.publisher_grant {cohort : Cohort} (static : Static cohort)
    {worker : Nat} {client : Clients.Client}
    (member : cohort.clients[worker]? = some (.legacy client))
    (publisher : client.role = .publishPayloadWake) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = client.store.address := by
  have descriptor := (static.descriptors worker (.legacy client) member).1.2.2.2.2
  rw [publisher] at descriptor
  exact descriptor.1

theorem Static.payload_grant {cohort : Cohort} (static : Static cohort)
    {worker : Nat} {client : Clients.Client}
    (member : cohort.clients[worker]? = some (.legacy client)) :
    ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = client.store.address := by
  obtain ⟨descriptor, role⟩ := static.descriptors worker (.legacy client) member
  have payload := descriptor.2.2.2.2
  rcases role with publisher | peer
  · rw [publisher] at payload
    exact payload.1
  · rw [peer] at payload
    exact payload.1

/-- Only the actual publisher's XCHG can write RAM at issue. Its four-byte W
footprint is disjoint from every live payload grant. -/
theorem issue_payload_frame {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    PayloadFrame cohort state.suspended.machine.memory after.machine.memory := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running pending decoded empty executed stepped user continuation => exact .refl _ _
  | parked live running pending => exact .refl _ _
  | @machine machine observed free issued =>
    obtain ⟨selected, instruction, live, running, decoded, _, effect⟩ := TSO.issue_effect _ _ _ issued
    cases effect with
    | queued pending aligned data executed writable output => exact .refl _ _
    | ordinary pending unlocked loads executed memory => exact .refl _ _
    | returned pending unlocked instruction executed memory => exact .refl _ _
    | blocked pending classified nonempty => exact .refl _ _
    | @atomic event output pending classified empty data executed transition address accumulator =>
      obtain ⟨_, _, _, operand, _, _⟩ := producer_exchange admitted.control admitted.currentCode
        admitted.static live running free decoded classified
      have atWord : event.address = cohort.registration.address := address.trans operand
      intro query publishing member published
      obtain ⟨grant, atGrant, grantAddress⟩ := admitted.static.payload_grant member
      have separate := (admitted.payload query grant atGrant).separate_keeper_word
        admitted.runtime.service.authority admitted.keeper
      have disjoint : DWordDisjoint event.address publishing.store.address 4 := by
        rw [atWord, ← grantAddress]
        exact (StoreBuffer.separate_symm separate).disjoint
      change loadDWord output.memory publishing.store.address = .ok publishing.store.value
      rw [transition.2.2.2]
      exact (loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ disjoint)).trans published

theorem issue_publication {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    PublicationFrame cohort state.suspended.machine.memory after.machine.memory :=
  (issue_payload_frame admitted actual).publication

/-- A drain writes its owner's prescribed payload value or a fully separate
payload grant. Actual returned peer FIFO entries are included. -/
theorem drain_payload_frame {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    PayloadFrame cohort state.suspended.machine.memory after.machine.memory := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, found, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have afterEq := congrArg Prod.fst same
  have machineEq := congrArg Prod.fst installed
  dsimp only at afterEq machineEq
  rw [afterEq, machineEq]
  have queued : head ∈ selected.buffer := by rw [buffer]; simp
  have allowed :=
    (admitted.runtime.service.suspended.buffers selected (List.mem_of_getElem? found) head queued).2.1
  have memoryEq : memory = writeDWordUnchecked state.suspended.machine.memory head.address head.value :=
    Except.ok.inj (committed.symm.trans (store_sound _ _ _ allowed).1)
  intro query publishing member published
  change loadDWord memory publishing.store.address = .ok publishing.store.value
  rw [memoryEq]
  by_cases own : query = worker
  · subst query
    obtain ⟨selectedKind, selectedMember, controlled⟩ := admitted.control worker selected found
    have sameKind := Option.some.inj (selectedMember.symm.trans member)
    subst selectedKind
    have exactStore := (Clients.WorkerControl.queued_store controlled queued).2
    rw [exactStore]
    exact load_after_write _ _ _ ((Bool.and_eq_true_iff.mp (exactStore ▸ allowed)).1)
  · obtain ⟨source, atSource, sourceAddress, _⟩ := admitted.fifo worker selected found head queued
    obtain ⟨grant, atGrant, grantAddress⟩ := admitted.static.payload_grant member
    have separate := admitted.static.payloadSeparate worker source query grant (Ne.symm own) atSource atGrant
    have disjoint : DWordDisjoint head.address publishing.store.address 4 := by
      rw [← sourceAddress, ← grantAddress]
      exact separate.disjoint
    exact (loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ disjoint)).trans published

theorem drain_publication {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    PublicationFrame cohort state.suspended.machine.memory after.machine.memory :=
  (drain_payload_frame admitted actual).publication

/-- Service uses current physical RAM and leaves it unchanged, including on
resume. A captured historical request is never substituted for this RAM. -/
theorem service_publication {cohort : Cohort} {state after : Futex.State} {action : Futex.Action}
    (actual : Futex.step cohort.profile.service state action = .ok after) :
    PublicationFrame cohort state.suspended.machine.memory after.suspended.machine.memory := by
  rw [service_memory actual]
  exact .refl _ _

theorem service_payload_frame {cohort : Cohort} {state after : Futex.State} {action : Futex.Action}
    (actual : Futex.step cohort.profile.service state action = .ok after) :
    PayloadFrame cohort state.suspended.machine.memory after.suspended.machine.memory := by
  rw [service_memory actual]
  exact .refl _ _

/-- Every actual issue leaves the W read unchanged or actually writes one.
This is below post-control and does not need a prior word-domain premise. -/
theorem issue_word_effect {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address =
      loadDWord state.suspended.machine.memory cohort.registration.address ∨
    loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running pending decoded empty executed stepped user continuation => exact .inl rfl
  | parked live running pending => exact .inl rfl
  | @machine machine observed free issued =>
    obtain ⟨selected, instruction, live, running, decoded, _, effect⟩ := TSO.issue_effect _ _ _ issued
    cases effect with
    | queued pending aligned data executed writable output => exact .inl rfl
    | ordinary pending unlocked loads executed memory => exact .inl rfl
    | returned pending unlocked instruction executed memory => exact .inl rfl
    | blocked pending classified nonempty => exact .inl rfl
    | @atomic event output pending classified empty data executed transition address accumulator =>
      obtain ⟨_, _, _, operand, replacement, instructionEq⟩ :=
        producer_exchange admitted.control admitted.currentCode admitted.static
          live running free decoded classified
      rw [instructionEq] at executed
      have written : event.after = 1 := by
        have value := (executeInstruction_atomic_sound executed).2.2.1
        apply value.trans
        change (selected.context.registers .rax).setWidth 32 = 1
        rw [replacement]
        rfl
      refine .inr ?_
      change loadDWord output.memory cohort.registration.address = .ok 1
      simpa only [address.trans operand, written] using transition.readback

/-- Current payload authority excludes every actual drain from the complete
registered word, even if its producer has already returned. -/
theorem drain_preserves_word {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address =
      loadDWord state.suspended.machine.memory cohort.registration.address := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, found, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have queued : head ∈ selected.buffer := by rw [buffer]; simp
  obtain ⟨grant, _, grantAddress, ready⟩ := admitted.fifo worker selected found head queued
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

theorem service_preserves_word {cohort : Cohort} {state after : Futex.State} {action : Futex.Action}
    (actual : Futex.step cohort.profile.service state action = .ok after) :
    loadDWord after.suspended.machine.memory cohort.registration.address =
      loadDWord state.suspended.machine.memory cohort.registration.address := by
  rw [service_memory actual]

theorem issue_preserves_published_word {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address = .ok 1 :=
  (issue_word_effect admitted actual).elim (fun same => same.trans published) id

theorem issue_preserves_word_domain {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address = .ok 0 ∨
      loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
  rcases issue_word_effect admitted actual with same | one
  · rw [same]
    exact admitted.word
  · exact .inr one

theorem drain_preserves_word_domain {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    loadDWord after.machine.memory cohort.registration.address = .ok 0 ∨
      loadDWord after.machine.memory cohort.registration.address = .ok 1 := by
  rw [drain_preserves_word admitted actual]
  exact admitted.word

theorem service_preserves_word_domain {cohort : Cohort} {state after : Futex.State}
    {action : Futex.Action} (domain : WordDomain cohort state)
    (actual : Futex.step cohort.profile.service state action = .ok after) : WordDomain cohort after := by
  unfold WordDomain at domain ⊢
  rw [service_memory actual]
  exact domain

/-- Every successful mixed runtime action has the same pre-control payload
frame, obtained through the exact raw issue/drain projections. -/
theorem runtime_payload_frame {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result) :
    PayloadFrame cohort state.suspended.machine.memory result.1.suspended.machine.memory := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      exact issue_payload_frame admitted (Physical.issue_projection _ _ _ _ issued)
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      exact drain_payload_frame admitted (Physical.drain_projection _ _ _ _ drained)
  | service action =>
    cases serviced : Futex.step cohort.profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      exact service_payload_frame serviced

theorem runtime_publication {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result) :
    PublicationFrame cohort state.suspended.machine.memory result.1.suspended.machine.memory :=
  (runtime_payload_frame admitted actual).publication

theorem published_word_step {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (actual : Runtime.step cohort.profile state action = .ok result) :
    loadDWord result.1.suspended.machine.memory cohort.registration.address = .ok 1 := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      exact issue_preserves_published_word admitted published (Physical.issue_projection _ _ _ _ issued)
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      exact (drain_preserves_word admitted (Physical.drain_projection _ _ _ _ drained)).trans published
  | service action =>
    cases serviced : Futex.step cohort.profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      exact (service_preserves_word serviced).trans published

theorem word_domain_step {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result) : WordDomain cohort result.1 := by
  cases action with
  | issue worker =>
    cases issued : Physical.issue cohort.profile state worker with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      subst result
      exact issue_preserves_word_domain admitted (Physical.issue_projection _ _ _ _ issued)
  | drain worker =>
    cases drained : Physical.drain cohort.profile state worker with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      subst result
      exact drain_preserves_word_domain admitted (Physical.drain_projection _ _ _ _ drained)
  | service action =>
    cases serviced : Futex.step cohort.profile.service state action with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok after =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      subst result
      exact service_preserves_word_domain admitted.word serviced

end EDSL.OS.Futex.Predicate

#audit_edsl
