/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientFrames
import EDSL.Examples.FutexSafety
import EDSL.Audit

namespace EDSL.Tests.FutexClientFrames
open X86 OS OS.AddressSpace
open Examples.Futex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def payload : OS.Futex.Storage.Grant := ⟨7, ⟨1, 0⟩, 131072⟩

theorem payload_initial : payload.Valid initial.authority := by
  exact ⟨⟨7, 0, ⟨131072, 4⟩⟩, rfl, rfl, rfl, rfl, rfl⟩

-- This instantiates the generic preservation theorem on actual mixed client
-- execution, including XCHG, pin installation/closure and completed workers.
theorem payload_after_prefix {actions : List OS.Futex.Runtime.Action}
    {result : OS.Futex.State × List OS.Futex.Runtime.Observation}
    (actual : OS.Futex.Runtime.schedule profile initial actions = .ok result) :
    payload.Valid result.1.authority :=
  OS.Futex.Clients.runtime_schedule_grant initial_invariant payload_initial actual

-- Arbitrary call actors (including keeper/producer actors) and payload values
-- remain enabled together. Publication comes from current authority, without
-- requiring a successful future update as a premise.
theorem publication_with_live_call (actor : Nat) (value : BitVec 32) :
    ∃ active after pin,
      OS.Futex.Resources.retainCall initial.authority registration actor = .ok (active, pin) ∧
      OS.Futex.Storage.publish active payload value = .ok after ∧
      OS.Futex.Resources.Valid after registration ∧
      loadDWord (toMemory after.shared.resources.space) payload.address = .ok value ∧
      loadDWord (toMemory after.shared.resources.space) registration.address = .ok 0 := by
  obtain ⟨retained, ready⟩ := OS.Futex.Clients.retainCall_grant_enabled
    initial_valid.authority initial_registration_live payload_initial actor
  let active := Atomics.install initial.authority (registration.callHandle actor)
  have activeValid : Atomics.WellFormed active :=
    (OS.Futex.Resources.retainCall_effect _ _ _ _ initial_valid.authority retained).1
  have keeper : OS.Futex.Resources.Valid active registration :=
    (OS.Futex.Resources.retainCall_effect _ _ _ _ initial_valid.authority retained).2.1
  obtain ⟨after, published⟩ := OS.Futex.Storage.publish_enabled active payload value ready
  have effect := OS.Futex.Storage.publish_effect published
  have writable : canStoreDWord (toMemory active.shared.resources.space) payload.address = true :=
    ready.choose_spec.2.2.1
  have addressable := (Bool.and_eq_true_iff.mp writable).1
  have separated := ready.disjoint_keeper_word activeValid keeper
  refine ⟨active, after, initial.authority.nextHandle, retained, published, ?_, ?_, ?_⟩
  · simpa only [OS.Futex.Resources.Valid, effect.2.2.1] using keeper
  · rw [effect.2.1]
    exact load_after_write _ _ _ addressable
  · rw [effect.2.1]
    exact (loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ separated)).trans (by rfl)

-- Every authorized FIFO preserves all eight stack bytes and the full code
-- window, even when the code and return are interpreted through forwarding.
theorem fifo_protects_return (buffer : StoreBuffer.Buffer)
    (authorized : ∀ store ∈ buffer, ∃ grant : OS.Futex.Storage.Grant,
      grant.address = store.address ∧ grant.Valid initial.authority) :
    readWord (StoreBuffer.view initial.suspended.machine.memory buffer) 32768 = .ok 24576 ∧
      CodeAt (StoreBuffer.view initial.suspended.machine.memory buffer) 4096
        Examples.FutexStubs.Profile.wait.bytes := by
  have stack : Threads.HasLoan initial.authority.shared 9 1 ⟨32768, 8⟩ :=
    ⟨_, rfl, rfl, rfl⟩
  have code : Threads.HasLoan initial.authority.shared 9 0 ⟨4096, 13⟩ :=
    ⟨_, rfl, rfl, rfl⟩
  have stackFrame : ∀ store ∈ buffer, DWordDisjoint store.address 32768 8 := by
    intro store member
    obtain ⟨grant, address, ready⟩ := authorized store member
    rw [← address]
    exact ready.disjoint_hasLoan initial_valid.authority stack
  have codeFrame : ∀ store ∈ buffer, DWordDisjoint store.address 4096 13 := by
    intro store member
    obtain ⟨grant, address, ready⟩ := authorized store member
    rw [← address]
    exact ready.disjoint_hasLoan initial_valid.authority code
  constructor
  · rw [StoreBuffer.view_readWord_frame _ _ _ stackFrame]
    rfl
  · apply StoreBuffer.view_code _ _ _ _ _ codeFrame
    refine ⟨by decide, ?_⟩
    intro offset byte present
    have bound := (List.getElem_of_getElem? present).1
    change offset < 13 at bound
    have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨
        offset = 5 ∨ offset = 6 ∨ offset = 7 ∨ offset = 8 ∨ offset = 9 ∨ offset = 10 ∨
        offset = 11 ∨ offset = 12 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Examples.FutexStubs.Profile.bytes] at present <;> subst byte <;> rfl

-- A write to the upper half of the protected eight-byte return slot cannot
-- gain ordinary authority, despite the underlying stack's mapped bytes.
example : ¬ (OS.Futex.Storage.Grant.mk 7 ⟨5, 0⟩ 32772).Valid initial.authority := by
  intro ready
  have same := ready.different_loan_ticket initial_valid.authority
    (identifier := 1) (loan := ⟨⟨5, 0⟩, 7, 10, ⟨32768, 8⟩⟩) (by rfl)
  exact same rfl

-- Add an independently owned payload for a second actual store/RET worker.
-- The original code/stack loans and futex keeper remain live resources.
def extended : Atomics.State × Option Ownership.Ticket :=
  checked (Atomics.mutate initial.authority (.allocate 8 ⟨262144, 4⟩ readWrite)) (by rfl)

theorem extended_valid : Atomics.WellFormed extended.1 :=
  Atomics.mutate_wellFormed _ _ _ initial_valid.authority (checked_ok _ _)

def peerPayload : OS.Futex.Storage.Grant := ⟨8, ⟨10, 0⟩, 262144⟩

def pairProfile : OS.Futex.Physical.Profile :=
  { service := profile.service
    payload := fun worker => if worker = 0 then some payload
      else if worker = 1 then some peerPayload else none
    atomic := fun _ => none }

def peerContext : Threads.Context :=
  { context 2 with registers := fun register =>
      if register = .rsp then 32864
      else if register = .rsi then peerPayload.address
      else (context 2).registers register }

def pairInitial : OS.Futex.State :=
  OS.Futex.Runtime.initial extended.1 (some registration)
    [⟨context 2, false, []⟩, ⟨peerContext, false, []⟩]

theorem pairInvariant : OS.Futex.Runtime.Invariant pairProfile pairInitial := by
  apply OS.Futex.Runtime.initial_invariant _ _ _ _ extended_valid
  intro worker member store queued
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> cases queued

theorem firstReady : payload.Valid pairInitial.authority := by
  exact ⟨⟨7, 0, ⟨131072, 4⟩⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem secondReady : peerPayload.Valid pairInitial.authority := by
  exact ⟨⟨8, 0, ⟨262144, 4⟩⟩, rfl, rfl, rfl, rfl, rfl⟩

def pairActions : List OS.Futex.Runtime.Action :=
  [.issue 0, .issue 0, .issue 1, .issue 1, .issue 0]

def pairReturned : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule pairProfile pairInitial pairActions) (by rfl)

theorem pairReturned_ok :
    OS.Futex.Runtime.schedule pairProfile pairInitial pairActions = .ok pairReturned := checked_ok _ _

theorem returnedInvariant : OS.Futex.Runtime.Invariant pairProfile pairReturned.1 :=
  (OS.Futex.Runtime.schedule_invariant pairInvariant pairReturned_ok).1

theorem returnedFirstReady : payload.Valid pairReturned.1.authority :=
  OS.Futex.Clients.runtime_schedule_grant pairInvariant firstReady pairReturned_ok

theorem returnedSecondReady : peerPayload.Valid pairReturned.1.authority :=
  OS.Futex.Clients.runtime_schedule_grant pairInvariant secondReady pairReturned_ok

-- Actual RET retained its complete FIFO, preserved the peer FIFO, read the
-- original return target, and retained both payload grants through that RET.
example : ∃ producer peer,
    pairReturned.1.suspended.machine.workers[0]? = some producer ∧ producer.returned = true ∧
    producer.context.rip = 24576 ∧ producer.context.registers .rsp = 32840 ∧
    producer.buffer = [⟨131072, 0x11223344⟩] ∧
    pairReturned.1.suspended.machine.workers[1]? = some peer ∧ peer.returned = false ∧
    peer.buffer = [⟨262144, 0x11223344⟩] ∧
    payload.Valid pairReturned.1.authority ∧ peerPayload.Valid pairReturned.1.authority := by
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, returnedFirstReady, returnedSecondReady⟩

def physicalDrain : Suspend.State × Suspend.Observation :=
  checked (Suspend.drain pairReturned.1.suspended 0) (by rfl)

-- Current grant authority enables replay of the returned producer's actual
-- drain. Its peer remains buffered, unreturned and unchanged. Both grants
-- survive publication, so producer liveness never substitutes for authority.
theorem returned_drain_enabled :
    ∃ after,
      OS.Futex.Physical.drain pairProfile pairReturned.1 0 =
        .ok (after, .machine (.drained 0 ⟨131072, 0x11223344⟩)) ∧
      payload.Valid after.authority ∧ peerPayload.Valid after.authority ∧
      loadDWord after.suspended.machine.memory 131072 = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory 262144 = .ok 0 ∧
      after.suspended.machine.workers[1]? = pairReturned.1.suspended.machine.workers[1]? ∧
      ∃ producer, after.suspended.machine.workers[0]? = some producer ∧
        producer.returned = true ∧ producer.buffer = [] := by
  have actual : Suspend.drain pairReturned.1.suspended 0 =
      .ok (physicalDrain.1, .machine (.drained 0 ⟨131072, 0x11223344⟩)) := by rfl
  have ready : OS.Futex.Physical.Ready pairProfile pairReturned.1.authority
      (.machine (.drained 0 ⟨131072, 0x11223344⟩)) :=
    ⟨payload, rfl, rfl, returnedFirstReady⟩
  obtain ⟨authority, replay, _, _, _⟩ := OS.Futex.Physical.synchronize_enabled
    pairProfile pairReturned.1.authority _ _ _ returnedInvariant.service.authority
    returnedInvariant.memory ready (OS.Futex.Physical.drain_effect actual)
  let after : OS.Futex.State :=
    { pairReturned.1 with suspended := physicalDrain.1, authority := authority }
  have lifted : OS.Futex.Physical.drain pairProfile pairReturned.1 0 =
      .ok (after, .machine (.drained 0 ⟨131072, 0x11223344⟩)) := by
    simp only [OS.Futex.Physical.drain, actual, Except.mapError]
    change (do
      let next ← OS.Futex.Physical.synchronize pairProfile pairReturned.1.authority
        (.machine (.drained 0 ⟨131072, 0x11223344⟩))
      pure ({ pairReturned.1 with suspended := physicalDrain.1, authority := next },
        Suspend.Observation.machine (.drained 0 ⟨131072, 0x11223344⟩))) =
      .ok (after, Suspend.Observation.machine (.drained 0 ⟨131072, 0x11223344⟩))
    rw [replay]
    rfl
  exact ⟨after, lifted, OS.Futex.Clients.drain_grant returnedFirstReady lifted,
    OS.Futex.Clients.drain_grant returnedSecondReady lifted, rfl, rfl, rfl, _, rfl, rfl, rfl⟩

end EDSL.Tests.FutexClientFrames

#audit_edsl
