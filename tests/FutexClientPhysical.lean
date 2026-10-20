/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientPhysical
import EDSL.Examples.FutexClient
import EDSL.Examples.FutexSafety
import EDSL.Audit

namespace EDSL.Tests.FutexClientPhysical
open X86 OS OS.AddressSpace Examples.Futex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- An actual pending WAIT, an actual publisher exchange, a real compare
which derives EAGAIN, and an unrelated peer's still nonempty FIFO. -/
def mismatchReadyActions : List Futex.Runtime.Action :=
  queuePayload ++ [.issue 2] ++ waiterEntry 0 ++ publisherExchange ++ [.service (.compare 0)]

def mismatchReady : Futex.State × List Futex.Runtime.Observation :=
  checked (Futex.Runtime.schedule profile initial mismatchReadyActions) (by rfl)

theorem mismatchReady_invariant : Futex.Runtime.Invariant profile mismatchReady.1 :=
  (every_prefix (checked_ok _ _)).1

def mismatchCall : Futex.Call := ⟨0, .wait 0, 2, .ready .waitAgain .mismatch⟩

def mismatchSaved : Suspend.Saved := (mismatchReady.1.suspended.pending 0).get (by rfl)

-- Arbitrary full private clobbers cannot prevent enabled resume/RET, truncate
-- the typed negative raw result, restore historical W=0, or flush the peer.
-- The result is derived from current ready service state, without a premise
-- asserting successful future resume, RET, adapter replay or completion.
theorem mismatch_ready_returns (flags rcx r11 : Word) :
    ∃ resumed after returned,
      Futex.resumeReady profile.service mismatchReady.1 0 flags rcx r11 = .ok resumed ∧
      Futex.Physical.issue profile resumed 0 = .ok (after, .machine (.retired 0 none)) ∧
      after.suspended.machine.workers[0]? = some returned ∧
      returned.returned = true ∧ returned.context.registers .rax = 0xfffffffffffffff5 ∧
      returned.context.rip = 24576 ∧ returned.context.registers .rsp = 32776 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
      after.suspended.machine.workers[2]? = mismatchReady.1.suspended.machine.workers[2]? ∧
      after.suspended.pending 2 = mismatchReady.1.suspended.pending 2 ∧
      Futex.Runtime.Invariant profile after := by
  have found : mismatchReady.1.calls 0 = some mismatchCall := rfl
  have pending : mismatchReady.1.suspended.pending mismatchCall.worker = some mismatchSaved := rfl
  have code : CodeAt mismatchReady.1.suspended.machine.memory mismatchSaved.request.continuation [0xc3] := by
    refine ⟨by decide, ?_⟩
    intro offset byte present
    cases offset with
    | zero =>
      have same : byte = 0xc3 := by simpa using present.symm
      subst byte
      rfl
    | succ offset => simp at present
  have stack : readWord mismatchReady.1.suspended.machine.memory
      (mismatchSaved.request.user.registers .rsp) = .ok 24576 := rfl
  obtain ⟨resumed, after, returned, resume, issue, live, done, empty, raw, target, stackPointer,
    privateFlags, privateRcx, privateR11, memory, peers, resumedInv, afterInv⟩ :=
    Futex.Clients.LiftCore.resume_ret_enabled mismatchReady_invariant found
      (outcome := .waitAgain) (origin := .mismatch) rfl pending code stack (by decide) flags rcx r11
  refine ⟨resumed, after, returned, resume, issue, live, done, raw, target, stackPointer,
    privateFlags, privateRcx, privateR11, ?_, (peers 2 (by decide)).1, (peers 2 (by decide)).2, afterInv⟩
  rw [memory]
  rfl

def returnedDrain : Suspend.State × Suspend.Observation :=
  checked (Suspend.drain mismatchReady.1.suspended 2) (by rfl)

-- A returned producer can actually drain while an unrelated typed ready
-- service call remains pending. The current retained grant enables the new
-- generic lift; neither producer liveness nor service completion is needed.
theorem returned_ready_peer_drain :
    ∃ after producer,
      Futex.Physical.drain profile mismatchReady.1 2 =
        .ok (after, .machine (.drained 2 ⟨131072, 0x11223344⟩)) ∧
      after.suspended.machine.workers[2]? = some producer ∧
      producer.returned = true ∧ producer.buffer = [] ∧
      after.suspended.pending 0 = mismatchReady.1.suspended.pending 0 ∧
      after.suspended.machine.workers[0]? = mismatchReady.1.suspended.machine.workers[0]? ∧
      loadDWord after.suspended.machine.memory 131072 = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
      Futex.Runtime.Invariant profile after ∧
      (Futex.Storage.Grant.mk 7 ⟨1, 0⟩ 131072).Valid after.authority := by
  let grant : Futex.Storage.Grant := ⟨7, ⟨1, 0⟩, 131072⟩
  have grantInitial : grant.Valid initial.authority :=
    ⟨⟨7, 0, ⟨131072, 4⟩⟩, rfl, rfl, rfl, rfl, rfl⟩
  have grantReady : grant.Valid mismatchReady.1.authority :=
    Futex.Clients.runtime_schedule_grant initial_invariant grantInitial (checked_ok _ _)
  have ready : Futex.Physical.Ready profile mismatchReady.1.authority
      (.machine (.drained 2 ⟨131072, 0x11223344⟩)) := ⟨grant, rfl, rfl, grantReady⟩
  have actual : Suspend.drain mismatchReady.1.suspended 2 =
      .ok (returnedDrain.1, .machine (.drained 2 ⟨131072, 0x11223344⟩)) := rfl
  obtain ⟨after, drained, physical, invariant, history⟩ :=
    Futex.Clients.LiftCore.drain_enabled mismatchReady_invariant ready actual
  let producer := (returnedDrain.1.machine.workers[2]?).get (by rfl)
  refine ⟨after, producer, drained, ?_, rfl, rfl, ?_, ?_, ?_, ?_, invariant,
    Futex.Clients.drain_grant grantReady drained⟩
  all_goals rw [physical]; rfl

def selectedReadyActions : List Futex.Runtime.Action :=
  queuePayload ++ waiterEntry 0 ++ [.service (.compare 0)] ++ publisherExchange ++
    publisherEntry ++ [.service (.wake 1 (some 0))]

def selectedReady : Futex.State × List Futex.Runtime.Observation :=
  checked (Futex.Runtime.schedule profile initial selectedReadyActions) (by rfl)

def wakeCall : Futex.Call := ⟨1, .wakeOne, 3, .ready .wakeOne (.wake 1)⟩

def wakeSaved : Suspend.Saved := (selectedReady.1.suspended.pending 1).get (by rfl)

-- Selecting a real eligible waiter derives count one. Its typed result can
-- return through the actual waker RET under arbitrary clobbers, while the
-- selected waiter's ready pending request and the buffered peer both survive.
theorem selected_wake_returns (flags rcx r11 : Word) :
    ∃ resumed after returned,
      Futex.resumeReady profile.service selectedReady.1 1 flags rcx r11 = .ok resumed ∧
      Futex.Physical.issue profile resumed 1 = .ok (after, .machine (.retired 1 none)) ∧
      after.suspended.machine.workers[1]? = some returned ∧
      returned.returned = true ∧ returned.context.registers .rax = 1 ∧
      returned.context.rip = 24576 ∧ returned.context.registers .rsp = 32808 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      after.suspended.pending 0 = selectedReady.1.suspended.pending 0 ∧
      after.suspended.machine.workers[2]? = selectedReady.1.suspended.machine.workers[2]? ∧
      after.suspended.machine.memory = selectedReady.1.suspended.machine.memory ∧
      Futex.Runtime.Invariant profile after := by
  have valid : Futex.Runtime.Invariant profile selectedReady.1 :=
    (every_prefix (checked_ok _ _)).1
  have found : selectedReady.1.calls 1 = some wakeCall := rfl
  have pending : selectedReady.1.suspended.pending wakeCall.worker = some wakeSaved := rfl
  have code : CodeAt selectedReady.1.suspended.machine.memory wakeSaved.request.continuation [0xc3] := by
    refine ⟨by decide, ?_⟩
    intro offset byte present
    cases offset with
    | zero =>
      have same : byte = 0xc3 := by simpa using present.symm
      subst byte
      rfl
    | succ offset => simp at present
  have stack : readWord selectedReady.1.suspended.machine.memory
      (wakeSaved.request.user.registers .rsp) = .ok 24576 := rfl
  obtain ⟨resumed, after, returned, resume, issue, live, done, empty, raw, target, stackPointer,
    privateFlags, privateRcx, privateR11, memory, peers, resumedInv, afterInv⟩ :=
    Futex.Clients.LiftCore.resume_ret_enabled valid found
      (outcome := .wakeOne) (origin := .wake 1) rfl pending code stack (by decide) flags rcx r11
  exact ⟨resumed, after, returned, resume, issue, live, done, raw, target, stackPointer,
    privateFlags, privateRcx, privateR11, (peers 0 (by decide)).2, (peers 2 (by decide)).1,
    memory, afterInv⟩

namespace CohortCoverage

abbrev fixture := Examples.FutexClient.cohort

def returnedPeer : Futex.State × List Futex.Runtime.Observation :=
  checked (Futex.Runtime.schedule Examples.FutexClient.profile Examples.FutexClient.initial
    [.issue 2, .issue 2, .issue 2]) (by rfl)

def physicalDrain : Suspend.State × Suspend.Observation :=
  checked (Suspend.drain returnedPeer.1.suspended 2) (by rfl)

-- This is the complete admitted-client lift on an actually returned buffered
-- producer, rather than an extra check of cleanup rejection. The drain keeps
-- its returned context, current rights and all other real worker records.
theorem returned_peer_lift :
    ∃ after producer,
      Futex.Physical.drain Examples.FutexClient.profile returnedPeer.1 2 =
        .ok (after, .machine (.drained 2 ⟨131072, 0x55667788⟩)) ∧
      Futex.Clients.Admitted fixture after ∧
      after.suspended.machine.workers[2]? = some producer ∧
      producer.returned = true ∧ producer.buffer = [] ∧
      producer.context.rip = 0x6200 ∧ producer.context.registers .rsp = 32840 ∧
      loadDWord after.suspended.machine.memory 131072 = .ok 0x55667788 ∧
      after.suspended.machine.workers[1]? = returnedPeer.1.suspended.machine.workers[1]? := by
  have admitted : Futex.Clients.Admitted fixture returnedPeer.1 :=
    Examples.FutexClient.initial_admitted.schedule (checked_ok _ _)
  have actual : Suspend.drain returnedPeer.1.suspended 2 =
      .ok (physicalDrain.1, .machine (.drained 2 ⟨131072, 0x55667788⟩)) := rfl
  obtain ⟨after, drained, exactPhysical, afterAdmitted⟩ := Futex.Clients.drain_lift admitted actual
  let producer := (physicalDrain.1.machine.workers[2]?).get (by rfl)
  refine ⟨after, producer, drained, afterAdmitted, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals rw [exactPhysical]; rfl

/-- The own payload STORE leaves XCHG blocked until its actual FIFO drain.
The returned peer's different FIFO stays nonempty throughout this prefix. -/
def publishingReadyActions : List Futex.Runtime.Action :=
  [.issue 2, .issue 2, .issue 2,
   .issue 0, .issue 0, .issue 0, .service (.compare 0),
   .issue 1, .issue 1, .issue 1, .issue 1, .drain 1,
   .issue 1, .issue 1, .issue 1, .issue 1, .issue 1,
   .service (.wake 1 (some 0))]

def publishingReady : Futex.State × List Futex.Runtime.Observation :=
  checked (Futex.Runtime.schedule Examples.FutexClient.profile Examples.FutexClient.initial
    publishingReadyActions) (by rfl)

-- The concrete same-worker publisher's actual selected-WAKE result returns
-- through its protected RET at offset31. No successful future resume/RET is
-- a premise; the generic complete admitted-client theorem enables both.
theorem publisher_ready_ret (flags rcx r11 : Word) :
    ∃ resumed after returned,
      Futex.resumeReady Examples.FutexClient.profile.service publishingReady.1 1 flags rcx r11 = .ok resumed ∧
      Futex.Physical.issue Examples.FutexClient.profile resumed 1 = .ok (after, .machine (.retired 1 none)) ∧
      Futex.Clients.Admitted fixture resumed ∧ Futex.Clients.Admitted fixture after ∧
      after.suspended.machine.workers[1]? = some returned ∧ returned.returned = true ∧
      returned.context.registers .rax = 1 ∧ returned.context.rip = 0x6100 ∧
      returned.context.registers .rsp = 32808 ∧ returned.context.flags = flags ∧
      returned.context.registers .rcx = rcx ∧ returned.context.registers .r11 = r11 ∧
      loadDWord after.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
      loadDWord after.suspended.machine.memory 131072 = .ok 0 ∧
      after.suspended.pending 0 = publishingReady.1.suspended.pending 0 ∧
      after.suspended.machine.workers[2]? = publishingReady.1.suspended.machine.workers[2]? := by
  have admitted : Futex.Clients.Admitted fixture publishingReady.1 :=
    Examples.FutexClient.initial_admitted.schedule (checked_ok _ _)
  let call : Futex.Call := ⟨1, .wakeOne, 3, .ready .wakeOne (.wake 1)⟩
  have found : publishingReady.1.calls 1 = some call := rfl
  obtain ⟨resumed, after, returned, client, member, resume, issue, live, done, empty, raw,
    target, stackPointer, privateFlags, privateRcx, privateR11, memory, peers, resumedAd, afterAd⟩ :=
    Futex.Clients.ready_ret_enabled admitted found (outcome := .wakeOne) (origin := .wake 1)
      rfl flags rcx r11
  have sameClient : client = Examples.FutexClient.publisher := Option.some.inj member.symm
  subst client
  refine ⟨resumed, after, returned, resume, issue, resumedAd, afterAd, live, done, raw, target,
    stackPointer, privateFlags, privateRcx, privateR11, ?_, ?_, ?_, (peers 0 (by decide)).2,
    (peers 2 (by decide)).1⟩
  all_goals rw [memory]; rfl

def publisherFirst : Futex.State × Suspend.Observation :=
  checked (Futex.Physical.issue Examples.FutexClient.profile Examples.FutexClient.initial 1) (by rfl)

def wrongDestination : Threads.Context :=
  let context := ((publisherFirst.1.suspended.machine.workers[1]?).get (by rfl)).context
  { context with registers := fun register => if register = .rsi then 131072 else context.registers register }

def unauthorized : Futex.State :=
  let machine := TSO.install publisherFirst.1.suspended.machine 1
    publisherFirst.1.suspended.machine.memory wrongDestination false []
  { publisherFirst.1 with suspended := { publisherFirst.1.suspended with machine := machine } }

def unauthorizedRetirement : Futex.State × Suspend.Observation :=
  checked (Futex.Physical.issue Examples.FutexClient.profile unauthorized 1) (by rfl)

-- The writable Q destination is accepted by ordinary physical STORE enqueue.
-- Current admission excludes it through the independently proved generic
-- authorization theorem, and a later adapter drain rejects its wrong address.
theorem unauthorized_enqueue_excluded :
    Futex.Physical.issue Examples.FutexClient.profile unauthorized 1 =
      .ok unauthorizedRetirement ∧
      Futex.Physical.drain Examples.FutexClient.profile unauthorizedRetirement.1 1 = .error .wrongAddress ∧
      ¬ Futex.Clients.Admitted fixture unauthorized := by
  refine ⟨checked_ok _ _, rfl, ?_⟩
  intro admitted
  let worker := (unauthorized.suspended.machine.workers[1]?).get (by rfl)
  have live : unauthorized.suspended.machine.workers[1]? = some worker := rfl
  have running : worker.returned = false := rfl
  have free : unauthorized.suspended.pending 1 = none := rfl
  have decoded : decodeAt (TSO.sharedState unauthorized.suspended.machine worker) = .ok .storeEaxRsi := rfl
  have intent : TSO.pendingStore worker.context .storeEaxRsi = some ⟨131072, 0x11223344⟩ := rfl
  obtain ⟨grant, atGrant, address, ready⟩ := Futex.Clients.store_intent_authorized admitted.control
    (fun i client member => (admitted.protected i client member).2.2.1)
    admitted.static.descriptors admitted.payload live running free decoded intent
  have same : grant = Examples.FutexClient.publisherGrant := Option.some.inj atGrant.symm
  subst grant
  exact (by decide : (Examples.FutexClient.publisherGrant.address = 131072) → False) address

end CohortCoverage

end EDSL.Tests.FutexClientPhysical

#audit_edsl
