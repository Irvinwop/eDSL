/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Futex
import EDSL.Audit

namespace EDSL.Tests.FutexPhysical
open X86 OS OS.AddressSpace Examples.Futex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Counts concern actual decoded retirements. Service actions, resumptions and
-- FIFO drains must not count another SYSCALL or a synthetic user instruction.
example : OS.Futex.Runtime.retiredCount mismatch.2 = 6 := by rfl
example : OS.Futex.Runtime.retiredCount woken.2 = 13 := by rfl
example : OS.Futex.Runtime.retiredCount completed.2 = 5 := by rfl

-- Full-width raw EAGAIN is kept through the actual RET; RCX/R11 clobbers do
-- not replace the raw outcome, and the peer's new physical RAM is retained.
example : ∃ waiter,
    mismatch.1.suspended.machine.workers[0]? = some waiter ∧
    waiter.context.registers .rax = 0xfffffffffffffff5 ∧
    waiter.context.registers .rcx = 0x1234 ∧ waiter.context.registers .r11 = 0x5678 ∧
    waiter.context.flags = 0x8d7 ∧
    loadDWord mismatch.1.suspended.machine.memory 65536 = .ok 1 := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The FIFO's later publication remains coupled to the managed resource RAM,
-- preserving W and both completed workers' full returned contexts.
example :
    loadDWord (toMemory drained.1.authority.shared.resources.space) 131072 = .ok 0x11223344 ∧
    loadDWord (toMemory drained.1.authority.shared.resources.space) 65536 = .ok 1 ∧
    drained.1.suspended.machine.workers[0]? = woken.1.suspended.machine.workers[0]? ∧
    drained.1.suspended.machine.workers[1]? = woken.1.suspended.machine.workers[1]? := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- One wake can choose the second eligible call. It readies exactly that
-- waiter, retains the first waiter in the queue, and returns count one.
def secondChosen : OS.Futex.State := choice 1 (by rfl)

example : ∃ firstPin secondPin wakerPin,
    secondChosen.calls 0 = some ⟨0, .wait 0, firstPin, .queued⟩ ∧
    secondChosen.calls 1 = some ⟨3, .wait 0, secondPin, .ready .waitZero (.wake 2)⟩ ∧
    secondChosen.calls 2 = some ⟨1, .wakeOne, wakerPin, .ready .wakeOne (.wake 2)⟩ ∧
    secondChosen.queue = [0] := by
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

example : OS.Futex.wakeOne twoQueued.1 2 (some 2) = .error .ineligible := by rfl
example : OS.Futex.wakeOne twoQueued.1 2 none = .error .queueNotEmpty := by rfl
example : OS.Futex.resumeReady profile.service completed.1 0 0 0 0 = .error .missingCall := by rfl

def returnedBuffered : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile woken.1
    (waiterEntry 3 ++ [.service (.compare 2), .service (.resume 2 0 0 0), .issue 3, .issue 2])) (by rfl)

-- Every worker has really returned and every call/queue is consumed, yet
-- cleanup must wait for the producer's remaining physical store to publish.
example :
    returnedBuffered.1.suspended.machine.workers.all (fun worker => worker.returned) = true ∧
    returnedBuffered.1.queue = [] ∧
    OS.Futex.Lifecycle.collect cleanupPlan returnedBuffered.1 = .error .busy ∧
    loadDWord returnedBuffered.1.suspended.machine.memory 131072 = .ok 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def changedParked : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile parked.1 publisherExchange) (by rfl)

-- Publishing a different word alone does not remove a queued caller or imply
-- notification. This actual queued invocation still admits infinite parking.
example :
    loadDWord changedParked.1.suspended.machine.memory 65536 = .ok 1 ∧
    changedParked.1.queue = [0] ∧
    OS.Futex.Runtime.Infinite profile (fun _ => changedParked.1) (fun _ => .issue 0)
      (fun _ => .physical (.parked 0 0)) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

def retryEntered : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile parked.1
    (publisherExchange ++ [.service (.retry 0)])) (by rfl)

-- Internal retry consumes no invocation ID or pin, and preserves the actual
-- pending syscall while removing queue eligibility before the fresh read.
example : ∃ prior current,
    parked.1.calls 0 = some prior ∧ retryEntered.1.calls 0 = some current ∧
    current.pin = prior.pin ∧ current.worker = prior.worker ∧ current.op = prior.op ∧
    retryEntered.1.suspended.nextCall = parked.1.suspended.nextCall ∧
    (retryEntered.1.suspended.pending 0).map OS.Suspend.Saved.identifier =
      (parked.1.suspended.pending 0).map OS.Suspend.Saved.identifier ∧
    retryEntered.1.queue = [] := by
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Teardown must preserve the unrelated live loan and its independently
-- readable word. It must preserve the final published physical data too.
example :
    Borrowing.loadWord collected.authority.shared 99 8 196608 = .ok 0xa5a5a5a5 ∧
    loadDWord collected.suspended.machine.memory 131072 = .ok 0x11223344 ∧
    loadDWord collected.suspended.machine.memory 65536 = .ok 1 := by
  exact ⟨rfl, rfl, rfl⟩

def withTicket (state : Atomics.State) (operation : Ownership.Mutation) :
    Except Atomics.Fault (Atomics.State × Ownership.Ticket) := do
  let (after, result) ← Atomics.mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw .missingHandle

/-- Checked closure permits actual release/reallocation. The newly mapped
word can be accessed through new authority, while the old keeper stays revoked
even at the identical numerical address and actor. -/
def reclaim : Except Atomics.Fault (Except Atomics.Fault (BitVec 32) × BitVec 32) := do
  let (released, _) ← Atomics.mutate collected.authority (.release 7 registration.ticket)
  let (reallocated, ticket) ← withTicket released (.allocate 7 ⟨65536, 4⟩ readWrite)
  let (fresh, handle) ← Atomics.issue reallocated 7 ticket 90 65536
  let (_, previous) ← Atomics.exchange fresh 90 handle 0x12345678
  return (OS.Futex.Resources.readPinned fresh 90 registration.keeper, previous)

example : reclaim = .ok (.error .missingHandle, 0) := by rfl

end EDSL.Tests.FutexPhysical

#audit_edsl
