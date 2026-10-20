/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientControl
import EDSL.Audit

namespace EDSL.Tests.FutexClientControl
open X86 OS OS.Futex OS.Futex.Clients

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem request_ext {left right : SyscallRequest}
    (registers : ∀ register, left.user.registers register = right.user.registers register)
    (rip : left.user.rip = right.user.rip) (flags : left.user.flags = right.user.flags)
    (ram : left.user.memory = right.user.memory) (continuation : left.continuation = right.continuation) :
    left = right := by
  rcases left with ⟨⟨_, _, _, _⟩, _⟩
  rcases right with ⟨⟨_, _, _, _⟩, _⟩
  simp only [SyscallRequest.mk.injEq, X86.State.mk.injEq]
  exact ⟨⟨funext registers, rip, flags, ram⟩, continuation⟩

private theorem context_ext {left right : Threads.Context}
    (registers : ∀ register, left.registers register = right.registers register)
    (rip : left.rip = right.rip) (flags : left.flags = right.flags) : left = right := by
  rcases left with ⟨_, _, _⟩
  rcases right with ⟨_, _, _⟩
  simp only [Threads.Context.mk.injEq]
  exact ⟨funext registers, rip, flags⟩

private def memory : Memory where
  read address :=
    if 8192 ≤ address.toNat ∧ address.toNat < 8224 then publishingBytes[address.toNat - 8192]?
    else if 16384 ≤ address.toNat ∧ address.toNat < 16392 then peerBytes[address.toNat - 16384]?
    else if 4096 ≤ address.toNat ∧ address.toNat < 4109 then (Role.wait 0xfedcba98).bytes[address.toNat - 4096]?
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (32800 ≤ address.toNat ∧ address.toNat < 32808) ∨
        (32832 ≤ address.toNat ∧ address.toNat < 32840) then
      some (if address.toNat % 32 = 1 then 0x60 else 0)
    else if (65536 ≤ address.toNat ∧ address.toNat < 65540) ∨
        (131072 ≤ address.toNat ∧ address.toNat < 131076) ∨
        (196608 ≤ address.toNat ∧ address.toNat < 196612) then some 0
    else none
  executable address := decide ((8192 ≤ address.toNat ∧ address.toNat < 8224) ∨
    (16384 ≤ address.toNat ∧ address.toNat < 16392) ∨ (4096 ≤ address.toNat ∧ address.toNat < 4109))
  writable address := decide ((65536 ≤ address.toNat ∧ address.toNat < 65540) ∨
    (131072 ≤ address.toNat ∧ address.toNat < 131076) ∨ (196608 ≤ address.toNat ∧ address.toNat < 196612))

private def entry (pc stack payload : Word) : Threads.Context :=
  { registers := fun register =>
      if register = .rdi then 65536 else if register = .rsi then payload
      else if register = .rsp then stack else if register = .rdx then 0xfedcba98
      else if register = .r10 ∨ register = .r8 ∨ register = .r9 then 0
      else 0xfedcba9876543210
    rip := pc
    flags := 0x8d7 }

private def publisher : Client := ⟨.publishPayloadWake, entry 8192 32768 131072, 0, 0, 1, 24576⟩
private def peer : Client := ⟨.payloadPeer, entry 16384 32800 196608, 1, 2, 3, 24576⟩
private def waiter : Client := ⟨.wait 0xfedcba98, entry 4096 32832 0, 2, 4, 5, 24576⟩

private def initial : Suspend.State :=
  Suspend.initial ⟨memory, [⟨publisher.entry, false, []⟩, ⟨peer.entry, false, []⟩, ⟨waiter.entry, false, []⟩]⟩

private def peerReturned : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule initial [.issue 1, .issue 1, .issue 1]) (by rfl)

private def storePending : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule peerReturned.1 [.issue 0, .issue 0, .issue 0, .issue 0]) (by rfl)

-- The real same-worker FIFO blocks XCHG and does not publish P early.
-- A peer has already returned while its distinct Q value remains pending.
example : storePending.2 = [.machine (.retired 0 none), .machine (.retired 0 none),
      .machine (.retired 0 none), .machine (.blocked 0)] ∧
    loadDWord storePending.1.machine.memory 131072 = .ok 0 ∧
    ∃ worker, storePending.1.machine.workers[1]? = some worker ∧ worker.returned = true ∧
      worker.buffer = [⟨196608, 0x55667788⟩] := by
  exact ⟨rfl, rfl, _, rfl, rfl, rfl⟩

private def exchanged : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule storePending.1 [.drain 0, .issue 0]) (by rfl)

-- Draining the caller enables exactly its XCHG. The peer is not flushed,
-- and the publisher's payload survives the atomic write to W.
example : exchanged.2 = [.machine (.drained 0 ⟨131072, 0x11223344⟩),
      .machine (.retired 0 (some ⟨65536, 0, 1⟩))] ∧
    loadDWord exchanged.1.machine.memory 131072 = .ok 0x11223344 ∧
    loadDWord exchanged.1.machine.memory 65536 = .ok 1 ∧
    loadDWord exchanged.1.machine.memory 196608 = .ok 0 ∧
    exchanged.1.machine.workers[1]? = storePending.1.machine.workers[1]? := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private def wakeEntered : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule exchanged.1 [.issue 0, .issue 0, .issue 0, .issue 0]) (by rfl)

-- The 32-byte publication client actually reaches its WAKE suffix with
-- canonical full-width arguments and the original private preserved fields.
example : ∃ saved, wakeEntered.1.pending 0 = some saved ∧ publisher.Family saved.request ∧
    classify saved.request = .ok .wakeOne ∧ saved.request.continuation = 8223 ∧
    saved.request.user.registers .rdi = 65536 ∧
    saved.request.user.registers .rbx = 0xfedcba9876543210 := by
  refine ⟨_, rfl, ⟨by decide, ?_⟩, rfl, rfl, rfl, rfl⟩
  apply request_ext
  · intro register
    cases register <;> rfl
  all_goals rfl

private def peerDrained : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule wakeEntered.1 [.drain 1]) (by rfl)

-- This instantiates the generic control theorem on an actual already-returned
-- worker with a nonempty FIFO, rather than testing cleanup rejection again.
example : ∃ worker, peerDrained.1.machine.workers[1]? = some worker ∧
    WorkerControl peer 1 peerDrained.1 worker := by
  let actualPeer := (wakeEntered.1.machine.workers[1]?).get (by rfl)
  have before : WorkerControl peer 1 wakeEntered.1 actualPeer := by
    refine .peerReturned rfl ?_ rfl rfl (Or.inr rfl)
    apply context_ext
    · intro register
      cases register <;> rfl
    all_goals rfl
  exact before.drain_selected (by rfl) (by rfl)

private def waitEntered : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule wakeEntered.1 [.issue 2, .issue 2, .issue 2]) (by rfl)

private def changedWaiting : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule waitEntered.1 [.drain 1]) (by rfl)

private def resumed : Suspend.State :=
  checked (Suspend.resume changedWaiting.1 2 1 (Outcome.waitAgain (expected := 0xfedcba98)).raw
    0xffffffffffffffff 0x8877665544332211 0x1122334455667788) (by rfl)

private def waitReturned : Suspend.State × List Suspend.Observation :=
  checked (Suspend.schedule resumed [.issue 2]) (by rfl)

-- A high expected32, full raw -11 and arbitrary full clobbers survive actual
-- resume/RET. Current peer RAM remains current; capture memory stays historic.
example : ∃ saved worker, waitEntered.1.pending 2 = some saved ∧ waiter.Family saved.request ∧
    classify saved.request = .ok (.wait 0xfedcba98) ∧
    loadDWord saved.request.user.memory 196608 = .ok 0 ∧
    waitReturned.1.machine.workers[2]? = some worker ∧ worker.returned = true ∧
    worker.context.registers .rax = 0xfffffffffffffff5 ∧
    worker.context.registers .rcx = 0x8877665544332211 ∧
    worker.context.registers .r11 = 0x1122334455667788 ∧
    worker.context.flags = 0xffffffffffffffff ∧ worker.context.rip = 24576 ∧
    worker.context.registers .rsp = 32840 ∧
    loadDWord waitReturned.1.machine.memory 196608 = .ok 0x55667788 ∧
    waitReturned.1.machine.workers[0]? = waitEntered.1.machine.workers[0]? := by
  refine ⟨_, _, rfl, ⟨by decide, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply request_ext
  · intro register
    cases register <;> rfl
  all_goals rfl

end EDSL.Tests.FutexClientControl

#audit_edsl
