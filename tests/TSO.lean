/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.StoreBuffer
import EDSL.Examples.MutexExecution
import EDSL.Audit

namespace EDSL.Tests.TSO
open X86 OS OS.AddressSpace TSO Examples.StoreBuffer

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev litmusInitial := Examples.StoreBuffer.initial

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def delayedResult : TSO.State × List Observation := checked (TSO.schedule litmusInitial delayed) (by rfl)

def completeResult : TSO.State × List Observation := checked (TSO.schedule litmusInitial complete) (by rfl)

-- Independent store-buffer outcome: both loads return litmusInitial zero before
-- either store publishes. An SC implementation cannot produce this result.
example : observe delayedResult.1 = ([0, 0], some 0, some 0, [(false, 1), (false, 1)]) := by rfl

-- RET does not flush ordinary stores. Completion and publication differ;
-- draining retired callers later retains their actual return contexts.
def returnedResult : TSO.State × List Observation :=
  checked (TSO.schedule litmusInitial (delayed ++ [.issue 0, .issue 1])) (by rfl)

example : observe returnedResult.1 = ([0, 0], some 0, some 0, [(true, 1), (true, 1)]) := by rfl
example : observe completeResult.1 = ([0, 0], some 1, some 1, [(true, 0), (true, 0)]) := by rfl
example : retiredCount completeResult.2 = 6 ∧ completeResult.2.length = 8 := ⟨rfl, rfl⟩
example : completeResult.1.workers.map (fun worker => (worker.context.registers .rsp, worker.context.rip)) =
    [(32776, 8192), (32776, 8192)] := by rfl

-- The six interleavings of two stores followed by two loads all exclude the
-- same both-zero result on the prior immediate-visibility machine.
def orders : List (List Nat) := [[0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0],
  [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]]

def sequentialResults : List (Option (List Word)) := orders.map fun selections =>
  (MachineThreads.schedule sequential selections).toOption.map fun result =>
    result.1.workers.map (fun worker => worker.context.registers .rax)

example : sequentialResults = [some [0, 1], some [1, 1], some [1, 1],
    some [1, 1], some [1, 1], some [1, 0]] := by rfl

-- Same-address forwarding must see the newest own write while global RAM
-- still holds zero. This uses decoded MOV bytes, not a buffer-only fixture.
def forward : TSO.State :=
  { litmusInitial with workers := [⟨Examples.StoreBuffer.context 65536 65536, false, []⟩] }

def forwarded : TSO.State × List Observation :=
  checked (TSO.schedule forward [.issue 0, .issue 0]) (by rfl)

example : observe forwarded.1 = ([1], some 0, some 0, [(false, 1)]) := by rfl

-- Two different pending values distinguish newest-store forwarding from
-- reading the FIFO head. The memory remains zero until an explicit drain.
def newestBytes : List Byte := [0x89, 0x06, 0xb8, 2, 0, 0, 0, 0x89, 0x06, 0x8b, 0x07, 0xc3]

def newestInitial : TSO.State :=
  { forward with memory := { forward.memory with
      read := fun address => if 4194304 ≤ address.toNat ∧ address.toNat < 4194316 then
        newestBytes[address.toNat - 4194304]? else forward.memory.read address
      executable := fun address => decide (4194304 ≤ address.toNat ∧ address.toNat < 4194316) } }

def newestRun : TSO.State × List Observation :=
  checked (TSO.schedule newestInitial (List.replicate 4 (.issue 0))) (by rfl)

example : observe newestRun.1 = ([2], some 0, some 0, [(false, 2)]) := by rfl

def newestDrained : TSO.State × Observation := checked (TSO.drain newestRun.1 0) (by rfl)
example : (loadDWord newestDrained.1.memory 65536).toOption = some 1 ∧
    newestDrained.1.workers.map (fun worker =>
      (loadDWord (X86.StoreBuffer.view newestDrained.1.memory worker.buffer) 65536).toOption) =
        [some 2] := ⟨rfl, rfl⟩

-- The certified mutex routine encounters its release XCHG with two pending
-- payload stores. It must block, retain the lock, then publish FIFO stores
-- before releasing. Drains do not retire instructions or move RIP.
def mutexInitial : TSO.State := TSO.initial (MutexReplay.erase (Examples.MutexWorkers.admitted 0xfffffffe))

def mutexHeld : TSO.State × List Observation :=
  checked (TSO.schedule mutexInitial (List.replicate 10 (.issue 0))) (by rfl)

def mutexBlocked : TSO.State × Observation := checked (TSO.issue mutexHeld.1 0) (by rfl)

example : mutexBlocked.2 = .blocked 0 ∧
    (loadDWord mutexBlocked.1.memory 65536).toOption = some 1 ∧
    (loadDWord mutexBlocked.1.memory 131072).toOption = some 0xfffffffe ∧
    mutexBlocked.1.workers.map (fun worker => (worker.context.rip, worker.buffer.length)) =
      [(4194333, 2), (4194304, 0)] := by exact ⟨rfl, rfl, rfl, rfl⟩

def firstDrain : TSO.State × Observation := checked (TSO.drain mutexHeld.1 0) (by rfl)
def secondDrain : TSO.State × Observation := checked (TSO.drain firstDrain.1 0) (by rfl)

example : (TSO.issue firstDrain.1 0).toOption.map Prod.snd = some (.blocked 0) := by rfl

-- A peer's busy XCHG may execute while the holder still has pending stores.
-- Requiring every worker's buffer to be empty would over-restrict TSO.
def peerBusy : TSO.State × List Observation :=
  checked (TSO.schedule mutexHeld.1 [.issue 1, .issue 1]) (by rfl)

example : peerBusy.2 = [.retired 1 none, .retired 1 (some ⟨65536, 1, 1⟩)] ∧
    peerBusy.1.workers.map (fun worker => worker.buffer.length) = [2, 0] := ⟨rfl, rfl⟩

def release : TSO.State × Observation := checked (TSO.issue secondDrain.1 0) (by rfl)

example : (loadDWord firstDrain.1.memory 131072).toOption = some 0xffffffff ∧
    (loadDWord secondDrain.1.memory 131072).toOption = some 0 ∧
    release.2 = .retired 0 (some ⟨65536, 1, 0⟩) ∧
    (loadDWord release.1.memory 65536).toOption = some 0 := ⟨rfl, rfl, rfl, rfl⟩

-- Profile and architectural rejections remain explicit.
example : TSO.issue litmusInitial 2 = .error .missingThread := by rfl
example : TSO.drain litmusInitial 0 = .error .emptyBuffer := by rfl
example : TSO.issue returnedResult.1 0 = .error .alreadyReturned := by rfl

def unaligned : TSO.State :=
  { litmusInitial with workers := [⟨Examples.StoreBuffer.context 65537 65540, false, []⟩] }
example : TSO.issue unaligned 0 = .error (.unsupportedAlignment 65537) := by rfl

def executableDestination : TSO.State :=
  { litmusInitial with workers := [⟨Examples.StoreBuffer.context 4194304 65540, false, []⟩] }
example : TSO.issue executableDestination 0 = .error (.executableWrite 4194304) := by rfl

def deniedLastByte : TSO.State :=
  { litmusInitial with memory := { litmusInitial.memory with
      writable := fun address => if address = 65539 then false else litmusInitial.memory.writable address } }
example : TSO.issue deniedLastByte 0 = .error (.machine (.writeDenied 65536)) := by rfl

end EDSL.Tests.TSO

#audit_edsl
