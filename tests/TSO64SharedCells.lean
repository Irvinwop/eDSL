/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.OS.TSO64
import EDSL.Audit

namespace EDSL.Tests.TSO64SharedCells
open X86 OS.TSO64

abbrev Fault := OS.TSO64.Fault

/-- Two actual contexts start at selected instruction boundaries in one checked
code loan. Both handles precede every tested instruction and publication. -/
def start (first second old deltaA deltaB : Word) (offsetA offsetB : Nat) :
    Except Fault OS.TSO64.State := do
  let ready ← (TSO64.fixture first second old).mapError Fault.os
  let a := { TSO64.context 262144 131072 deltaA 5 with rip := 393216 + BitVec.ofNat 64 offsetA }
  let b := { TSO64.context 327680 196608 deltaB 5 with rip := 393216 + BitVec.ofNat 64 offsetB }
  let one ← attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  attach one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB]

def metadata (state : OS.TSO64.State) (tid : Nat) :
    Option (Word × Word × Phase × List Nat × Nat × Nat) :=
  state.workers[tid]?.map fun worker =>
    (worker.context.registers .rax, worker.context.rip, worker.phase,
      Queue.occurrences worker.pending, worker.pending.length, worker.nextStore)

def managedPublications (observations : List Observation) : List (Nat × Nat) :=
  observations.filterMap fun observation => match observation with
    | .drained tid (.managed _ _ occurrence) => some (tid, occurrence)
    | _ => none

/-- Bytes: MOV [RDI],RSI; MOV [RDI],RSI; MOV RAX,[RDI]; MOV RAX,[RDI]; RET.
The reader starts at the first load. No expected state is supplied to execution. -/
def equalStores : Except Fault
    (Except Error Word × Option (Word × Word × Phase × List Nat × Nat × Nat) ×
      Option (Word × Word × Phase × List Nat × Nat × Nat) × Except Fault Word ×
      Except Error Word × Option (Word × Word × Phase × List Nat × Nat × Nat) ×
      Option (Word × Word × Phase × List Nat × Nat × Nat) × Except Fault Word ×
      List (Nat × Nat) × List Nat × Except Error Word × Except Error Word) := do
  let initial ← start 0x8b48378948378948 0x000000c3078b4807
    0x0000000100000000 0xfedcba9876543210 0 0 6
  let before ← schedule initial
    [.issue 0 false, .issue 0 true, .issue 1 false,
      .issue 0 true, .issue 0 false, .issue 0 false] .sharedCell
  let after ← schedule before.1 [.drain 0, .issue 1 true, .drain 0] .sharedCell
  return (loadQWord (published before.1.world) 65536, metadata before.1 0, metadata before.1 1,
    collect before.1 0, loadQWord (published after.1.world) 65536,
    metadata after.1 0, metadata after.1 1, collect after.1 0,
    managedPublications after.2, (before.2 ++ after.2).map Observation.retired,
    loadQWord (published after.1.world) 65544, loadQWord (published after.1.world) 262144)

/-- Real equal-value MOV issues allocate distinct IDs; own loads forward while
the peer sees old RAM. RET leaves both stores pending. FIFO publication retains
each ID, and the later peer load sees current RAM without resetting the counter. -/
theorem decoded_equal_stores_and_return : equalStores = .ok
    (.ok 0x0000000100000000,
      some (0xfedcba9876543210, 0x7000, .returned, [0, 1], 2, 2),
      some (0x0000000100000000, 393225, .running, [], 0, 0), .error .resource,
      .ok 0xfedcba9876543210,
      some (0xfedcba9876543210, 0x7000, .returned, [], 0, 2),
      some (0xfedcba9876543210, 393228, .running, [], 0, 0), .ok 0xfedcba9876543210,
      [(0, 0), (0, 1)], [1, 1, 1, 1, 1, 1, 0, 1, 0],
      .ok 0xabcdef0123456789, .ok 0x7000) := by rfl

def defaultDenial : Except Fault OS.TSO64.Observation := do
  let initial ← start 0x8b48378948378948 0x000000c3078b4807
    0x0000000100000000 0xfedcba9876543210 0 0 6
  return (← step initial (.issue 0 false)).2

/-- The identical real managed store remains denied under the default policy.
Selecting shared mode is explicit at execution; decoding alone grants nothing. -/
theorem default_managed_mov_is_denied : defaultDenial = .error .noGrant := by rfl

/-- MOV [RDX],RSI; MOV [RDI],RSI; LOCK XADD [RDI],RAX; RET. -/
def mixedLock : Except Fault
    (List (Nat × Word × Word × Word) × List Nat × List (Nat × Nat) ×
      Except Error Word × Except Error Word × Except Error Word ×
      Option (Word × Word × Phase × List Nat × Nat × Nat) ×
      Option (Word × Word × Phase × List Nat × Nat × Nat) × Except Fault Word) := do
  let initial ← start 0x48f0378948328948 0x00000000c307c10f 11 7 9 0 0
  let result ← schedule initial
    [.issue 0 false, .issue 0 false, .issue 1 false, .issue 0 false,
      .drain 0, .issue 0 true, .drain 0, .issue 0 false, .issue 0 false] .sharedCell
  return (TSO64.events result.2, result.2.map Observation.retired, managedPublications result.2,
    loadQWord (published result.1.world) 65536,
    loadQWord (published result.1.world) 131072,
    loadQWord (published result.1.world) 196608,
    metadata result.1 0, metadata result.1 1, collect result.1 0)

/-- LOCK blocks on either own tag and succeeds with a peer's store still queued.
Only successful MOV stores consume IDs; drains, blocked attempts, RMW and RET
do not. The RMW uses the word actually published by the managed FIFO head. -/
theorem mixed_fifo_blocks_only_issuing_worker : mixedLock = .ok
    ([(0, 5, 7, 12)], [1, 1, 1, 0, 0, 0, 0, 1, 1], [(0, 1)],
      .ok 12, .ok 7, .ok 0,
      some (7, 0x7000, .returned, [], 0, 2),
      some (5, 393219, .running, [], 1, 1), .ok 7) := by rfl

/-- MOV [RDX],RSI; MOV RAX,[RDI]; MOV RAX,[RDI]; MOV [RDI],RSI; RET.
The writer starts at the managed store; the reader retains a disjoint own store. -/
def currentRAM : Except Fault
    (Option (Word × Word × Phase × List Nat × Nat × Nat) ×
      Option (Word × Word × Phase × List Nat × Nat × Nat) ×
      Except Error Word × Except Error Word × Except Error Word × List Nat) := do
  let initial ← start 0x8b48078b48328948 0x000000c337894807
    0x1122334455667788 0xfedcba9876543210 9 9 0
  let before ← schedule initial [.issue 0 false, .issue 1 false, .issue 1 false] .sharedCell
  let after ← schedule before.1 [.drain 0, .issue 1 false] .sharedCell
  let some reader := after.1.workers[1]? | throw .missingWorker
  return (metadata before.1 1, metadata after.1 1,
    loadQWord (published after.1.world) 65536,
    loadQWord (published after.1.world) 196608,
    loadQWord (localCPU after.1 reader).memory 196608,
    (before.2 ++ after.2).map Observation.retired)

/-- A managed load falls back to CURRENT published memory through a nonempty
disjoint own FIFO. It retains the own ordinary overlay without publishing it. -/
theorem peer_publication_updates_buffered_reader : currentRAM = .ok
    (some (0x1122334455667788, 393222, .running, [], 1, 1),
      some (0xfedcba9876543210, 393225, .running, [], 1, 1),
      .ok 0xfedcba9876543210, .ok 0, .ok 9, [1, 1, 1, 0, 1]) := by rfl

end EDSL.Tests.TSO64SharedCells

#audit_edsl
