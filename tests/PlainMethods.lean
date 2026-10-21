/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods
import tests.TSO64DrainClosure
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.PlainMethods
open X86 OS.TSO64 X86.VCGen.PlainMethods

/-!
Independent shape mutations and closed synthetic executions of the production
scheduler. The four windows are the frozen corpus bytes, but these tests do not
construct a machine-call adapter or certify the corresponding corpus functions.
The acquire/release names identify the intended interface; no source-order,
global C23, physical x86, native execution or Linux claim follows from these runs.
-/

inductive Variant where
  | gcc | clang

inductive Access where
  | load | store

def operation : Access → Operation
  | .load => .load (.base .rdi)
  | .store => .store (.base .rdi) .rsi

def padding : Variant → List Padding
  | .gcc => [.endbr64]
  | .clang => []

/-- Exact symbol windows from corpus/v1/{gcc,clang}/manifest.json. -/
def window : Variant → Access → List Byte
  | .gcc, .load => [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x07, 0xc3]
  | .gcc, .store => [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0x37, 0xc3]
  | .clang, .load => [0x48, 0x8b, 0x07, 0xc3]
  | .clang, .store => [0x48, 0x89, 0x37, 0xc3]

theorem frozen_windows_decode_as_the_selected_operation (variant : Variant) (access : Access) :
    check (window variant access) (operation access) (padding variant) = true := by
  cases variant <;> cases access <;> decide +kernel

-- Direction is part of the operation, even when address, width and RET match.
example : check (window .clang .store) (operation .load) [] = false := by decide +kernel
example : check (window .clang .load) (operation .store) [] = false := by decide +kernel

-- DWORD MOV cannot implement the qword interface; W=0 REX cannot repair it.
example : check [0x8b, 0x07, 0xc3] (operation .load) [] = false := by decide +kernel
example : check [0x89, 0x37, 0xc3] (operation .store) [] = false := by decide +kernel
example : check [0x40, 0x8b, 0x07, 0xc3] (operation .load) [] = false := by decide +kernel

-- The load destination is RAX, the store source is RSI, and the address is RDI.
example : check [0x48, 0x8b, 0x0f, 0xc3] (operation .load) [] = false := by decide +kernel
example : check [0x48, 0x89, 0x07, 0xc3] (operation .store) [] = false := by decide +kernel
example : check [0x48, 0x8b, 0x06, 0xc3] (operation .load) [] = false := by decide +kernel
example : check [0x48, 0x89, 0x32, 0xc3] (operation .store) [] = false := by decide +kernel

theorem gcc_padding_cannot_be_omitted (access : Access) :
    check (window .gcc access) (operation access) [] = false := by
  cases access <;> decide +kernel

theorem absent_padding_cannot_be_claimed (access : Access) :
    check (window .clang access) (operation access) [.endbr64] = false := by
  cases access <;> decide +kernel

theorem bytes_after_ret_are_not_part_of_the_checked_window (variant : Variant) (access : Access) :
    check (window variant access ++ [0x90]) (operation access) (padding variant) = false := by
  cases variant <;> cases access <;> decide +kernel

theorem a_missing_ret_is_rejected (variant : Variant) (access : Access) :
    check (window variant access).dropLast (operation access) (padding variant) = false := by
  cases variant <;> cases access <;> decide +kernel

-- RAX may be the address overwritten by the load or the store's own source.
example : check [0x48, 0x8b, 0x00, 0xc3] (.load (.base .rax)) [] = true := by decide +kernel
example : check [0x48, 0x89, 0x00, 0xc3] (.store (.base .rax) .rax) [] = true := by decide +kernel

-- Full64 SIB shapes retain REX.X/B/R and their encoded suffix length. These
-- admit a load with destination/base RAX and a store with index/source R12;
-- these assertions check shape admission, not dynamic alias execution.
example : check [0x4a, 0x8b, 0x04, 0x60, 0xc3]
    (.load (.indexed .rax .r12 1)) [] = true := by decide +kernel
example : check [0x4f, 0x89, 0x24, 0xa0, 0xc3]
    (.store (.indexed .r8 .r12 2) .r12) [] = true := by decide +kernel
example : check [0x4f, 0x89, 0x24, 0xa0, 0xc3]
    (.store (.indexed .r8 .r12 2) .rsp) [] = false := by decide +kernel
example : check [0x4a, 0x8b, 0x04, 0x60, 0xc3, 0x90]
    (.load (.indexed .rax .r12 1)) [] = false := by decide +kernel

-- The shape allows RSP as a store source despite the subsequent RET update.
example : check [0x48, 0x89, 0x27, 0xc3]
    (.store (.base .rdi) .rsp) [] = true := by decide +kernel

-- Padding is an instruction sequence, not an arbitrary skipped byte count.
example : check [0xf3, 0x0f, 0x1e, 0xfa, 0x90, 0x48, 0x8b, 0x07, 0xc3]
    (operation .load) [.endbr64, .nop .one] = true := by decide +kernel
example : check [0xf3, 0x0f, 0x1e, 0xfa, 0x90, 0x48, 0x8b, 0x07, 0xc3]
    (operation .load) [.endbr64] = false := by decide +kernel

abbrev PendingView := Nat × Word × StoreBuffer.Mixed.Value × Option Nat
abbrev DrainView := Nat × Nat × Word × StoreBuffer.Mixed.Value × Option Nat

-- Stage finite equality, as in TSO64DrainClosure, at the existing depth limit.
private instance : DecidableEq PendingView := inferInstance
private instance : DecidableEq DrainView := inferInstance
private instance : DecidableEq (List PendingView) := inferInstance
private instance : DecidableEq (List DrainView) := inferInstance
private instance : DecidableEq (List (Except Error Word)) := inferInstance
private instance : DecidableEq (List (Except Fault Word)) := inferInstance
private instance : DecidableEq (List (Option (Nat × Word))) := inferInstance

def pendingView : Pending → PendingView
  | .ordinary _ store => (0, store.address, store.value, none)
  | .managed reference value occurrence => (1, reference.cell.address, .qword value, some occurrence)

structure WorkerView where
  registers : List Word
  rip : Word
  flags : Word
  phase : Phase
  pending : List PendingView
  nextStore : Nat
  deriving DecidableEq

private instance : DecidableEq (List WorkerView) := inferInstance

/-- Observe all sixteen GPRs, not just the designated result and stack. -/
def workerView (worker : Worker) : WorkerView where
  registers := [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
    .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map worker.context.registers
  rip := worker.context.rip
  flags := worker.context.flags
  phase := worker.phase
  pending := worker.pending.map pendingView
  nextStore := worker.nextStore

structure AuthorityView where
  actor : Nat
  code : Lease
  caller : Lease
  callerAddress : Word
  grants : List OS.Ownership.Ticket
  atomics : List OS.Atomics64.HandleId64
  deriving DecidableEq

private instance : DecidableEq (List AuthorityView) := inferInstance

def authorityView (worker : Worker) : AuthorityView :=
  ⟨worker.resources.actor, worker.resources.code, worker.resources.caller,
    worker.resources.callerAddress, worker.resources.grants, worker.resources.atomics⟩

structure RetainedView where
  authority : AuthorityView
  pending : List Pending
  nextStore : Nat
  deriving DecidableEq

private instance : DecidableEq (List RetainedView) := inferInstance

/-- Retain the complete entries, including original tickets/handles/cells;
the literal payload summaries below additionally check what was enqueued. -/
def retainedView (worker : Worker) : RetainedView :=
  ⟨authorityView worker, worker.pending, worker.nextStore⟩

def retainedAcrossRet (before after : OS.TSO64.State) : Bool :=
  decide (before.workers.map retainedView = after.workers.map retainedView)

def authorityKept (before after : OS.TSO64.State) : Bool :=
  decide (before.workers.map authorityView = after.workers.map authorityView)

/-- Owned words, managed word, neighboring qword and both original callers. -/
def worldWords (state : OS.TSO64.State) : List (Except Error Word) :=
  [131072, 196608, 65536, 65544, 262144, 327680].map (loadQWord (published state.world))

def eventKind : Observation → Nat × Nat
  | .ordinary tid => (0, tid)
  | .returned tid => (1, tid)
  | .drained tid _ => (2, tid)
  | .blocked tid => (3, tid)
  | .rmw tid _ => (4, tid)

def loadPreamble : Variant → List Action
  | .gcc => [.issue 0 true]
  | .clang => []

def storePreamble : Variant → List Action
  | .gcc => [.issue 0 true, .issue 1 false]
  | .clang => []

/-- Reader: MOV [RDX],RSI; frozen load window. Peer: MOV [RDI],RSI; RET.
The owned reader store and peer managed store are actually issued, never placed
in the input queue. The load window begins at byte3, the peer at byte11/7. -/
def acquireStart : Variant → Except Fault OS.TSO64.State
  | .gcc => TSO64SharedCells.start 0x48fa1e0ff3328948 0x00c3378948c3078b
      0x1122334455667788 9 0xfedcba9876543210 0 11
  | .clang => TSO64SharedCells.start 0x48c3078b48328948 0x0000000000c33789
      0x1122334455667788 9 0xfedcba9876543210 0 7

structure AcquireRun where
  initial : OS.TSO64.State
  loaded : OS.TSO64.State × Observation
  readerReturned : OS.TSO64.State × Observation
  writerReturned : OS.TSO64.State × Observation
  peerPublished : OS.TSO64.State × Observation
  closed : OS.TSO64.State
  observations : List Observation

def acquireRun (variant : Variant) : Except Fault AcquireRun := do
  let initial ← acquireStart variant
  let queued ← schedule initial [.issue 0 false, .issue 1 true] .sharedCell
  let padded ← schedule queued.1 (loadPreamble variant) .sharedCell
  let loaded ← step padded.1 (.issue 0 false) .sharedCell
  let readerReturned ← step loaded.1 (.issue 0 true) .sharedCell
  let writerReturned ← step readerReturned.1 (.issue 1 false) .sharedCell
  let peerPublished ← step writerReturned.1 (.drain 1) .sharedCell
  let closed ← DrainClosure.drainAll peerPublished.1 .sharedCell
  pure ⟨initial, loaded, readerReturned, writerReturned, peerPublished, closed.1,
    queued.2 ++ padded.2 ++
      [loaded.2, readerReturned.2, writerReturned.2, peerPublished.2] ++ closed.2⟩

structure AcquireSummary where
  responses : List (Option (Nat × Word))
  beforePublication : List (Except Error Word)
  afterPublication : List (Except Error Word)
  afterClosure : List (Except Error Word)
  returnedWorkers : List WorkerView
  finalWorkers : List WorkerView
  exactRetFrame : Bool
  resourcesKept : Bool
  collectAtReturn : List (Except Fault Word)
  collectAfterClosure : List (Except Fault Word)
  closurePlan : List Action
  drains : List DrainView
  kinds : List (Nat × Nat)
  retired : List Nat
  deriving DecidableEq

def acquireSummary (run : AcquireRun) : AcquireSummary where
  responses := [Return.returnValue run.loaded, Return.returnValue run.readerReturned,
    Return.returnValue run.writerReturned, Return.returnValue run.peerPublished]
  beforePublication := worldWords run.writerReturned.1
  afterPublication := worldWords run.peerPublished.1
  afterClosure := worldWords run.closed
  returnedWorkers := run.writerReturned.1.workers.map workerView
  finalWorkers := run.closed.workers.map workerView
  exactRetFrame := retainedAcrossRet run.loaded.1 run.writerReturned.1
  resourcesKept := authorityKept run.initial run.closed
  collectAtReturn := [collect run.writerReturned.1 0, collect run.writerReturned.1 1]
  collectAfterClosure := [collect run.closed 0, collect run.closed 1]
  closurePlan := DrainClosure.actions run.peerPublished.1
  drains := run.observations.filterMap TSO64DrainClosure.observationSummary
  kinds := run.observations.map eventKind
  retired := run.observations.map Observation.retired

-- Literal register observations, independent of the executor and model's
-- Operation.registers/responded helpers. RAX differs from initial 5 and the
-- later publication; every other GPR is also checked after RET and drains.
def acquireReaderRegisters : List Word :=
  [0x1122334455667788, 131076, 131072, 0x8877665544332211,
    262152, 0x8877665544332211, 9, 65536,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211]

def firstStoreRegisters : List Word :=
  [5, 131076, 131072, 0x8877665544332211,
    262152, 0x8877665544332211, 0xfedcba9876543210, 65536,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211]

def acquireWriterRegisters : List Word :=
  [5, 196612, 196608, 0x8877665544332211,
    327688, 0x8877665544332211, 0xfedcba9876543210, 65536,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211]

def acquireExpected (variant : Variant) : AcquireSummary where
  responses := [none, some (0, 0x1122334455667788), some (1, 5), none]
  beforePublication := [.ok 0, .ok 0, .ok 0x1122334455667788,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  afterPublication := [.ok 0, .ok 0, .ok 0xfedcba9876543210,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  afterClosure := [.ok 9, .ok 0, .ok 0xfedcba9876543210,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  returnedWorkers := [
    ⟨acquireReaderRegisters, 0x7000, 0x200202, .returned,
      [(0, 131072, .qword 9, none)], 1⟩,
    ⟨acquireWriterRegisters, 0x8000, 0x200202, .returned,
      [(1, 65536, .qword 0xfedcba9876543210, some 0)], 1⟩]
  finalWorkers := [
    ⟨acquireReaderRegisters, 0x7000, 0x200202, .returned, [], 1⟩,
    ⟨acquireWriterRegisters, 0x8000, 0x200202, .returned, [], 1⟩]
  exactRetFrame := true
  resourcesKept := true
  collectAtReturn := [.error .resource, .error .resource]
  collectAfterClosure := [.ok 0x1122334455667788, .ok 5]
  closurePlan := [.drain 0]
  drains := [(1, 1, 65536, .qword 0xfedcba9876543210, some 0),
    (0, 0, 131072, .qword 9, none)]
  kinds := match variant with
    | .gcc => [(0, 0), (0, 1), (0, 0), (0, 0), (1, 0), (1, 1), (2, 1), (2, 0)]
    | .clang => [(0, 0), (0, 1), (0, 0), (1, 0), (1, 1), (2, 1), (2, 0)]
  retired := match variant with
    | .gcc => [1, 1, 1, 1, 1, 1, 0, 0]
    | .clang => [1, 1, 1, 1, 1, 0, 0]

/-- The nonempty disjoint own FIFO neither supplies a managed value nor hides
current RAM. The RET response keeps the actual loaded full64 word even after
the peer publishes a different word; own ordinary publication occurs last. -/
theorem acquire_response_is_the_loaded_word_with_the_exact_return_and_drain_frames
    (variant : Variant) :
    (acquireRun variant).map acquireSummary = .ok (acquireExpected variant) := by
  cases variant <;> decide +kernel

/-- MOV [RDX],RAX; frozen store window. Both contexts execute the prelude.
The peer's ordinary head drains before its method begins: both counters are 1,
while only worker 0 still has an ordinary head. Queue length cannot supply IDs. -/
def releaseStart : Variant → Except Fault OS.TSO64.State
  | .gcc => TSO64SharedCells.start 0x48fa1e0ff3028948 0x0000000000c33789
      0x1122334455667788 0xfedcba9876543210 0x8000000100000009 0 0
  | .clang => TSO64SharedCells.start 0x00c3378948028948 0
      0x1122334455667788 0xfedcba9876543210 0x8000000100000009 0 0

structure ReleaseRun where
  initial : OS.TSO64.State
  accessed : OS.TSO64.State
  returned : OS.TSO64.State
  ordinaryPublished : OS.TSO64.State
  managedPublished : OS.TSO64.State
  closed : OS.TSO64.State
  responses : List (Option (Nat × Word))
  observations : List Observation

def releaseRun (variant : Variant) : Except Fault ReleaseRun := do
  let initial ← releaseStart variant
  let queued ← schedule initial [.issue 0 false, .issue 1 true] .sharedCell
  let boundary ← step queued.1 (.drain 1) .sharedCell
  let padded ← schedule boundary.1 (storePreamble variant) .sharedCell
  let storedA ← step padded.1 (.issue 0 false) .sharedCell
  let storedB ← step storedA.1 (.issue 1 true) .sharedCell
  let returnedA ← step storedB.1 (.issue 0 true) .sharedCell
  let returnedB ← step returnedA.1 (.issue 1 false) .sharedCell
  let ordinaryPublished ← step returnedB.1 (.drain 0) .sharedCell
  let managedPublished ← step ordinaryPublished.1 (.drain 0) .sharedCell
  let closed ← DrainClosure.drainAll managedPublished.1 .sharedCell
  pure ⟨initial, storedB.1, returnedB.1, ordinaryPublished.1, managedPublished.1, closed.1,
    [Return.returnValue storedA, Return.returnValue storedB, Return.returnValue returnedA,
      Return.returnValue returnedB, Return.returnValue ordinaryPublished,
      Return.returnValue managedPublished],
    queued.2 ++ [boundary.2] ++ padded.2 ++ [storedA.2, storedB.2, returnedA.2, returnedB.2,
      ordinaryPublished.2, managedPublished.2] ++ closed.2⟩

structure ReleaseSummary where
  responses : List (Option (Nat × Word))
  beforePublication : List (Except Error Word)
  afterOrdinaryHead : List (Except Error Word)
  afterManagedHead : List (Except Error Word)
  afterClosure : List (Except Error Word)
  returnedWorkers : List WorkerView
  finalWorkers : List WorkerView
  exactRetFrame : Bool
  resourcesKept : Bool
  collectAtReturn : List (Except Fault Word)
  collectAfterClosure : List (Except Fault Word)
  closurePlan : List Action
  drains : List DrainView
  kinds : List (Nat × Nat)
  retired : List Nat
  deriving DecidableEq

def releaseSummary (run : ReleaseRun) : ReleaseSummary where
  responses := run.responses
  beforePublication := worldWords run.returned
  afterOrdinaryHead := worldWords run.ordinaryPublished
  afterManagedHead := worldWords run.managedPublished
  afterClosure := worldWords run.closed
  returnedWorkers := run.returned.workers.map workerView
  finalWorkers := run.closed.workers.map workerView
  exactRetFrame := retainedAcrossRet run.accessed run.returned
  resourcesKept := authorityKept run.initial run.closed
  collectAtReturn := [collect run.returned 0, collect run.returned 1]
  collectAfterClosure := [collect run.closed 0, collect run.closed 1]
  closurePlan := DrainClosure.actions run.returned
  drains := run.observations.filterMap TSO64DrainClosure.observationSummary
  kinds := run.observations.map eventKind
  retired := run.observations.map Observation.retired

def secondStoreRegisters : List Word :=
  [5, 196612, 196608, 0x8877665544332211,
    327688, 0x8877665544332211, 0x8000000100000009, 65536,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211]

def releaseExpected (variant : Variant) : ReleaseSummary where
  responses := [none, none, some (0, 5), some (1, 5), none, none]
  beforePublication := [.ok 0, .ok 5, .ok 0x1122334455667788,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  afterOrdinaryHead := [.ok 5, .ok 5, .ok 0x1122334455667788,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  afterManagedHead := [.ok 5, .ok 5, .ok 0xfedcba9876543210,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  afterClosure := [.ok 5, .ok 5, .ok 0x8000000100000009,
    .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  returnedWorkers := [
    ⟨firstStoreRegisters, 0x7000, 0x200202, .returned,
      [(0, 131072, .qword 5, none), (1, 65536, .qword 0xfedcba9876543210, some 1)], 2⟩,
    ⟨secondStoreRegisters, 0x8000, 0x200202, .returned,
      [(1, 65536, .qword 0x8000000100000009, some 1)], 2⟩]
  finalWorkers := [
    ⟨firstStoreRegisters, 0x7000, 0x200202, .returned, [], 2⟩,
    ⟨secondStoreRegisters, 0x8000, 0x200202, .returned, [], 2⟩]
  exactRetFrame := true
  resourcesKept := true
  collectAtReturn := [.error .resource, .error .resource]
  collectAfterClosure := [.ok 5, .ok 5]
  closurePlan := [.drain 0, .drain 0, .drain 1]
  drains := [(1, 0, 196608, .qword 5, none),
    (0, 0, 131072, .qword 5, none),
    (0, 1, 65536, .qword 0xfedcba9876543210, some 1),
    (1, 1, 65536, .qword 0x8000000100000009, some 1)]
  kinds := match variant with
    | .gcc => [(0, 0), (0, 1), (2, 1), (0, 0), (0, 1), (0, 0), (0, 1),
        (1, 0), (1, 1), (2, 0), (2, 0), (2, 1)]
    | .clang => [(0, 0), (0, 1), (2, 1), (0, 0), (0, 1), (1, 0), (1, 1),
        (2, 0), (2, 0), (2, 1)]
  retired := match variant with
    | .gcc => [1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0]
    | .clang => [1, 1, 0, 1, 1, 1, 1, 0, 0, 0]

/-- Both stores return before either managed publication, preserving machine
RAX=5 (the logical store reply is unit). Worker 0's mixed FIFO publishes its
ordinary head first. The peer's counter survives its earlier ordinary drain;
both managed occurrences are 1 despite different pending lengths. RET/drains
retain counters and flags and RET pops exactly one original caller slot. -/
theorem release_returns_before_publication_and_preserves_exact_mixed_fifos
    (variant : Variant) :
    (releaseRun variant).map releaseSummary = .ok (releaseExpected variant) := by
  cases variant <;> decide +kernel

structure StackSourceSummary where
  responses : List (Option (Nat × Word))
  returnedWorker : Option WorkerView
  beforePublication : List (Except Error Word)
  afterPublication : List (Except Error Word)
  exactRetFrame : Bool
  resourcesKept : Bool
  drains : List DrainView
  retired : List Nat
  deriving DecidableEq

/-- Synthetic MOV [RDI],RSP; RET, using the same actual code/caller loans and
shared authority. No requested poststate or buffered entry is an input. -/
def stackSource : Except Fault StackSourceSummary := do
  let initial ← TSO64SharedCells.start 0x00000000c3278948 0
    0x1122334455667788 0xfedcba9876543210 0 0 0
  let stored ← step initial (.issue 0 false) .sharedCell
  let returned ← step stored.1 (.issue 0 true) .sharedCell
  let drained ← step returned.1 (.drain 0) .sharedCell
  pure {
    responses := [Return.returnValue stored, Return.returnValue returned, Return.returnValue drained]
    returnedWorker := returned.1.workers[0]?.map workerView
    beforePublication := worldWords returned.1
    afterPublication := worldWords drained.1
    exactRetFrame := retainedAcrossRet stored.1 returned.1
    resourcesKept := authorityKept initial drained.1
    drains := [stored.2, returned.2, drained.2].filterMap TSO64DrainClosure.observationSummary
    retired := [stored.2, returned.2, drained.2].map Observation.retired
  }

/-- Publication uses the pre-RET source 262144, not the popped RSP 262152.
RAX and the original protected caller word retain their separate roles. -/
theorem rsp_store_captures_the_source_before_ret_pops_the_caller : stackSource = .ok {
    responses := [none, some (0, 5), none]
    returnedWorker := some ⟨firstStoreRegisters, 0x7000, 0x200202, .returned,
      [(1, 65536, .qword 262144, some 0)], 1⟩
    beforePublication := [.ok 0, .ok 0, .ok 0x1122334455667788,
      .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
    afterPublication := [.ok 0, .ok 0, .ok 262144,
      .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
    exactRetFrame := true
    resourcesKept := true
    drains := [(0, 1, 65536, .qword 262144, some 0)]
    retired := [1, 1, 0]
  } := by decide +kernel

end EDSL.Tests.PlainMethods

#print axioms EDSL.X86.VCGen.PlainMethods.check_sound
#print axioms EDSL.X86.VCGen.ManagedAccess.issue_loadMem64
#print axioms EDSL.X86.VCGen.ManagedAccess.issue_storeMem64
#print axioms EDSL.X86.VCGen.PlainMethods.complete
#print axioms EDSL.X86.VCGen.PlainMethods.all_completed
#print axioms EDSL.X86.VCGen.PlainMethods.enough_own_issues
#print axioms EDSL.X86.VCGen.ManagedReturn.step_ret
#print axioms EDSL.X86.VCGen.ManagedReturn.response
#print axioms EDSL.Tests.PlainMethods.frozen_windows_decode_as_the_selected_operation
#print axioms EDSL.Tests.PlainMethods.acquire_response_is_the_loaded_word_with_the_exact_return_and_drain_frames
#print axioms EDSL.Tests.PlainMethods.release_returns_before_publication_and_preserves_exact_mixed_fifos
#print axioms EDSL.Tests.PlainMethods.rsp_store_captures_the_source_before_ret_pops_the_caller
#audit_edsl
