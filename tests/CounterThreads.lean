/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CounterCertificate
import EDSL.Audit

namespace EDSL.Tests.CounterWorkers
open X86 OS.AddressSpace
abbrev TState := OS.CounterThreads.State
abbrev Fault := OS.CounterThreads.Fault
abbrev Start := OS.CounterThreads.Start

def seed (old : BitVec 32) : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xe3, readExecute⟩ | 4097 => some ⟨0x0b, readExecute⟩
    | 4098 | 4109 => some ⟨0xb8, readExecute⟩ | 4099 => some ⟨1, readExecute⟩
    | 4100 | 4101 | 4102 | 4110 | 4111 | 4112 | 4113 => some ⟨0, readExecute⟩
    | 4103 => some ⟨0xf0, readExecute⟩ | 4104 => some ⟨0x0f, readExecute⟩
    | 4105 => some ⟨0xc1, readExecute⟩ | 4106 => some ⟨0x07, readExecute⟩
    | 4107 => some ⟨0xe2, readExecute⟩ | 4108 => some ⟨0xf5, readExecute⟩
    | 4114 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩ | 32785 => some ⟨0x30, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 |
      32784 | 32786 | 32787 | 32788 | 32789 | 32790 | 32791 => some ⟨0, readOnly⟩
    | 65536 => some ⟨old.extractLsb' 0 8, readWrite⟩ | 65537 => some ⟨old.extractLsb' 8 8, readWrite⟩
    | 65538 => some ⟨old.extractLsb' 16 8, readWrite⟩ | 65539 => some ⟨old.extractLsb' 24 8, readWrite⟩
    | 65540 => some ⟨0xd8, readWrite⟩ | 65541 => some ⟨0xc7, readWrite⟩
    | 65542 => some ⟨0xb6, readWrite⟩ | 65543 => some ⟨0xa5, readWrite⟩
    | _ => none

def entry (stack count flags : Word) : OS.CounterThreads.Context where
  registers register := if register = .rdi then 65536 else if register = .rsp then stack
    else if register = .rcx then count else if register = .rsi then 0xfeedface89abcdef else 0xdeadbeefcafebabe
  rip := 4096
  flags := flags

def withTicket (state : TState) (operation : OS.Ownership.Mutation) : Except Fault (TState × OS.Ownership.Ticket) := do
  let (after, result) ← OS.CounterThreads.mutate state operation
  let some ticket := result | throw .missingThread
  pure (after, ticket)

def setupIn (space : Space) (a b : Word) : Except Fault (TState × Start × Start) := do
  let initial := OS.CounterThreads.empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty space)))
  let (data, dataTicket) ← withTicket initial (.adopt 0 ⟨65536, 8⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4096, 19⟩)
  let (stackA, aTicket) ← withTicket code (.adopt 0 ⟨32768, 8⟩)
  let (both, bTicket) ← withTicket stackA (.adopt 0 ⟨32784, 8⟩)
  pure (both, ⟨entry 32768 a 0x8d7, dataTicket, codeTicket, aTicket⟩,
    ⟨entry 32784 b 0x246, dataTicket, codeTicket, bTicket⟩)

def failedWith {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with | .error actual => decide (actual = expected) | .ok _ => false

def completedContext (state : TState) (identifier : Nat) : Except Fault (Word × Word × Word × Word × Word) := do
  let some worker := state.workers identifier | throw .missingThread
  if worker.phase ≠ .completed then throw .notCompleted
  pure (worker.context.registers .rax, worker.context.registers .rcx, worker.context.registers .rsp,
    worker.context.rip, worker.context.flags)

structure Observation where
  counter : Option (BitVec 32)
  guard : Option (BitVec 32)
  returns : List Word
  contexts : List (Word × Word × Word × Word × Word)
  events : List (Nat × AtomicEvent)
  pinnedAfterFirstJoin : Bool
  reclaimed : Bool
  deriving DecidableEq, Repr

def twoWorkers (selections : List Nat) : Except Fault Observation := do
  let (initial, a, b) ← setupIn (seed 0xffffffff) 1 1
  let (one, aId) ← OS.CounterThreads.spawn initial 0 a
  let (both, bId) ← OS.CounterThreads.spawn one 0 b
  let (done, events) ← OS.CounterThreads.schedule both selections
  let aContext ← completedContext done aId
  let bContext ← completedContext done bId
  let (first, aValue) ← OS.CounterThreads.join done 0 aId
  let pinned := failedWith (OS.CounterThreads.mutate first (.store 0 a.dataTicket 65540 0)) (.atomic .reserved)
  let (joined, bValue) ← OS.CounterThreads.join first 0 bId
  let counter := (loadDWord (toMemory joined.shared.shared.resources.space) 65536).toOption
  let guard := (loadDWord (toMemory joined.shared.shared.resources.space) 65540).toOption
  let (released, _) ← OS.CounterThreads.mutate joined (.release 0 a.dataTicket)
  let (codeFree, _) ← OS.CounterThreads.mutate released (.protect 0 a.codeTicket readOnly)
  let (stackFree, _) ← OS.CounterThreads.mutate codeFree (.release 0 a.stackTicket)
  let (allFree, _) ← OS.CounterThreads.mutate stackFree (.release 0 b.stackTicket)
  pure ⟨counter, guard, [aValue, bValue], [aContext, bContext], events, pinned,
    decide (allFree.shared.shared.resources.space.cells 65536 = none)⟩

def aFirst : Observation := ⟨some 1, some 0xa5b6c7d8, [0, 0],
  [(0, 0, 32776, 8192, 0x57), (0, 0, 32792, 12288, 0x202)],
  [(0, ⟨65536, 0xffffffff, 0⟩), (1, ⟨65536, 0, 1⟩)], true, true⟩
def bFirst : Observation := ⟨some 1, some 0xa5b6c7d8, [0, 0],
  [(0, 0, 32776, 8192, 2), (0, 0, 32792, 12288, 0x257)],
  [(1, ⟨65536, 0xffffffff, 0⟩), (0, ⟨65536, 0, 1⟩)], true, true⟩

-- Explicit structural recursors keep the finite schedule enumeration reducible
-- by the kernel rather than relying on well-founded recursion elaboration.
def interleavings : Nat → Nat → List (List Nat) :=
  Nat.rec (fun b => [List.replicate b 1]) fun a previous =>
    Nat.rec [List.replicate (a + 1) 0] fun b below =>
      ((previous (b + 1)).map (0 :: ·)) ++ (below.map (1 :: ·))

-- The source routine's third selected instruction is its RMW. Expected order
-- comes from the supplied schedule, independently of the emitted model trace.
def thirdSelection (identifier : Nat) (selections : List Nat) : Nat :=
  (((selections.zipIdx.filter fun pair => decide (pair.1 = identifier))[2]?).map (·.2)).getD selections.length

-- Fourteen batches cover all 924 schedules while bounding each kernel
-- reduction's working memory on the CI runner.
def checkInterleavings (offset : Nat) : Bool := ((interleavings 6 6).drop offset |>.take 66).all fun selections =>
  let expected := if thirdSelection 0 selections < thirdSelection 1 selections then aFirst else bFirst
  decide ((twoWorkers selections).toOption = some expected)

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
example : (interleavings 6 6).length = 924 := by decide +kernel
example : checkInterleavings 0 = true := by decide +kernel
example : checkInterleavings 66 = true := by decide +kernel
example : checkInterleavings 132 = true := by decide +kernel
example : checkInterleavings 198 = true := by decide +kernel
example : checkInterleavings 264 = true := by decide +kernel
example : checkInterleavings 330 = true := by decide +kernel
example : checkInterleavings 396 = true := by decide +kernel
example : checkInterleavings 462 = true := by decide +kernel
example : checkInterleavings 528 = true := by decide +kernel
example : checkInterleavings 594 = true := by decide +kernel
example : checkInterleavings 660 = true := by decide +kernel
example : checkInterleavings 726 = true := by decide +kernel
example : checkInterleavings 792 = true := by decide +kernel
example : checkInterleavings 858 = true := by decide +kernel

def runCounts (aCount bCount : Word) : Except Fault (Option (BitVec 32) × Nat × List Word) := do
  let (initial, a, b) ← setupIn (seed 0xfffffffe) aCount bCount
  let (one, _) ← OS.CounterThreads.spawn initial 0 a
  let (both, _) ← OS.CounterThreads.spawn one 0 b
  let (done, events) ← OS.CounterThreads.finishWorkers both (OS.CounterThreads.liveIds both)
  let (joined, values) ← OS.CounterThreads.collect done 0 (OS.CounterThreads.liveIds done)
  pure ((loadDWord (toMemory joined.shared.shared.resources.space) 65536).toOption, events.length, values)

example : runCounts 0 0 = .ok (some 0xfffffffe, 0, [0, 0]) := by rfl
example : runCounts 0 2 = .ok (some 0, 2, [0, 0]) := by rfl
example : runCounts 2 3 = .ok (some 3, 5, [0, 0]) := by rfl

-- Join must reject every incomplete phase, including after the increment but
-- before the actual backedge, final MOV and RET. Reusing the resources creates
-- a fresh ID; the joined ID must never select the new worker.
def lifecycle : Except Fault (List Bool × List Word × Nat × Option (BitVec 32)) := do
  let (initial, a, _) ← setupIn (seed 0xfffffffe) 1 0
  let (started, identifier) ← OS.CounterThreads.spawn initial 0 a
  let early := (List.range 6).map fun length =>
    match OS.CounterThreads.schedule started (List.replicate length identifier) with
    | .error _ => false
    | .ok (paused, _) => failedWith (OS.CounterThreads.join paused 0 identifier) .notCompleted
  let (done, _) ← OS.CounterThreads.schedule started (List.replicate 6 identifier)
  let extra := failedWith (OS.CounterThreads.dispatch done identifier) .alreadyCompleted
  let parent := failedWith (OS.CounterThreads.join done 9 identifier) .wrongParent
  let (joined, value) ← OS.CounterThreads.join done 0 identifier
  let staleJoin := failedWith (OS.CounterThreads.join joined 0 identifier) .missingThread
  let (again, fresh) ← OS.CounterThreads.spawn joined 0 a
  let staleDispatch := failedWith (OS.CounterThreads.dispatch again identifier) .missingThread
  let (finished, _) ← OS.CounterThreads.schedule again (List.replicate 6 fresh)
  let (collected, nextValue) ← OS.CounterThreads.join finished 0 fresh
  pure (early ++ [extra, parent, staleJoin, staleDispatch], [value, nextValue], fresh,
    (loadDWord (toMemory collected.shared.shared.resources.space) 65536).toOption)

example : lifecycle = .ok (List.replicate 10 true, [0, 0], 1, some 0) := by rfl

-- Checked admission errors, including failure after acquiring code/stack loans,
-- must not admit invalid data authority. While a worker is paused immediately
-- before XADD, conflicting mutations reject and unrelated memory remains usable.
def failuresAndInterference : Except Fault (List Bool × Word × Option (BitVec 32) × Option (BitVec 32)) := do
  let (initial, a, _) ← setupIn (seed 0xffffffff) 1 0
  let invalidData := { a with dataTicket := ⟨99, 0⟩ }
  let invalidStack := { a with stackTicket := ⟨99, 0⟩ }
  let checks := [
    failedWith (OS.CounterThreads.spawn initial 9 a) .wrongParent,
    failedWith (OS.CounterThreads.spawn initial 0 a false) .creationFailed,
    failedWith (OS.CounterThreads.spawn initial 0 invalidStack) (.atomic (.authority (.ownership .missingAllocation))),
    failedWith (OS.CounterThreads.spawn initial 0 invalidData) (.atomic (.authority (.ownership .missingAllocation)))]
  let (started, identifier) ← OS.CounterThreads.spawn initial 0 a
  let (prepared, _) ← OS.CounterThreads.schedule started [identifier, identifier]
  let blocked := [
    failedWith (OS.CounterThreads.mutate prepared (.protect 0 a.codeTicket readOnly)) (.atomic (.authority .borrowed)),
    failedWith (OS.CounterThreads.mutate prepared (.release 0 a.stackTicket)) (.atomic (.authority .borrowed)),
    failedWith (OS.CounterThreads.mutate prepared (.store 0 a.dataTicket 65540 0)) (.atomic .reserved),
    failedWith (OS.CounterThreads.mutate prepared (.release 0 a.dataTicket)) (.atomic .reserved),
    failedWith (OS.CounterThreads.mutate prepared (.transfer 0 a.dataTicket 9)) (.atomic .reserved)]
  let (other, ticket) ← withTicket prepared (.allocate 0 ⟨131072, 4⟩ readWrite)
  let (changed, _) ← OS.CounterThreads.mutate other (.store 0 ticket 131072 0x76543210)
  let (done, _) ← OS.CounterThreads.schedule changed (List.replicate 4 identifier)
  let (joined, value) ← OS.CounterThreads.join done 0 identifier
  pure (checks ++ blocked, value,
    (loadDWord (toMemory joined.shared.shared.resources.space) 65536).toOption,
    (loadDWord (toMemory joined.shared.shared.resources.space) 131072).toOption)

example : failuresAndInterference = .ok (List.replicate 9 true, 0, some 0, some 0x76543210) := by rfl

def changedCell (address : Word) (cell : Option Cell) : Space :=
  ⟨fun query => if query = address then cell else (seed 0x11223344).cells query⟩

def rejectedStart (space : Space) (expected : Fault) : Except Fault Bool := do
  let (initial, a, _) ← setupIn space 1 0
  pure (failedWith (OS.CounterThreads.spawn initial 0 a) expected)

example : rejectedStart (changedCell 4108 (some ⟨0xf6, readExecute⟩)) .unsupportedCode = .ok true := by rfl
example : failedWith (rejectedStart (changedCell 4114 none) .unsupportedCode)
    (.atomic (.authority (.ownership (.addressSpace .notMapped)))) = true := by rfl
example : rejectedStart (changedCell 4114 (some ⟨0xc3, readOnly⟩)) .unsupportedCode = .ok true := by rfl
example : rejectedStart (changedCell 65539 (some ⟨0x11, readOnly⟩))
    (.atomic (.machine (.writeDenied 65536))) = .ok true := by rfl

end EDSL.Tests.CounterWorkers

#audit_edsl
