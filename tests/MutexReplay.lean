/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Model
import EDSL.Audit

namespace EDSL.Tests.MutexReplay
open X86 OS.AddressSpace
abbrev RState := OS.MutexReplay.State
abbrev Fault := OS.MutexReplay.Fault
abbrev Start := OS.MutexReplay.Start

-- This owned machine fixture is assembled independently in mutex-worker.S.
-- Expected results below use the public +2 request contract and actual byte
-- reads, rather than deriving an expectation from model-generated events.
def fixture : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x87, 0x07, 0x83, 0xf8, 0, 0x75, 0xf4,
   0x8b, 0x06, 0x8d, 0x40, 1, 0x89, 0x06, 0x8d, 0x40, 1, 0x89, 0x06,
   0xb8, 0, 0, 0, 0, 0x87, 0x07, 0xb8, 0, 0, 0, 0, 0xc3]

def seed (old : BitVec 32) : Space where
  cells address :=
    if 4194304 ≤ address.toNat ∧ address.toNat < 4194341 then
      (fixture[address.toNat - 4194304]?).map fun byte => ⟨byte, readExecute⟩
    else match address.toNat with
      | 32769 => some ⟨0x20, readOnly⟩
      | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readOnly⟩
      | 65536 | 65537 | 65538 | 65539 => some ⟨0, readWrite⟩
      | 131072 => some ⟨old.extractLsb' 0 8, readWrite⟩
      | 131073 => some ⟨old.extractLsb' 8 8, readWrite⟩
      | 131074 => some ⟨old.extractLsb' 16 8, readWrite⟩
      | 131075 => some ⟨old.extractLsb' 24 8, readWrite⟩
      | 131076 => some ⟨0xd8, readWrite⟩ | 131077 => some ⟨0xc7, readWrite⟩
      | 131078 => some ⟨0xb6, readWrite⟩ | 131079 => some ⟨0xa5, readWrite⟩
      | _ => none

def entry (flags : Word) : OS.MutexReplay.Context where
  registers register := if register = .rdi then 65536 else if register = .rsi then 131072
    else if register = .rsp then 32768 else 0xfeedface89abcdef
  rip := 4194304
  flags := flags

def withTicket (state : OS.Mutex.State) (operation : OS.Ownership.Mutation) :
    Except Fault (OS.Mutex.State × OS.Ownership.Ticket) := do
  let (after, result) ← (OS.Mutex.mutate state operation).mapError OS.MutexReplay.Fault.protocol
  let some ticket := result | throw .invalidContext
  pure (after, ticket)

def setupIn (space : Space) : Except Fault (RState × Start) := do
  let initial := OS.Mutex.empty (OS.Borrowing.empty (OS.Ownership.empty space))
  let (lock, lockTicket) ← withTicket initial (.adopt 0 ⟨65536, 4⟩)
  let (data, dataTicket) ← withTicket lock (.adopt 0 ⟨131072, 8⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4194304, 37⟩)
  let (stack, stackTicket) ← withTicket code (.adopt 0 ⟨32768, 8⟩)
  let registered ← (OS.Mutex.register stack
    ⟨0, lockTicket, 65536, dataTicket, 131072, fun value => !value.getLsbD 0⟩).mapError OS.MutexReplay.Fault.protocol
  pure (OS.MutexReplay.empty registered, ⟨entry 0x8d7, codeTicket, stackTicket⟩)

def cohort : Except Fault (RState × Start) := do
  let (initial, start) ← setupIn (seed 0xfffffffe)
  let first ← OS.MutexReplay.spawn initial start
  -- Both workers may read the same immutable return stack and executable code.
  let second ← OS.MutexReplay.spawn first { start with entry := entry 0x246 }
  pure (second, start)

def failedWith {α : Type} (result : Except Fault α) (expected : Fault) : Bool :=
  match result with | .error actual => decide (actual = expected) | .ok _ => false

def protocolFailedWith {α : Type} (result : Except OS.Mutex.Fault α) (expected : OS.Mutex.Fault) : Bool :=
  match result with | .error actual => decide (actual = expected) | .ok _ => false

def selections : List Nat := List.replicate 7 0 ++ List.replicate 4 1 ++
  List.replicate 6 0 ++ List.replicate 13 1

structure Observation where
  payload : Option (BitVec 32)
  adjacentGuard : Option (BitVec 32)
  lock : Option (BitVec 32)
  returns : List Word
  endpoints : List (Word × Word)
  events : List (Nat × AtomicEvent)
  pinned : Bool
  reclaimed : Bool
  deriving DecidableEq, Repr

def handoff : Except Fault Observation := do
  let (initial, start) ← cohort
  let (done, events) ← OS.MutexReplay.verify initial selections
  let pinned := protocolFailedWith (OS.Mutex.mutate done.shared (.protect 0 start.codeTicket readOnly)) (.authority .borrowed)
  let (collected, returns) ← OS.MutexReplay.collect done
  let mutable := OS.Mutex.mutate collected (.protect 0 start.codeTicket readOnly)
  pure ⟨(loadDWord (toMemory collected.shared.resources.space) 131072).toOption,
    (loadDWord (toMemory collected.shared.resources.space) 131076).toOption,
    (loadDWord (toMemory collected.shared.resources.space) 65536).toOption, returns,
    done.workers.map (fun worker => (worker.context.registers .rsp, worker.context.rip)), events,
    pinned, mutable.toOption.isSome⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

-- The busy worker really exchanges 1→1 while its peer holds the odd payload.
-- The two completed requests wrap the initial 0xfffffffe to 2, return through
-- the caller's actual stack, and leave neighboring data unchanged.
example : handoff = .ok ⟨some 2, some 0xa5b6c7d8, some 0, [0, 0],
    [(32776, 8192), (32776, 8192)],
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩), (0, ⟨65536, 1, 0⟩),
     (1, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 0⟩)], true, true⟩ := by rfl

def heldPrefix : Except Fault (Option (BitVec 32) × Option (Nat × Nat) × List Bool × List (Nat × AtomicEvent)) := do
  let (initial, start) ← cohort
  let (odd, events) ← OS.MutexReplay.schedule initial (List.replicate 7 0 ++ List.replicate 4 1)
  let some worker := odd.workers[0]? | throw .missingThread
  let some guard := worker.guard | throw .invalidContext
  let some peer := odd.workers[1]? | throw .missingThread
  let holder := odd.shared.mutex.bind fun record => record.holder.map fun lease => (lease.identifier, lease.actor)
  pure ((loadDWord (toMemory odd.shared.shared.resources.space) 131072).toOption, holder,
    [decide (worker.phase = .incrementingSecond), decide (peer.phase = .entry ∧ peer.guard = none),
     protocolFailedWith (OS.Mutex.release odd.shared 1 guard) .invalidInvariant,
     protocolFailedWith (OS.Mutex.guardStore odd.shared 2 guard 0) .wrongActor,
     protocolFailedWith (OS.Mutex.mutate odd.shared (.protect 0 start.codeTicket readOnly)) (.authority .borrowed),
     protocolFailedWith (OS.Mutex.mutate odd.shared (.release 0 start.stackTicket)) (.authority .borrowed)], events)

example : heldPrefix = .ok (some 0xffffffff, some (0, 1), List.replicate 6 true,
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩)]) := by rfl

-- An incomplete schedule is valid replay, but cannot certify the endpoint.
-- RET itself, and not just restored payload or a released lock, is required.
def lifecycle : Except Fault (List Bool) := do
  let (initial, start) ← cohort
  let incomplete := failedWith (OS.MutexReplay.verify initial (List.replicate 7 0)) .postcondition
  let (odd, _) ← OS.MutexReplay.schedule initial (List.replicate 7 0)
  let some worker := odd.workers[0]? | throw .missingThread
  let some oldGuard := worker.guard | throw .invalidContext
  let early := failedWith (OS.MutexReplay.collect odd) .notCompleted
  let spawnAfterStart := failedWith (OS.MutexReplay.spawn odd start) .started
  let (secondHeld, _) ← OS.MutexReplay.schedule odd
    (List.replicate 4 1 ++ List.replicate 6 0 ++ List.replicate 2 1)
  let stale := protocolFailedWith (OS.Mutex.guardLoad secondHeld.shared 1 oldGuard) .staleGuard
  let (beforeReturn, _) ← OS.MutexReplay.schedule secondHeld (List.replicate 10 1)
  let beforeRet := failedWith (OS.MutexReplay.collect beforeReturn) .notCompleted
  let (done, _) ← OS.MutexReplay.schedule beforeReturn [1]
  pure [incomplete, early, spawnAfterStart, stale, beforeRet,
    failedWith (OS.MutexReplay.dispatch done 0) .alreadyCompleted,
    failedWith (OS.MutexReplay.dispatch done 2) .missingThread,
    failedWith (OS.MutexReplay.verify done []) .started,
    protocolFailedWith (OS.Mutex.guardLoad done.shared 1 oldGuard) .missingGuard]

example : lifecycle = .ok (List.replicate 9 true) := by rfl

def changedCell (address : Word) (cell : Option Cell) : Space :=
  ⟨fun query => if query = address then cell else (seed 0xfffffffe).cells query⟩

def rejectedStart (space : Space) (expected : Fault) : Except Fault Bool := do
  let (initial, start) ← setupIn space
  pure (failedWith (OS.MutexReplay.spawn initial start) expected)

-- A changed branch target and a non-executable final RET reject even though
-- the rest of the routine is intact. Every stack/data operand byte matters.
example : rejectedStart (changedCell 4194315 (some ⟨0xf5, readExecute⟩)) .unsupportedCode = .ok true := by rfl
example : rejectedStart (changedCell 4194340 (some ⟨0xc3, readOnly⟩)) .unsupportedCode = .ok true := by rfl
example : rejectedStart (changedCell 32775 (some ⟨0, inaccessible⟩))
    (.machine (.inaccessibleStack 32775)) = .ok true := by rfl
example : failedWith (setupIn (changedCell 131075 (some ⟨0xff, readOnly⟩)))
    (.protocol (.machine (.writeDenied 131072))) = true := by rfl
example : failedWith (setupIn (changedCell 65539 (some ⟨0, readOnly⟩)))
    (.protocol (.machine (.writeDenied 65536))) = true := by rfl

def contextFailures : Except Fault (List Bool) := do
  let (initial, start) ← setupIn (seed 0xfffffffe)
  let wrongRegisters : OS.MutexReplay.Context :=
    { start.entry with registers := fun register => if register = .rsi then 65536 else start.entry.registers register }
  pure [failedWith (OS.MutexReplay.spawn initial { start with entry := wrongRegisters }) .invalidContext,
    failedWith (OS.MutexReplay.spawn initial { start with codeTicket := ⟨99, 0⟩ })
      (.protocol (.authority (.ownership .missingAllocation))),
    failedWith (OS.MutexReplay.spawn initial { start with stackTicket := ⟨99, 0⟩ })
      (.protocol (.authority (.ownership .missingAllocation)))]

example : contextFailures = .ok (List.replicate 3 true) := by rfl

end EDSL.Tests.MutexReplay

#audit_edsl
