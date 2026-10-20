/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics
import EDSL.Audit

namespace EDSL.Tests.Atomics
open X86 OS.AddressSpace

def initial : OS.Atomics.State := OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty))

def failureIs {α : Type} (operation : Except OS.Atomics.Fault α) (expected : OS.Atomics.Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def withTicket (state : OS.Atomics.State) (operation : OS.Ownership.Mutation) :
    Except OS.Atomics.Fault (OS.Atomics.State × OS.Ownership.Ticket) := do
  let (after, result) ← OS.Atomics.mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw .missingHandle

def setup : Except OS.Atomics.Fault (OS.Atomics.State × OS.Ownership.Ticket) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (data, _) ← OS.Atomics.mutate owned (.store 7 ticket 65536 0x11223344)
  let (both, _) ← OS.Atomics.mutate data (.store 7 ticket 65540 0xa5b6c7d8)
  return (both, ticket)

-- Separate actor identities share one current word. The second old result
-- must observe the peer's replacement rather than the word at handle issuance.
def twoActors (reverse : Bool) : Except OS.Atomics.Fault
    (BitVec 32 × BitVec 32 × Except Error (BitVec 32) × Except Error (BitVec 32)) := do
  let (owned, ticket) ← setup
  let (one, a) ← OS.Atomics.issue owned 7 ticket 11 65536
  let (both, b) ← OS.Atomics.issue one 7 ticket 12 65536
  let (first, oldA) ← if reverse then OS.Atomics.exchange both 12 b 0x76543210 else OS.Atomics.exchange both 11 a 0x89abcdef
  let (last, oldB) ← if reverse then OS.Atomics.exchange first 11 a 0x89abcdef else OS.Atomics.exchange first 12 b 0x76543210
  return (oldA, oldB, loadDWord (toMemory last.shared.resources.space) 65536,
    loadDWord (toMemory last.shared.resources.space) 65540)

example : twoActors false = .ok (0x11223344, 0x89abcdef, .ok 0x76543210, .ok 0xa5b6c7d8) := by rfl
example : twoActors true = .ok (0x11223344, 0x76543210, .ok 0x89abcdef, .ok 0xa5b6c7d8) := by rfl

-- Pinning applies to the entire allocation, including a disjoint upper word,
-- and lasts until the final actor closes its handle. Wrong actors and other
-- cell addresses cannot turn the shared capability into ordinary write access.
def pinnedLifecycle : Except OS.Atomics.Fault (List Bool × BitVec 32 × Nat) := do
  let (owned, ticket) ← setup
  let (one, a) ← OS.Atomics.issue owned 7 ticket 11 65536
  let (both, b) ← OS.Atomics.issue one 7 ticket 12 65536
  let checks :=
    [failureIs (OS.Atomics.exchange both 12 a 0) .wrongActor,
     failureIs (OS.Atomics.close both 11 b) .wrongActor,
     failureIs (OS.Atomics.issue both 7 ticket 13 65540) .conflictingCell,
     failureIs (OS.Atomics.mutate both (.store 7 ticket 65540 0)) .reserved,
     failureIs (OS.Atomics.mutate both (.protect 7 ticket readOnly)) .reserved,
     failureIs (OS.Atomics.mutate both (.transfer 7 ticket 8)) .reserved,
     failureIs (OS.Atomics.mutate both (.release 7 ticket)) .reserved,
     failureIs (OS.Atomics.readBorrow both 7 ticket 13 ⟨65540, 4⟩) .reserved]
  let last ← OS.Atomics.close both 11 a
  let stillPinned := failureIs (OS.Atomics.mutate last (.store 7 ticket 65536 0)) .reserved
  let unpinned ← OS.Atomics.close last 12 b
  let (changed, _) ← OS.Atomics.mutate unpinned (.store 7 ticket 65536 0x10203040)
  let (renewed, fresh) ← OS.Atomics.issue changed 7 ticket 11 65536
  let stale := failureIs (OS.Atomics.exchange renewed 11 a 0) .missingHandle
  let staleClose := failureIs (OS.Atomics.close renewed 12 b) .missingHandle
  let (_, old) ← OS.Atomics.exchange renewed 11 fresh 0xdeadbeef
  return (checks ++ [stillPinned, stale, staleClose], old, fresh)

example : pinnedLifecycle = .ok
    ([true, true, true, true, true, true, true, true, true, true, true], 0x10203040, 2) := by rfl

-- Ordinary read loans and atomic authority must exclude one another in either
-- creation order, even when the loan covers only the neighboring word.
def ordinaryReaders : Except OS.Atomics.Fault (List Bool × BitVec 32) := do
  let (owned, ticket) ← setup
  let (borrowed, loan) ← OS.Atomics.readBorrow owned 7 ticket 21 ⟨65540, 4⟩
  let blocked := failureIs (OS.Atomics.issue borrowed 7 ticket 11 65536) (.authority .borrowed)
  let free ← OS.Atomics.finishLoan borrowed 21 loan
  let (active, handle) ← OS.Atomics.issue free 7 ticket 11 65536
  let reversed := failureIs (OS.Atomics.readBorrow active 7 ticket 21 ⟨65540, 4⟩) .reserved
  let (_, old) ← OS.Atomics.exchange active 11 handle 0xffffffff
  return ([blocked, reversed], old)

example : ordinaryReaders = .ok ([true, true], 0x11223344) := by rfl

def independentResources : Except OS.Atomics.Fault (BitVec 32 × BitVec 32 × Except Error (BitVec 32)) := do
  let (owned, ticket) ← setup
  let (first, a) ← OS.Atomics.issue owned 7 ticket 11 65536
  let (other, second) ← withTicket first (.allocate 8 ⟨131072, 4⟩ readWrite)
  let (loaned, loan) ← OS.Atomics.readBorrow other 8 second 21 ⟨131072, 4⟩
  let (changed, oldA) ← OS.Atomics.exchange loaned 11 a 0x89abcdef
  let read ← match OS.Borrowing.loadWord changed.shared 21 loan 131072 with
    | .ok value => pure value
    | .error _ => throw OS.Atomics.Fault.missingHandle
  let finished ← OS.Atomics.finishLoan changed 21 loan
  let (otherActive, b) ← OS.Atomics.issue finished 8 second 12 131072
  let (written, oldB) ← OS.Atomics.exchange otherActive 12 b 0x76543210
  let (again, _) ← OS.Atomics.exchange written 11 a 0x10203040
  if read ≠ 0 then throw .missingHandle
  return (oldA, oldB, loadDWord (toMemory again.shared.resources.space) 131072)

example : independentResources = .ok (0x11223344, 0, .ok 0x76543210) := by rfl

-- Bounds, mapping, current epoch, owner and atomic address support remain
-- checked even before any handles exist.
def issueFailures : Except OS.Atomics.Fault (List Bool) := do
  let (owned, ticket) ← setup
  let checks :=
    [failureIs (OS.Atomics.issue owned 8 ticket 11 65536) (.authority (.ownership .wrongOwner)),
     failureIs (OS.Atomics.issue owned 7 ticket 11 65541) (.authority (.ownership .outsideAllocation)),
     failureIs (OS.Atomics.issue owned 7 ticket 11 65537) (.machine (.unsupportedAtomicAddress 65537)),
     failureIs (OS.Atomics.issue owned 7 ⟨99, 0⟩ 11 65536) (.authority (.ownership .missingAllocation))]
  let (transferred, _) ← withTicket owned (.transfer 7 ticket 7)
  let stale := failureIs (OS.Atomics.issue transferred 7 ticket 11 65536) (.authority (.ownership .staleEpoch))
  return checks ++ [stale]

example : issueFailures = .ok [true, true, true, true, true] := by rfl

def readOnlyTail : Except OS.Atomics.Fault Bool := do
  let mapped ← (OS.AddressSpace.map OS.AddressSpace.empty ⟨65536, 4⟩ readWrite).mapError
    (fun fault => OS.Atomics.Fault.authority (.ownership (.addressSpace fault)))
  let tailReadOnly ← (OS.AddressSpace.protect mapped ⟨65539, 1⟩ readOnly).mapError
    (fun fault => OS.Atomics.Fault.authority (.ownership (.addressSpace fault)))
  let (owned, ticket) ← withTicket
    (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty tailReadOnly))) (.adopt 7 ⟨65536, 4⟩)
  return failureIs (OS.Atomics.issue owned 7 ticket 11 65536) (.machine (.writeDenied 65536))

example : readOnlyTail = .ok true := by rfl

/-- The proof invariant is inhabited by live shared authority, not merely by
an empty registry. Every replacement word has a successful checked exchange. -/
def allocated : OS.Atomics.State := OS.Atomics.empty (OS.Borrowing.empty
  (OS.Ownership.install (OS.Ownership.empty OS.AddressSpace.empty)
    (mapUnchecked OS.AddressSpace.empty ⟨65536, 8⟩ readWrite) 7 ⟨65536, 8⟩))

def live : OS.Atomics.State := OS.Atomics.install allocated ⟨7, ⟨0, 0⟩, 11, 65536⟩

theorem allocated_valid : OS.Atomics.WellFormed allocated := by
  have emptyValid := OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _
    (OS.Ownership.empty_wellFormed OS.AddressSpace.empty))
  exact OS.Atomics.mutate_wellFormed initial (.allocate 7 ⟨65536, 8⟩ readWrite)
    (allocated, some ⟨0, 0⟩) emptyValid (by rfl)

theorem live_valid : OS.Atomics.WellFormed live := by
  have success : OS.Atomics.issue allocated 7 ⟨0, 0⟩ 11 65536 = .ok (live, 0) := by rfl
  exact (OS.Atomics.issue_wellFormed _ _ _ _ _ _ allocated_valid success).1

theorem every_replacement_enabled (value : BitVec 32) :
    ∃ result, OS.Atomics.exchange live 11 0 value = .ok result :=
  OS.Atomics.exchange_enabled _ _ _ ⟨7, ⟨0, 0⟩, 11, 65536⟩ value live_valid (by rfl)

theorem every_old_and_new (old replacement : BitVec 32) :
    ∃ before after, OS.Atomics.WellFormed before ∧
      OS.Atomics.exchange before 11 0 replacement = .ok (after, old) := by
  obtain ⟨prepared, written⟩ := every_replacement_enabled old
  have valid := OS.Atomics.exchange_wellFormed _ _ _ _ _ live_valid written
  obtain ⟨handle, shared, authorized, _, same⟩ := OS.Atomics.exchange_ok _ _ _ _ _ written
  have actualHandle : handle = ⟨7, ⟨0, 0⟩, 11, 65536⟩ := Except.ok.inj authorized.symm
  subst handle
  have nextAuthority : OS.Atomics.authorize prepared.1 11 0 = .ok ⟨7, ⟨0, 0⟩, 11, 65536⟩ := by rw [same]; rfl
  obtain ⟨next, exchanged⟩ := OS.Atomics.exchange_enabled _ _ _ _ replacement valid nextAuthority
  obtain ⟨firstHandle, firstAuthority, first⟩ := OS.Atomics.exchange_sound _ _ _ _ _ written
  have firstEq : firstHandle = ⟨7, ⟨0, 0⟩, 11, 65536⟩ := Except.ok.inj firstAuthority.symm
  subst firstHandle
  obtain ⟨lastHandle, lastAuthority, last⟩ := OS.Atomics.exchange_sound _ _ _ _ _ exchanged
  have lastEq := Except.ok.inj (lastAuthority.symm.trans nextAuthority)
  subst lastHandle
  have oldResult : next.2 = old := Except.ok.inj (last.2.2.1.symm.trans first.readback)
  exact ⟨prepared.1, next.1, valid, exchanged.trans (congrArg Except.ok (Prod.ext rfl oldResult))⟩

def codeAndStack : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0x89, readExecute⟩
    | 4097 => some ⟨0xf0, readExecute⟩
    | 4098 => some ⟨0x87, readExecute⟩
    | 4099 => some ⟨0x07, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readOnly⟩
    | _ => none

-- The first actor changes the word after the second actor's handle is issued.
-- The actual compiler routine must return that current word and produce the
-- same new word as the checked OS operation. Code/stack loans survive both.
def machineComposition : Except OS.Atomics.Fault
    (Word × Word × Word × Word × Nat × Except Error (BitVec 32) × Except Error (BitVec 32)) := do
  let seed := OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty codeAndStack))
  let (owned, data) ← withTicket seed (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (coded, code) ← withTicket owned (.adopt 7 ⟨4096, 5⟩)
  let (stacked, stack) ← withTicket coded (.adopt 7 ⟨32768, 8⟩)
  let (codeLoan, _) ← OS.Atomics.readBorrow stacked 7 code 11 ⟨4096, 5⟩
  let (stackLoan, _) ← OS.Atomics.readBorrow codeLoan 7 stack 12 ⟨32768, 8⟩
  let (one, a) ← OS.Atomics.issue stackLoan 7 data 11 65536
  let (both, b) ← OS.Atomics.issue one 7 data 12 65536
  let (changed, _) ← OS.Atomics.exchange both 11 a 0x89abcdef
  let snapshot : X86.State := {
    registers := fun register => if register = .rdi then 65536
      else if register = .rsp then 32768
      else if register = .rsi then 0xfeedface76543210 else 0xdeadbeef11223344
    rip := 4096
    flags := 0x8d7
    memory := toMemory changed.shared.resources.space }
  let (osFinal, _) ← OS.Atomics.exchange changed 12 b 0x76543210
  let actual ← match run 3 snapshot with
    | .error fault => throw (OS.Atomics.Fault.machine fault)
    | .ok result => pure result
  return (actual.state.registers .rax, actual.state.registers .rsp, actual.state.rip,
    actual.state.flags, actual.instructions, loadDWord actual.state.memory 65536,
    loadDWord (toMemory osFinal.shared.resources.space) 65536)

example : machineComposition = .ok
    (0x89abcdef, 32776, 8192, 0x8d7, 3, .ok 0x76543210, .ok 0x76543210) := by rfl

end EDSL.Tests.Atomics

#audit_edsl
