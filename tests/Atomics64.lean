/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Preservation
import EDSL.X86.LockedLogical64.Machine
import EDSL.Logical64.Algebra
import EDSL.Audit

namespace EDSL.Tests.Atomics64
open X86 OS.AddressSpace OS.Atomics64

abbrev Fault := OS.Atomics64.Fault

/-- Literal loader bytes, including upper-half data, a distinct neighboring
qword, actual executable code and a readable caller slot. -/
def loader : Space where
  cells address := match address.toNat with
    | 65536 => some ⟨0x10, readWrite⟩
    | 65537 => some ⟨0x32, readWrite⟩
    | 65538 => some ⟨0x54, readWrite⟩
    | 65539 => some ⟨0x76, readWrite⟩
    | 65540 => some ⟨0x98, readWrite⟩
    | 65541 => some ⟨0xba, readWrite⟩
    | 65542 => some ⟨0xdc, readWrite⟩
    | 65543 => some ⟨0x0e, readWrite⟩
    | 65544 => some ⟨0xef, readWrite⟩
    | 65545 => some ⟨0xcd, readWrite⟩
    | 65546 => some ⟨0xab, readWrite⟩
    | 65547 => some ⟨0x89, readWrite⟩
    | 65548 => some ⟨0x67, readWrite⟩
    | 65549 => some ⟨0x45, readWrite⟩
    | 65550 => some ⟨0x23, readWrite⟩
    | 65551 => some ⟨0x01, readWrite⟩
    | 4096 => some ⟨0xf0, readExecute⟩
    | 4097 => some ⟨0x48, readExecute⟩
    | 4098 => some ⟨0x09, readExecute⟩
    | 4099 => some ⟨0x37, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readOnly⟩
    | _ => none

def seed (space : Space := loader) : OS.Atomics64.State :=
  empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty space)))

def failureIs {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def withTicket (state : OS.Atomics64.State) (operation : OS.Ownership.Mutation) :
    Except Fault (OS.Atomics64.State × OS.Ownership.Ticket) := do
  let (after, result) ← mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw .missingCell

def owned : Except Fault (OS.Atomics64.State × OS.Ownership.Ticket) :=
  withTicket (seed loader) (.adopt 7 ⟨65536, 16⟩)

-- Both handles exist before either actor executes. Literal event words and
-- bytes detect stale issuance snapshots, upper32 truncation and wrong endian.
def twoActors (reverse : Bool) : Except Fault
    (Event × Event × List (Option Byte) × Except Error Word) := do
  let (state, ticket) ← owned
  let (registered, cell) ← enroll state 7 ticket 65536
  let (one, a) ← issue registered 7 cell 11
  let (both, b) ← issue one 7 cell 12
  let (first, firstEvent) ← if reverse then logicalDiscard both 12 b 1
    else logicalDiscard both 11 a 0x8000000000000000
  let (last, lastEvent) ← if reverse then logicalDiscard first 11 a 0x8000000000000000
    else logicalDiscard first 12 b 1
  let memory := toMemory last.legacy.shared.resources.space
  return (firstEvent, lastEvent,
    [memory.read 65536, memory.read 65537, memory.read 65538, memory.read 65539,
     memory.read 65540, memory.read 65541, memory.read 65542, memory.read 65543],
    loadQWord memory 65544)

example : twoActors false = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨.bor, 0x8000000000000000,
      ⟨65536, 0x0edcba9876543210, 0x8edcba9876543210⟩⟩⟩,
     ⟨12, ⟨1⟩, ⟨0⟩, ⟨.bor, 1, ⟨65536, 0x8edcba9876543210, 0x8edcba9876543211⟩⟩⟩,
     [some 0x11, some 0x32, some 0x54, some 0x76, some 0x98, some 0xba, some 0xdc, some 0x8e],
     .ok 0x0123456789abcdef) := by rfl

example : twoActors true = .ok
    (⟨12, ⟨1⟩, ⟨0⟩, ⟨.bor, 1, ⟨65536, 0x0edcba9876543210, 0x0edcba9876543211⟩⟩⟩,
     ⟨11, ⟨0⟩, ⟨0⟩, ⟨.bor, 0x8000000000000000,
      ⟨65536, 0x0edcba9876543211, 0x8edcba9876543211⟩⟩⟩,
     [some 0x11, some 0x32, some 0x54, some 0x76, some 0x98, some 0xba, some 0xdc, some 0x8e],
     .ok 0x0123456789abcdef) := by rfl

-- Every mutation and read loan to the neighboring qword is still forbidden
-- after the LAST handle closes. Retirement, rather than close, lifts the gate.
def persistentRegistration : Except Fault (List Bool × Except Error Word) := do
  let (state, ticket) ← owned
  let (registered, cell) ← enroll state 7 ticket 65536
  let (active, handle) ← issue registered 7 cell 11
  let busy := failureIs (retire active 7 cell) .liveHandles
  let closed ← close active 11 handle
  let checks := [busy,
    failureIs (mutate closed (.store 7 ticket 65544 0)) .reserved,
    failureIs (mutate closed (.store64 7 ticket 65544 0)) .reserved,
    failureIs (mutate closed (.protect 7 ticket readOnly)) .reserved,
    failureIs (mutate closed (.transfer 7 ticket 8)) .reserved,
    failureIs (mutate closed (.release 7 ticket)) .reserved,
    failureIs (readBorrow closed 7 ticket 21 ⟨65544, 8⟩) .reserved,
    failureIs (issue32 closed 7 ticket 12 65544) .reserved,
    failureIs (enroll closed 7 ticket 65544) .reserved]
  let retired ← retire closed 7 cell
  let (written, _) ← mutate retired (.store64 7 ticket 65544 0x8070605040302010)
  return (checks, loadQWord (toMemory written.legacy.shared.resources.space) 65544)

example : persistentRegistration = .ok
    ([true, true, true, true, true, true, true, true, true], .ok 0x8070605040302010) := by rfl

-- Conflicts are allocation-wide and independent of registration order, even
-- when the ordinary loan or old32 handle addresses the upper, disjoint qword.
def conflictOrders : Except Fault (List Bool) := do
  let (state, ticket) ← owned
  let (old32, oldHandle) ← issue32 state 7 ticket 12 65544
  let oldFirst := failureIs (enroll old32 7 ticket 65536) .legacyReservation
  let noOld ← close32 old32 12 oldHandle
  let (reader, loan) ← readBorrow noOld 7 ticket 21 ⟨65544, 8⟩
  let readerFirst := failureIs (enroll reader 7 ticket 65536) .borrowed
  let wrongBorrower := failureIs (finishLoan reader 22 loan) (.legacy (.authority .wrongBorrower))
  let free ← finishLoan reader 21 loan
  let (registered, _) ← enroll free 7 ticket 65536
  return [oldFirst, readerFirst, wrongBorrower,
    failureIs (issue32 registered 7 ticket 12 65544) .reserved,
    failureIs (readBorrow registered 7 ticket 21 ⟨65544, 8⟩) .reserved]

example : conflictOrders = .ok [true, true, true, true, true] := by rfl

-- Owner, stored actor and current allocation epoch are independent checks.
-- Reusing the same address and owner cannot revive retired cell/handle IDs.
def revocation : Except Fault (List Bool × Nat × Nat × Event) := do
  let (state, ticket) ← owned
  let (registered, cell) ← enroll state 7 ticket 65536
  let (active, handle) ← issue registered 7 cell 11
  let wrong := [failureIs (issue active 8 cell 12) .wrongOwner,
    failureIs (retire active 8 cell) .wrongOwner,
    failureIs (logicalDiscard active 12 handle 0) .wrongActor,
    failureIs (close active 12 handle) .wrongActor]
  let closed ← close active 11 handle
  let retired ← retire closed 7 cell
  let (transferred, current) ← withTicket retired (.transfer 7 ticket 7)
  let stale := failureIs (enroll transferred 7 ticket 65536) (.ownership .staleEpoch)
  let wrongOwner := failureIs (enroll transferred 8 current 65536) (.ownership .wrongOwner)
  let (again, newCell) ← enroll transferred 7 current 65536
  let (renewed, newHandle) ← issue again 7 newCell 11
  let old := [failureIs (issue renewed 7 cell 12) .missingCell,
    failureIs (retire renewed 7 cell) .missingCell,
    failureIs (logicalDiscard renewed 11 handle 1) .missingHandle,
    failureIs (close renewed 11 handle) .missingHandle]
  let (_, event) ← logicalDiscard renewed 11 newHandle 1
  return (wrong ++ [stale, wrongOwner] ++ old, newCell.index, newHandle.index, event)

example : revocation = .ok
    ([true, true, true, true, true, true, true, true, true, true], 1, 1,
     ⟨11, ⟨1⟩, ⟨1⟩, ⟨.bor, 1, ⟨65536, 0x0edcba9876543210, 0x0edcba9876543211⟩⟩⟩) := by rfl

-- A mapped neighbor does not extend the ticket's interval: the authorized
-- seven bytes, or four bytes of a legacy-sized allocation, cannot authorize8.
def shortAllocation (length : Nat) : Except Fault Bool := do
  let (state, ticket) ← withTicket (seed loader) (.adopt 7 ⟨65536, length⟩)
  return failureIs (enroll state 7 ticket 65536) (.ownership .outsideAllocation)

example : shortAllocation 7 = .ok true := by rfl
example : shortAllocation 4 = .ok true := by rfl

def badAddress : Except Fault (List Bool) := do
  let (state, ticket) ← owned
  return [failureIs (enroll state 7 ticket 65537) (.machine (.unsupportedAtomicAddress 65537)),
    failureIs (enroll state 7 ticket 65545) (.ownership .outsideAllocation)]

example : badAddress = .ok [true, true] := by rfl

-- Independently remove R, W or non-execute permission at EACH of the eight
-- bytes. Enrollment must reject before any live atomic authority is created.
def deniedByte (offset : Nat) (permissions : Permissions) (expected : Fault) : Except Fault Bool := do
  let space := protectUnchecked loader ⟨65536 + BitVec.ofNat 64 offset, 1⟩ permissions
  let (state, ticket) ← withTicket (seed space) (.adopt 7 ⟨65536, 16⟩)
  return failureIs (enroll state 7 ticket 65536) expected

def allByteGates (permissions : Permissions) (expected : Fault) : List (Except Fault Bool) :=
  (List.range 8).map fun offset => deniedByte offset permissions expected

example : allByteGates readOnly (.machine (.writeDenied 65536)) =
    [.ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true] := by rfl
example : allByteGates inaccessible (.machine (.writeDenied 65536)) =
    [.ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true] := by rfl
example : allByteGates ⟨true, true, true⟩ .executable =
    [.ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true] := by rfl

-- Mask zero still produces a labeled full64 event; it is not optimized into
-- an ordinary read. The existing upper32 bits and current caller loans survive.
def unchangedAndLoans : Except Fault
    (Event × Except OS.Borrowing.ReadFault (BitVec 32) × Except OS.Borrowing.ReadFault Word ×
      Except Error LockedLogical64.Instruction × Bool) := do
  let (state, ticket) ← owned
  let (coded, code) ← withTicket state (.adopt 7 ⟨4096, 5⟩)
  let (stacked, stack) ← withTicket coded (.adopt 7 ⟨32768, 8⟩)
  let (codeLoaned, codeLoan) ← readBorrow stacked 7 code 21 ⟨4096, 5⟩
  let (loans, stackLoan) ← readBorrow codeLoaned 7 stack 22 ⟨32768, 8⟩
  let (registered, cell) ← enroll loans 7 ticket 65536
  let (active, handle) ← issue registered 7 cell 11
  let (changed, event) ← logicalDiscard active 11 handle 0
  let snapshot : X86.State := {
    registers := fun _ => 0
    rip := 4096
    flags := 0
    memory := toMemory changed.legacy.shared.resources.space }
  let wrongFinish := failureIs (finishLoan changed 21 stackLoan) (.legacy (.authority .wrongBorrower))
  return (event, OS.Borrowing.loadWord changed.legacy.shared 21 codeLoan 4096,
    OS.Borrowing.loadWord64 changed.legacy.shared 22 stackLoan 32768,
    LockedLogical64.decodeAt snapshot, wrongFinish)

example : unchangedAndLoans = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨.bor, 0, ⟨65536, 0x0edcba9876543210, 0x0edcba9876543210⟩⟩⟩,
     .ok 0x370948f0, .ok 8192, .ok .orRdiRsi, true) := by rfl

-- These are intentionally hostile present-state inputs, not admitted resource
-- transitions. A previously issued handle must recheck EVERY current byte;
-- even mask0 cannot use a stale writable/nonexecutable issuance snapshot.
def deniedRmwByte (offset : Nat) (permissions : Permissions) (expected : Fault) : Except Fault Bool := do
  let (state, ticket) ← owned
  let (registered, cell) ← enroll state 7 ticket 65536
  let (active, handle) ← issue registered 7 cell 11
  let hostile := { active with legacy := { active.legacy with shared := { active.legacy.shared with
    resources := { active.legacy.shared.resources with
      space := protectUnchecked active.legacy.shared.resources.space
        ⟨65536 + BitVec.ofNat 64 offset, 1⟩ permissions } } } }
  return failureIs (logicalDiscard hostile 11 handle 0) expected

def allRmwByteGates (permissions : Permissions) (expected : Fault) : List (Except Fault Bool) :=
  (List.range 8).map fun offset => deniedRmwByte offset permissions expected

example : allRmwByteGates readOnly (.machine (.writeDenied 65536)) =
    [.ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true] := by rfl
example : allRmwByteGates inaccessible (.machine (.writeDenied 65536)) =
    [.ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true] := by rfl
example : allRmwByteGates ⟨true, true, true⟩ .executable =
    [.ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true, .ok true] := by rfl

/-- Symbolic domain witness, assembled through checked allocation/store/enroll/
issue. Arbitrary old64 and mask64 are admitted by current resources, not by
assuming success or by supplying a future execution oracle. -/
def allocated : OS.Atomics64.State := empty (OS.Atomics.empty (OS.Borrowing.empty
  (OS.Ownership.install (OS.Ownership.empty OS.AddressSpace.empty)
    (mapUnchecked OS.AddressSpace.empty ⟨65536, 8⟩ readWrite) 7 ⟨65536, 8⟩)))

def prepared (old : Word) : OS.Atomics64.State :=
  { allocated with legacy := { allocated.legacy with shared := { allocated.legacy.shared with
    resources := { allocated.legacy.shared.resources with
      space := writeQWordCells allocated.legacy.shared.resources.space 65536 old } } } }

def registered (old : Word) : OS.Atomics64.State :=
  installCell (prepared old) ⟨7, ⟨0, 0⟩, 65536⟩

def live (old : Word) : OS.Atomics64.State := installHandle (registered old) ⟨11, ⟨0⟩⟩

theorem allocated_valid : WellFormed allocated := by
  have valid := empty_wellFormed _ (OS.Atomics.empty_wellFormed _
    (OS.Borrowing.empty_wellFormed _ (OS.Ownership.empty_wellFormed OS.AddressSpace.empty)))
  exact mutate_wellFormed (seed OS.AddressSpace.empty)
    (.allocate 7 ⟨65536, 8⟩ readWrite) (allocated, some ⟨0, 0⟩) valid (by rfl)

theorem prepared_store (old : Word) :
    mutate allocated (.store64 7 ⟨0, 0⟩ 65536 old) = .ok (prepared old, none) := by rfl

theorem prepared_valid (old : Word) : WellFormed (prepared old) :=
  mutate_wellFormed _ _ _ allocated_valid (prepared_store old)

theorem registered_valid (old : Word) : WellFormed (registered old) := by
  have success : enroll (prepared old) 7 ⟨0, 0⟩ 65536 = .ok (registered old, ⟨0⟩) := by rfl
  exact (enroll_wellFormed _ _ _ _ _ (prepared_valid old) success).1

theorem live_valid (old : Word) : WellFormed (live old) := by
  have success : issue (registered old) 7 ⟨0⟩ 11 = .ok (live old, ⟨0⟩) := by rfl
  exact (issue_wellFormed _ _ _ _ _ (registered_valid old) success).1

theorem every_old_and_mask (old mask : Word) :
    ∃ result, WellFormed (live old) ∧
      logicalDiscard (live old) 11 ⟨0⟩ mask = .ok result ∧
      result.2.logical.event.before = old ∧
      ∀ index : Fin 64,
        Logical64.HasBit result.2.logical.event.after index ↔
          Logical64.HasBit old index ∨ Logical64.HasBit mask index := by
  obtain ⟨result, success⟩ := logicalDiscard_enabled (live old) 11 ⟨0⟩ mask
    ⟨11, ⟨0⟩⟩ ⟨7, ⟨0, 0⟩, 65536⟩ (live_valid old) (by rfl)
  have sound := logicalDiscard_sound _ _ _ _ _ success
  have authorized : authorize (live old) 11 ⟨0⟩ =
      .ok (⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩) := by rfl
  have checked := logicalDiscard_guarded _ _ _ _ _ success
  obtain ⟨selected, target, authority, eventEq, _⟩ := checked
  have identities := Except.ok.inj (authority.symm.trans authorized)
  rcases identities with ⟨rfl, rfl⟩
  have atAddress : result.2.logical.event.address = 65536 := by rw [eventEq]
  have beforeEq : result.2.logical.event.before = old := by
    have currentRead : loadQWord (toMemory (live old).legacy.shared.resources.space) 65536 = .ok old := by
      exact (OS.Borrowing.store64_effect (legacy_store64_guarded
        (show OS.Atomics.mutate allocated.legacy (.store64 7 ⟨0, 0⟩ 65536 old) =
          .ok ((prepared old).legacy, none) from by rfl))).readback
    exact Except.ok.inj (sound.1.2.2.1.symm.trans (atAddress ▸ currentRead))
  refine ⟨result, live_valid old, success, beforeEq, ?_⟩
  intro index
  rw [sound.2.2.2.1, beforeEq]
  exact Logical64.HasBit.or_iff old mask index


-- A reservation must not become a global lock: ordinary changes to a distinct
-- allocation, then a second independently registered cell, remain admitted.
def independentAllocations : Except Fault (Event × Event × Except Error Word × Except Error Word) := do
  let (state, ticket) ← owned
  let (registered, cell) ← enroll state 7 ticket 65536
  let (active, a) ← issue registered 7 cell 11
  let (allocatedOther, other) ← withTicket active (.allocate 8 ⟨131072, 8⟩ readWrite)
  let (writtenOther, _) ← mutate allocatedOther (.store64 8 other 131072 0x0123456789abcdef)
  let (registeredOther, cellOther) ← enroll writtenOther 8 other 131072
  let (both, b) ← issue registeredOther 8 cellOther 12
  let (first, _) ← logicalDiscard both 11 a 0x8000000000000000
  let (second, bEvent) ← logicalDiscard first 12 b 0x8000000000000000
  let (last, aEvent) ← logicalDiscard second 11 a 1
  return (aEvent, bEvent, loadQWord (toMemory last.legacy.shared.resources.space) 65536,
    loadQWord (toMemory last.legacy.shared.resources.space) 131072)

example : independentAllocations = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨.bor, 1, ⟨65536, 0x8edcba9876543210, 0x8edcba9876543211⟩⟩⟩,
     ⟨12, ⟨1⟩, ⟨1⟩, ⟨.bor, 0x8000000000000000,
       ⟨131072, 0x0123456789abcdef, 0x8123456789abcdef⟩⟩⟩,
     .ok 0x8edcba9876543211, .ok 0x8123456789abcdef) := by rfl

-- The old raw address can name a new allocation, but not old logical IDs or
-- allocation tickets. Successful actual reallocation supplies the new epoch0.
def releaseAndReuse : Except Fault (List Bool × Nat × Nat × Nat × Event) := do
  let (state, ticket) ← owned
  let (registered, cell) ← enroll state 7 ticket 65536
  let (active, handle) ← issue registered 7 cell 11
  let closed ← close active 11 handle
  let retired ← retire closed 7 cell
  let (released, _) ← mutate retired (.release 7 ticket)
  let (allocatedAgain, freshTicket) ← withTicket released (.allocate 7 ⟨65536, 16⟩ readWrite)
  let oldTicket := failureIs (enroll allocatedAgain 7 ticket 65536) (.ownership .missingAllocation)
  let (again, newCell) ← enroll allocatedAgain 7 freshTicket 65536
  let (renewed, newHandle) ← issue again 7 newCell 11
  let (_, event) ← logicalDiscard renewed 11 newHandle 0x8000000000000001
  return ([oldTicket, failureIs (issue renewed 7 cell 11) .missingCell,
      failureIs (logicalDiscard renewed 11 handle 1) .missingHandle],
    freshTicket.identifier, newCell.index, newHandle.index, event)

example : releaseAndReuse = .ok
    ([true, true, true], 1, 1, 1,
     ⟨11, ⟨1⟩, ⟨1⟩, ⟨.bor, 0x8000000000000001, ⟨65536, 0, 0x8000000000000001⟩⟩⟩) := by rfl

end EDSL.Tests.Atomics64

#audit_edsl
#print axioms EDSL.Tests.Atomics64.every_old_and_mask
