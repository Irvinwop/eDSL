/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicAccess64
import EDSL.OS.Borrowing.Read64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicAccess64
open X86 OS.AddressSpace OS.Atomics64

abbrev Fault := OS.Atomics64.Fault
abbrev Shared := OS.Atomics64.State

/-- Independent code and caller bytes. The mutable test operands are created
and initialized through the real checked allocation/store operations below. -/
def loader : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0x0f, readExecute⟩
    | 4097 => some ⟨0x1f, readExecute⟩
    | 4098 => some ⟨0x00, readExecute⟩
    | 4099 => some ⟨0xc3, readExecute⟩
    | 32768 => some ⟨0x88, readOnly⟩
    | 32769 => some ⟨0x77, readOnly⟩
    | 32770 => some ⟨0x66, readOnly⟩
    | 32771 => some ⟨0x55, readOnly⟩
    | 32772 => some ⟨0x44, readOnly⟩
    | 32773 => some ⟨0x33, readOnly⟩
    | 32774 => some ⟨0x22, readOnly⟩
    | 32775 => some ⟨0x11, readOnly⟩
    | _ => none

def initial : Shared :=
  empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty loader)))

def withTicket (state : Shared) (operation : OS.Ownership.Mutation) :
    Except Fault (Shared × OS.Ownership.Ticket) := do
  let (after, ticket) ← mutate state operation
  match ticket with
  | some ticket => return (after, ticket)
  | none => throw .missingCell

structure Setup where
  state : Shared
  ticket : OS.Ownership.Ticket
  cell : CellId64
  writer : HandleId64
  reader : HandleId64
  codeLoan : Nat
  callerLoan : Nat

/-- Both actor handles and both unrelated loans precede every tested access.
In particular the reader's handle cannot contain the subsequent store value. -/
def setup : Except Fault Setup := do
  let (coded, code) ← withTicket initial (.adopt 7 ⟨4096, 4⟩)
  let (stacked, caller) ← withTicket coded (.adopt 7 ⟨32768, 8⟩)
  let (codeLoaned, codeLoan) ← readBorrow stacked 7 code 21 ⟨4096, 4⟩
  let (loaned, callerLoan) ← readBorrow codeLoaned 7 caller 22 ⟨32768, 8⟩
  let (allocated, ticket) ← withTicket loaned (.allocate 7 ⟨65536, 16⟩ readWrite)
  let (written, _) ← mutate allocated (.store64 7 ticket 65536 0x0000000100000000)
  let (neighbors, _) ← mutate written (.store64 7 ticket 65544 0x0123456789abcdef)
  let (registered, cell) ← enroll neighbors 7 ticket 65536
  let (one, writer) ← issue registered 7 cell 11
  let (both, reader) ← issue one 7 cell 12
  return ⟨both, ticket, cell, writer, reader, codeLoan, callerLoan⟩

def failureIs {α : Type} (result : Except Fault α) (expected : Fault) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- Each old handle reads its peer's subsequent publication, including upper
bits. Literal little-endian bytes, the adjacent qword, live code/caller reads,
and continuing reservation independently constrain the actual memory effect. -/
def roundTrip : Except Fault
    (StoreEvent64 × LoadEvent64 × StoreEvent64 × LoadEvent64 ×
      List (Option Byte) × Except Error Word ×
      Except OS.Borrowing.ReadFault (BitVec 32) ×
      Except OS.Borrowing.ReadFault Word × List Bool) := do
  let current ← setup
  let (first, firstStore) ← publishStore current.state 11 current.writer 0x8070605040302010
  let (observed, firstRead) ← load first 12 current.reader
  let (second, secondStore) ← publishStore observed 12 current.reader 0xfedcba9876543210
  let (last, secondRead) ← load second 11 current.writer
  let memory := toMemory last.legacy.shared.resources.space
  return (firstStore, firstRead, secondStore, secondRead,
    [65536,65537,65538,65539,65540,65541,65542,65543].map memory.read,
    loadQWord memory 65544,
    OS.Borrowing.loadWord last.legacy.shared 21 current.codeLoan 4096,
    OS.Borrowing.loadWord64 last.legacy.shared 22 current.callerLoan 32768,
    [failureIs (mutate last (.store64 7 current.ticket 65536 0)) .reserved,
     failureIs (mutate last (.store64 7 current.ticket 65544 0)) .reserved])

example : roundTrip = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, 65536, 0x8070605040302010⟩,
     ⟨12, ⟨1⟩, ⟨0⟩, 65536, 0x8070605040302010⟩,
     ⟨12, ⟨1⟩, ⟨0⟩, 65536, 0xfedcba9876543210⟩,
     ⟨11, ⟨0⟩, ⟨0⟩, 65536, 0xfedcba9876543210⟩,
     [some 0x10, some 0x32, some 0x54, some 0x76,
       some 0x98, some 0xba, some 0xdc, some 0xfe],
     .ok 0x0123456789abcdef, .ok 0xc3001f0f, .ok 0x1122334455667788,
     [true, true]) := by rfl

-- An unchanged-value request cannot skip actor authorization. The old value
-- was established through checked mutation, not supplied as an access premise.
def wrongActor : Except Fault (List Bool) := do
  let current ← setup
  return [failureIs (load current.state 12 current.writer) .wrongActor,
    failureIs (publishStore current.state 12 current.writer 0x0000000100000000) .wrongActor]

example : wrongActor = .ok [true, true] := by rfl

-- Hostile current inputs deliberately invalidate previously checked authority;
-- these are not admitted resource transitions. An old handle must recheck the
-- current epoch rather than merely its own existence and actor label.
def staleEpoch : Except Fault (List Bool) := do
  let current ← setup
  let oldResources := current.state.legacy.shared.resources
  let resources := { oldResources with allocations := (fun identifier =>
    if identifier = current.ticket.identifier then
      (oldResources.allocations identifier).map fun allocation =>
        { allocation with epoch := allocation.epoch + 1 }
    else oldResources.allocations identifier) }
  let hostile := { current.state with legacy := { current.state.legacy with
    shared := { current.state.legacy.shared with resources := resources } } }
  return [failureIs (load hostile 12 current.reader) (.ownership .staleEpoch),
    failureIs (publishStore hostile 11 current.writer 0x0000000100000000) (.ownership .staleEpoch)]

example : staleEpoch = .ok [true, true] := by rfl

-- Change only byte7 AFTER a successful publication. Repeating the exact current
-- value still requires all eight current bytes and nonexecutable normal data.
-- This intentionally conservative managed profile requires RW even for load.
def deniedUpperByte (permissions : Permissions) (expected : Fault) : Except Fault (List Bool) := do
  let current ← setup
  let (published, _) ← publishStore current.state 11 current.writer 0x8070605040302010
  let hostile := { published with legacy := { published.legacy with shared := { published.legacy.shared with
    resources := { published.legacy.shared.resources with
      space := protectUnchecked published.legacy.shared.resources.space ⟨65543, 1⟩ permissions } } } }
  return [failureIs (load hostile 12 current.reader) expected,
    failureIs (publishStore hostile 11 current.writer 0x8070605040302010) expected]

example : deniedUpperByte readOnly (.machine (.writeDenied 65536)) = .ok [true, true] := by rfl
example : deniedUpperByte inaccessible (.machine (.writeDenied 65536)) = .ok [true, true] := by rfl
example : deniedUpperByte ⟨true, true, true⟩ .executable = .ok [true, true] := by rfl

-- Closing the issuing handle and issuing a fresh one to the same actor cannot
-- resurrect the old ID. The fresh handle still reads the actual publication.
def closedHandle : Except Fault (List Bool × LoadEvent64 × Nat) := do
  let current ← setup
  let (published, _) ← publishStore current.state 11 current.writer 0x8070605040302010
  let closed ← close published 11 current.writer
  let (renewed, fresh) ← issue closed 7 current.cell 11
  let (_, observed) ← load renewed 11 fresh
  return ([failureIs (load renewed 11 current.writer) .missingHandle,
    failureIs (publishStore renewed 11 current.writer 0x8070605040302010) .missingHandle],
    observed, fresh.index)

example : closedHandle = .ok
    ([true, true], ⟨11, ⟨2⟩, ⟨0⟩, 65536, 0x8070605040302010⟩, 2) := by rfl

end EDSL.Tests.AtomicAccess64

#audit_edsl
