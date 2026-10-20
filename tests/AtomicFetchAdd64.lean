/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAdd64
import EDSL.Audit

namespace EDSL.Tests.AtomicFetchAdd64
open X86 OS.AddressSpace OS.Atomics64

abbrev Fault := OS.Atomics64.Fault
abbrev Managed := OS.Atomics64.State

def seed : Managed :=
  empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty)))

structure Ready where
  state : Managed
  ticket : OS.Ownership.Ticket
  cell : CellId64
  handle : HandleId64

def ticketFrom (output : Option OS.Ownership.Ticket) : Except Fault OS.Ownership.Ticket :=
  match output with
  | some ticket => .ok ticket
  | none => .error .missingCell

/-- Every executable fixture uses actual allocation, full64 stores, enrollment
and issue. No authorization, read or mutation is replaced by a mock. -/
def setup (old : Word) : Except Fault Ready := do
  let (allocated, output) ← mutate seed (.allocate 7 ⟨65536, 16⟩ readWrite)
  let ticket ← ticketFrom output
  let (neighbor, _) ← mutate allocated (.store64 7 ticket 65544 0x8877665544332211)
  let (written, _) ← mutate neighbor (.store64 7 ticket 65536 old)
  let (registered, cell) ← enroll written 7 ticket 65536
  let (live, handle) ← issue registered 7 cell 11
  return ⟨live, ticket, cell, handle⟩

def response (old delta : Word) : Except Fault (FetchAddEvent × Except Error Word × Except Error Word) := do
  let ready ← setup old
  let (after, event) ← fetchAdd ready.state 11 ready.handle delta
  let memory := toMemory after.legacy.shared.resources.space
  return (event, loadQWord memory 65536, loadQWord memory 65544)

-- Literal full64 answers distinguish arithmetic from logical ops, low32
-- truncation, lost high deltas and failure to wrap at exactly 64 bits.
example : response 0x12345678ffffffff 1 = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨1, ⟨65536, 0x12345678ffffffff, 0x1234567900000000⟩⟩⟩,
      .ok 0x1234567900000000, .ok 0x8877665544332211) := by rfl

example : response 0xffffffffffffffff 2 = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨2, ⟨65536, 0xffffffffffffffff, 1⟩⟩⟩,
      .ok 1, .ok 0x8877665544332211) := by rfl

example : response 0x0000000100000005 0x8000000200000000 = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨0x8000000200000000,
      ⟨65536, 0x0000000100000005, 0x8000000300000005⟩⟩⟩,
      .ok 0x8000000300000005, .ok 0x8877665544332211) := by rfl

example : response 0x8000000000000001 0x8000000000000000 = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨0x8000000000000000, ⟨65536, 0x8000000000000001, 1⟩⟩⟩,
      .ok 1, .ok 0x8877665544332211) := by rfl

example : response 0xfedcba9876543210 0 = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨0, ⟨65536, 0xfedcba9876543210, 0xfedcba9876543210⟩⟩⟩,
      .ok 0xfedcba9876543210, .ok 0x8877665544332211) := by rfl

/-- Both handles are issued before any addition. Each response must contain
the other actor's most recent result rather than an issuance-time snapshot. -/
def currentChain : Except Fault (List FetchAddEvent × Except Error Word) := do
  let ready ← setup 0xfffffffffffffffe
  let (both, second) ← issue ready.state 7 ready.cell 12
  let (one, first) ← fetchAdd both 11 ready.handle 1
  let (two, middle) ← fetchAdd one 12 second 2
  let (last, final) ← fetchAdd two 11 ready.handle 0x100000000
  return ([first, middle, final], loadQWord (toMemory last.legacy.shared.resources.space) 65536)

example : currentChain = .ok
    ([⟨11, ⟨0⟩, ⟨0⟩, ⟨1, ⟨65536, 0xfffffffffffffffe, 0xffffffffffffffff⟩⟩⟩,
      ⟨12, ⟨1⟩, ⟨0⟩, ⟨2, ⟨65536, 0xffffffffffffffff, 1⟩⟩⟩,
      ⟨11, ⟨0⟩, ⟨0⟩, ⟨0x100000000, ⟨65536, 1, 0x100000001⟩⟩⟩], .ok 0x100000001) := by rfl

def failureIs {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

example : (fetchAdd seed 11 ⟨0⟩ 0).map (fun _ => true) = .error .missingHandle := by rfl

/-- Zero delta still requires actor authority, emits a full old-value response
and retains the allocation-wide exclusion until close followed by retire. -/
def lifecycle : Except Fault (FetchAddEvent × List Bool × Except Error Word × FetchAddEvent) := do
  let ready ← setup 0x8000000000000001
  let (after, event) ← fetchAdd ready.state 11 ready.handle 0
  let wrong := failureIs (fetchAdd after 12 ready.handle 0) .wrongActor
  let target := failureIs (mutate after (.store64 7 ready.ticket 65536 0)) .reserved
  let neighbor := failureIs (mutate after (.store64 7 ready.ticket 65544 0)) .reserved
  let dword := failureIs (mutate after (.store 7 ready.ticket 65548 0)) .reserved
  let release := failureIs (mutate after (.release 7 ready.ticket)) .reserved
  let transfer := failureIs (mutate after (.transfer 7 ready.ticket 8)) .reserved
  let protect := failureIs (mutate after (.protect 7 ready.ticket readOnly)) .reserved
  let borrow := failureIs (readBorrow after 7 ready.ticket 22 ⟨65544, 8⟩) .reserved
  let legacy := failureIs (issue32 after 7 ready.ticket 12 65544) .reserved
  let busy := failureIs (retire after 7 ready.cell) .liveHandles
  let closed ← close after 11 ready.handle
  let revoked := failureIs (fetchAdd closed 11 ready.handle 0) .missingHandle
  let pinned := failureIs (mutate closed (.store64 7 ready.ticket 65544 0)) .reserved
  let retired ← retire closed 7 ready.cell
  let oldCell := failureIs (issue retired 7 ready.cell 11) .missingCell
  let (written, _) ← mutate retired (.store64 7 ready.ticket 65544 0x0123456789abcdef)
  let (transferred, output) ← mutate written (.transfer 7 ready.ticket 7)
  let newTicket ← ticketFrom output
  let stale := failureIs (enroll transferred 7 ready.ticket 65536) (.ownership .staleEpoch)
  let (registered, newCell) ← enroll transferred 7 newTicket 65536
  let (renewed, newHandle) ← issue registered 7 newCell 11
  let oldHandle := failureIs (fetchAdd renewed 11 ready.handle 0) .missingHandle
  let (last, fresh) ← fetchAdd renewed 11 newHandle 1
  return (event, [wrong, target, neighbor, dword, release, transfer, protect, borrow,
      legacy, busy, revoked, pinned, oldCell, stale, oldHandle],
    loadQWord (toMemory last.legacy.shared.resources.space) 65544, fresh)

example : lifecycle = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨0, ⟨65536, 0x8000000000000001, 0x8000000000000001⟩⟩⟩,
      List.replicate 15 true, .ok 0x0123456789abcdef,
      ⟨11, ⟨1⟩, ⟨1⟩, ⟨1, ⟨65536, 0x8000000000000001, 0x8000000000000002⟩⟩⟩) := by rfl

/-- Hostile current-world changes explicitly bypass managed reservation.
The still-present handle must recheck the current allocation at the RMW itself. -/
def invalidated (operation : OS.Ownership.Mutation) (expected : Fault) : Except Fault Bool := do
  let ready ← setup 0x8000000000000001
  let (legacy, _) ← (OS.Atomics.mutate ready.state.legacy operation).mapError Fault.legacy
  return failureIs (fetchAdd { ready.state with legacy := legacy } 11 ready.handle 0) expected

example : invalidated (.transfer 7 ⟨0, 0⟩ 7) (.ownership .staleEpoch) = .ok true := by rfl
example : invalidated (.release 7 ⟨0, 0⟩) (.ownership .missingAllocation) = .ok true := by rfl
example : invalidated (.protect 7 ⟨0, 0⟩ readOnly) (.machine (.writeDenied 65536)) = .ok true := by rfl
example : invalidated (.protect 7 ⟨0, 0⟩ ⟨true, true, true⟩) .executable = .ok true := by rfl

/-- Changing current owner without changing epoch must also fail; this hostile
registry edit is outside admitted transitions, not an alternate issue API. -/
def wrongCurrentOwner : Except Fault Bool := do
  let ready ← setup 0x8000000000000001
  let resources := OS.Ownership.replace ready.state.legacy.shared.resources 0 (some ⟨8, 0, ⟨65536, 16⟩⟩)
  let hostile := { ready.state with legacy := { ready.state.legacy with
    shared := { ready.state.legacy.shared with resources := resources } } }
  return failureIs (fetchAdd hostile 11 ready.handle 0) (.ownership .wrongOwner)

example : wrongCurrentOwner = .ok true := by rfl

/-- A handle record cannot resurrect a retired cell. Close/retire are real;
only the hostile copied handle is manually restored after those operations. -/
def revokedCell : Except Fault Bool := do
  let ready ← setup 0x8000000000000001
  let closed ← close ready.state 11 ready.handle
  let retired ← retire closed 7 ready.cell
  let hostile := { retired with handles := ready.state.handles }
  return failureIs (fetchAdd hostile 11 ready.handle 0) .missingCell

example : revokedCell = .ok true := by rfl

def withSpace (state : Managed) (space : OS.AddressSpace.Space) : Managed :=
  { state with legacy := { state.legacy with shared := { state.legacy.shared with
    resources := { state.legacy.shared.resources with space := space } } } }

/-- Every byte, especially the upper half, is rechecked after issue. Readable
neighbors, zero delta and a retained handle cannot excuse a missing permission. -/
def deniedByte (offset : Nat) (permissions : Permissions) (expected : Fault) : Except Fault Bool := do
  let ready ← setup 0x8000000000000001
  let hostile := withSpace ready.state (protectUnchecked ready.state.legacy.shared.resources.space
    ⟨65536 + BitVec.ofNat 64 offset, 1⟩ permissions)
  return failureIs (fetchAdd hostile 11 ready.handle 0) expected

example : (List.range 8).map (fun offset => deniedByte offset readOnly (.machine (.writeDenied 65536))) =
    List.replicate 8 (.ok true) := by rfl
example : (List.range 8).map (fun offset => deniedByte offset inaccessible (.machine (.writeDenied 65536))) =
    List.replicate 8 (.ok true) := by rfl
example : (List.range 8).map (fun offset => deniedByte offset ⟨true, true, true⟩ .executable) =
    List.replicate 8 (.ok true) := by rfl

def missingUpperByte (offset : Nat) : Except Fault Bool := do
  let ready ← setup 0x8000000000000001
  let hostile := withSpace ready.state (unmapUnchecked ready.state.legacy.shared.resources.space
    ⟨65536 + BitVec.ofNat 64 offset, 1⟩)
  return failureIs (fetchAdd hostile 11 ready.handle 0x8000000000000000) (.machine (.writeDenied 65536))

example : [4, 5, 6, 7].map missingUpperByte = List.replicate 4 (.ok true) := by rfl

/-- Mapped adjacent bytes do not extend a current allocation's authority. -/
def shortenedAllocation : Except Fault Bool := do
  let ready ← setup 0x8000000000000001
  let resources := OS.Ownership.replace ready.state.legacy.shared.resources 0 (some ⟨7, 0, ⟨65536, 4⟩⟩)
  let hostile := { ready.state with legacy := { ready.state.legacy with
    shared := { ready.state.legacy.shared with resources := resources } } }
  return failureIs (fetchAdd hostile 11 ready.handle 0) (.ownership .outsideAllocation)

example : shortenedAllocation = .ok true := by rfl

/-- A caller slot, executable code and an external read loan are established
through current operations. Fetch-add must retain their bytes and permissions,
and both registered cells must retain each other's full64 current contents. -/
def protectedResources : Except Fault
    (FetchAddEvent × Except OS.Borrowing.ReadFault Word × Except Error Word ×
      List (Option Byte) × List Bool × Except Error Word × Except Error Word) := do
  let ready ← setup 0x12345678ffffffff
  let (external, output) ← mutate ready.state (.allocate 8 ⟨131072, 8⟩ readWrite)
  let externalTicket ← ticketFrom output
  let (externalWritten, _) ← mutate external (.store64 8 externalTicket 131072 0x87654321fedcba98)
  let (loaned, loan) ← readBorrow externalWritten 8 externalTicket 22 ⟨131072, 8⟩
  let (caller, output) ← mutate loaned (.allocate 9 ⟨196608, 8⟩ readWrite)
  let callerTicket ← ticketFrom output
  let (callerWritten, _) ← mutate caller (.store64 9 callerTicket 196608 0x0102030405060708)
  let (callerLoaned, _) ← readBorrow callerWritten 9 callerTicket 22 ⟨196608, 8⟩
  let (code, output) ← mutate callerLoaned (.allocate 10 ⟨262144, 8⟩ readWrite)
  let codeTicket ← ticketFrom output
  let (codeWritten, _) ← mutate code (.store64 10 codeTicket 262144 0x90909090909090c3)
  let (executable, _) ← mutate codeWritten (.protect 10 codeTicket readExecute)
  let (guarded, _) ← readBorrow executable 10 codeTicket 22 ⟨262144, 8⟩
  let (changed, event) ← fetchAdd guarded 11 ready.handle 1
  let loanValue := OS.Borrowing.loadWord64 changed.legacy.shared 22 loan 131072
  let ended ← finishLoan changed 22 loan
  let (otherRegistered, otherCell) ← enroll ended 8 externalTicket 131072
  let (both, otherHandle) ← issue otherRegistered 8 otherCell 12
  let (last, _) ← fetchAdd both 12 otherHandle 0x100000000
  let memory := toMemory last.legacy.shared.resources.space
  return (event, loanValue, readWord memory 196608,
    (List.range 8).map (fun offset => memory.read (262144 + BitVec.ofNat 64 offset)),
    [memory.executable 262144, memory.executable 262151, memory.writable 262144,
      memory.writable 196608], loadQWord memory 65536, loadQWord memory 131072)

example : protectedResources = .ok
    (⟨11, ⟨0⟩, ⟨0⟩, ⟨1, ⟨65536, 0x12345678ffffffff, 0x1234567900000000⟩⟩⟩,
      .ok 0x87654321fedcba98, .ok 0x0102030405060708,
      [some 0xc3, some 0x90, some 0x90, some 0x90, some 0x90, some 0x90, some 0x90, some 0x90],
      [true, true, false, true], .ok 0x1234567900000000, .ok 0x87654322fedcba98) := by rfl

end EDSL.Tests.AtomicFetchAdd64

#audit_edsl
#print axioms EDSL.OS.Atomics64.fetchAdd_primitive
#print axioms EDSL.OS.Atomics64.fetchAdd_enabled_of_live
#print axioms EDSL.OS.Atomics64.fetchAdd_wellFormed
#print axioms EDSL.OS.Atomics64.fetchAdd_full_permissions
#print axioms EDSL.OS.Atomics64.fetchAdd_preserves_caller
#print axioms EDSL.OS.Atomics64.fetchAdd_loan_read
