/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Read64
import EDSL.Audit

namespace EDSL.Tests.Ownership64
open X86 OS.AddressSpace

abbrev World := OS.Ownership.World
abbrev BorrowState := OS.Borrowing.State
abbrev Ticket := OS.Ownership.Ticket

def ownershipFailure {α : Type} (operation : Except OS.Ownership.Fault α)
    (expected : OS.Ownership.Fault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

def borrowFailure {α : Type} (operation : Except OS.Borrowing.Fault α)
    (expected : OS.Borrowing.Fault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

def spaceFailure {α : Type} (operation : Except OS.AddressSpace.Fault α)
    (expected : OS.AddressSpace.Fault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

def readFailure {α : Type} (operation : Except OS.Borrowing.ReadFault α)
    (expected : OS.Borrowing.ReadFault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

def qwordIs (operation : Except Error Word) (expected : Word) : Bool :=
  match operation with
  | .ok value => decide (value = expected)
  | .error _ => false

def withTicket (state : BorrowState) (operation : OS.Ownership.Mutation) :
    Except OS.Borrowing.Fault (BorrowState × Ticket) := do
  let (after, result) ← OS.Borrowing.mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw .missingLoan

def initial : BorrowState := OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty)

-- Independent expected byte order detects truncation even if a defective
-- encoder and decoder would otherwise cancel each other's mistakes. The
-- operand is deliberately unaligned and has mapped bytes on both sides.
def checkedBytes : Except OS.Borrowing.Fault
    (List (Option Byte) × Except Error Word × Except Error (BitVec 32) × Except Error (BitVec 32)) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 10⟩ readWrite)
  let (stored, _) ← OS.Borrowing.mutate owned (.store64 7 ticket 65537 0xfedcba9876543210)
  return ((List.range 10).map fun offset => (toMemory stored.resources.space).read (65536 + BitVec.ofNat 64 offset),
    loadQWord (toMemory stored.resources.space) 65537,
    loadDWord (toMemory stored.resources.space) 65537,
    loadDWord (toMemory stored.resources.space) 65541)

example : checkedBytes = .ok
    ([some 0, some 0x10, some 0x32, some 0x54, some 0x76, some 0x98,
      some 0xba, some 0xdc, some 0xfe, some 0],
      .ok 0xfedcba9876543210, .ok 0x76543210, .ok 0xfedcba98) := by rfl

-- Machine permissions alone admit this span, but neither adjacent allocation
-- authorizes all eight bytes, even with a shared owner.
def adjacent : Except OS.Ownership.Fault (Bool × Bool × Bool) := do
  let (left, a) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 4⟩ readWrite
  let (both, b) ← OS.Ownership.allocate left 7 ⟨65540, 4⟩ readWrite
  return (canStoreQWord (toMemory both.space) 65536,
    ownershipFailure (OS.Ownership.storeWord64 both 7 a 65536 0xfedcba9876543210) .outsideAllocation,
    ownershipFailure (OS.Ownership.storeWord64 both 7 b 65536 0xfedcba9876543210) .outsideAllocation)

example : adjacent = .ok (true, true, true) := by rfl

-- Every upper byte is independently denied, hidden, or removed. Checking only
-- the low dword (or only endpoints) would accept at least one of these stores.
def upperBytePreflight : Except OS.AddressSpace.Fault (List (Bool × Bool × Bool)) := do
  let mapped ← OS.AddressSpace.map OS.AddressSpace.empty ⟨65536, 8⟩ readWrite
  (List.range 4).mapM fun index => do
    let address : Word := 65540 + BitVec.ofNat 64 index
    let denied ← OS.AddressSpace.protect mapped ⟨address, 1⟩ readOnly
    let hidden ← OS.AddressSpace.protect mapped ⟨address, 1⟩ inaccessible
    let missing ← OS.AddressSpace.unmap mapped ⟨address, 1⟩
    return (spaceFailure (OS.AddressSpace.storeQWord denied 65536 0xfedcba9876543210) .denied,
      spaceFailure (OS.AddressSpace.storeQWord hidden 65536 0xfedcba9876543210) .denied,
      spaceFailure (OS.AddressSpace.storeQWord missing 65536 0xfedcba9876543210) .denied)

example : upperBytePreflight = .ok
    [(true, true, true), (true, true, true), (true, true, true), (true, true, true)] := by rfl

-- Transfers, including transfer back, revoke old epochs; releasing and
-- remapping the same address creates a distinct lifetime and ticket.
def staleTickets : Except OS.Ownership.Fault
    (List Bool × Except Error Word) := do
  let (owned, first) ← OS.Ownership.allocate (OS.Ownership.empty OS.AddressSpace.empty) 7 ⟨65536, 8⟩ readWrite
  let wrong := ownershipFailure (OS.Ownership.storeWord64 owned 8 first 65536 1) .wrongOwner
  let (other, handed) ← OS.Ownership.transfer owned 7 first 8
  let stale := ownershipFailure (OS.Ownership.storeWord64 other 7 first 65536 1) .staleEpoch
  let (back, current) ← OS.Ownership.transfer other 8 handed 7
  let staleBack := ownershipFailure (OS.Ownership.storeWord64 back 7 first 65536 1) .staleEpoch
  let released ← OS.Ownership.release back 7 current
  let absent := ownershipFailure (OS.Ownership.storeWord64 released 7 current 65536 1) .missingAllocation
  let (reused, fresh) ← OS.Ownership.allocate released 7 ⟨65536, 8⟩ readWrite
  let dead := ownershipFailure (OS.Ownership.storeWord64 reused 7 current 65536 1) .missingAllocation
  let stored ← OS.Ownership.storeWord64 reused 7 fresh 65536 0x89abcdef01234567
  return ([wrong, stale, staleBack, absent, dead], loadQWord (toMemory stored.space) 65536)

example : staleTickets = .ok ([true, true, true, true, true], .ok 0x89abcdef01234567) := by rfl

-- A two-byte loan is disjoint from the qword store operand. It must still
-- freeze the entire allocation; ending just one of two loans is insufficient.
def partialFreeze : Except OS.Borrowing.Fault
    (List Bool × Except Error Word × Except Error (BitVec 32)) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 16⟩ readWrite)
  let (populated, _) ← OS.Borrowing.mutate owned (.store 7 ticket 65548 0x12345678)
  let (first, a) ← OS.Borrowing.readBorrow populated 7 ticket 11 ⟨65548, 2⟩
  let (both, b) ← OS.Borrowing.readBorrow first 7 ticket 12 ⟨65550, 2⟩
  let blocked := borrowFailure (OS.Borrowing.mutate both (.store64 7 ticket 65536 1)) .borrowed
  let one ← OS.Borrowing.finishLoan both 11 a
  let stillBlocked := borrowFailure (OS.Borrowing.mutate one (.store64 7 ticket 65536 1)) .borrowed
  let ended ← OS.Borrowing.finishLoan one 12 b
  let (stored, _) ← OS.Borrowing.mutate ended (.store64 7 ticket 65536 0xfedcba9876543210)
  return ([blocked, stillBlocked], loadQWord (toMemory stored.resources.space) 65536,
    loadDWord (toMemory stored.resources.space) 65548)

example : partialFreeze = .ok ([true, true], .ok 0xfedcba9876543210, .ok 0x12345678) := by rfl

-- A successful qword mutation in another allocation must retain both narrow
-- and wide live reads, exact stored loan metadata, frontier and permissions.
def survivingLoans : Except OS.Borrowing.Fault
    (Except OS.Borrowing.ReadFault Word × Except OS.Borrowing.ReadFault (BitVec 32) × List Bool) := do
  let (first, a) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (both, b) ← withTicket first (.allocate 7 ⟨131072, 8⟩ readWrite)
  let (populated, _) ← OS.Borrowing.mutate both (.store64 7 a 65536 0x89abcdef01234567)
  let (readOnly, _) ← OS.Borrowing.mutate populated (.protect 7 a OS.AddressSpace.readOnly)
  let (wide, x) ← OS.Borrowing.readBorrow readOnly 7 a 11 ⟨65536, 8⟩
  let (borrowed, y) ← OS.Borrowing.readBorrow wide 7 a 12 ⟨65540, 4⟩
  let (stored, _) ← OS.Borrowing.mutate borrowed (.store64 7 b 131072 0xfedcba9876543210)
  return (OS.Borrowing.loadWord64 stored 11 x 65536, OS.Borrowing.loadWord stored 12 y 65540,
    [decide (stored.loans x = borrowed.loans x), decide (stored.loans y = borrowed.loans y),
      decide (stored.nextLoan = borrowed.nextLoan),
      decide (stored.resources.frontier = borrowed.resources.frontier),
      decide (stored.resources.allocations a.identifier = borrowed.resources.allocations a.identifier),
      decide (stored.resources.allocations b.identifier = borrowed.resources.allocations b.identifier),
      decide ((stored.resources.space.cells 65543).map Cell.permissions = some OS.AddressSpace.readOnly),
      decide ((stored.resources.space.cells 131079).map Cell.permissions = some readWrite),
      qwordIs (loadQWord (toMemory stored.resources.space) 131072) 0xfedcba9876543210])

example : survivingLoans = .ok
    (.ok 0x89abcdef01234567, .ok 0x89abcdef, [true, true, true, true, true, true, true, true, true]) := by rfl

-- Supplied bytes are independent of the qword encoder. Checked adoption and a
-- read-only loan must suffice for a full DATA read with nonzero high bits.
def literalSpace : Space where
  cells address :=
    match address.toNat with
    | 65536 => some ⟨0x10, readOnly⟩
    | 65537 => some ⟨0x32, readOnly⟩
    | 65538 => some ⟨0x54, readOnly⟩
    | 65539 => some ⟨0x76, readOnly⟩
    | 65540 => some ⟨0x98, readOnly⟩
    | 65541 => some ⟨0xba, readOnly⟩
    | 65542 => some ⟨0xdc, readOnly⟩
    | 65543 => some ⟨0xfe, readOnly⟩
    | _ => none

def readOnlyLifecycle : Except OS.Borrowing.Fault
    (Except OS.Borrowing.ReadFault Word × List Bool) := do
  let (owned, ticket) ← withTicket (OS.Borrowing.empty (OS.Ownership.empty literalSpace))
    (.adopt 7 ⟨65536, 8⟩)
  let (first, retired) ← OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65536, 8⟩
  let loaded := OS.Borrowing.loadWord64 first 11 retired 65536
  let wrong := readFailure (OS.Borrowing.loadWord64 first 12 retired 65536) (.authority .wrongBorrower)
  let crosses := readFailure (OS.Borrowing.loadWord64 first 11 retired 65537) .outsideLoan
  let ended ← OS.Borrowing.finishLoan first 11 retired
  let absent := readFailure (OS.Borrowing.loadWord64 ended 11 retired 65536) (.authority .missingLoan)
  let (later, current) ← OS.Borrowing.readBorrow ended 7 ticket 11 ⟨65536, 8⟩
  let dead := readFailure (OS.Borrowing.loadWord64 later 11 retired 65536) (.authority .missingLoan)
  let blocked := borrowFailure (OS.Borrowing.mutate later (.store64 7 ticket 65536 0)) .borrowed
  let finished ← OS.Borrowing.finishLoan later 11 current
  let denied := borrowFailure (OS.Borrowing.mutate finished (.store64 7 ticket 65536 0))
    (.ownership (.addressSpace .denied))
  return (loaded, [wrong, crosses, absent, dead, blocked, denied])

example : readOnlyLifecycle = .ok (.ok 0xfedcba9876543210, [true, true, true, true, true, true]) := by rfl

def literalOwned : World :=
  OS.Ownership.install (OS.Ownership.empty literalSpace) literalSpace 7 ⟨65536, 8⟩

theorem literal_adopted :
    OS.Ownership.adopt (OS.Ownership.empty literalSpace) 7 ⟨65536, 8⟩ =
      .ok (literalOwned, ⟨0, 0⟩) := by rfl

theorem literal_owned_valid : OS.Ownership.WellFormed literalOwned :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) literal_adopted).1

def literalLoan : OS.Borrowing.Loan := ⟨⟨0, 0⟩, 7, 11, ⟨65536, 8⟩⟩

def literalBorrowed : BorrowState :=
  OS.Borrowing.installLoan (OS.Borrowing.empty literalOwned) literalLoan

theorem literal_borrowed :
    OS.Borrowing.readBorrow (OS.Borrowing.empty literalOwned) 7 ⟨0, 0⟩ 11 ⟨65536, 8⟩ =
      .ok (literalBorrowed, 0) := by rfl

theorem literal_valid : OS.Borrowing.WellFormed literalBorrowed :=
  (OS.Borrowing.readBorrow_wellFormed _ _ _ _ _ _
    (OS.Borrowing.empty_wellFormed _ literal_owned_valid) literal_borrowed).1

-- Every admitted history includes the newly checked 64-bit mutation case.
-- The old narrow read must remain stable through exactly the same history.
theorem all_histories_wide (after : BorrowState)
    (history : OS.Borrowing.History literalBorrowed after)
    (survives : (after.loans 0).isSome = true) :
    OS.Borrowing.loadWord64 after 11 0 65536 = .ok 0xfedcba9876543210 :=
  history.loadWord64_stable literal_valid 11 0 65536 _ (by rfl) survives

theorem all_histories_narrow (after : BorrowState)
    (history : OS.Borrowing.History literalBorrowed after)
    (survives : (after.loans 0).isSome = true) :
    OS.Borrowing.loadWord after 11 0 65540 = .ok 0xfedcba98 :=
  history.loadWord_stable literal_valid 11 0 65540 _ (by rfl) survives

theorem all_histories_retired (middle after : BorrowState)
    (finished : OS.Borrowing.finishLoan literalBorrowed 11 0 = .ok middle)
    (history : OS.Borrowing.History middle after) :
    OS.Borrowing.loadWord64 after 11 0 65536 = .error (.authority .missingLoan) :=
  (OS.Borrowing.finished_for_history 11 0 literal_valid finished history).loadWord64_denied 11 65536

end EDSL.Tests.Ownership64

#audit_edsl
