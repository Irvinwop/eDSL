/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Read
import EDSL.Examples.Compiler.MemoryWitness
import EDSL.Audit

namespace EDSL.Tests.Borrowing
open X86 OS.AddressSpace

abbrev BorrowState := OS.Borrowing.State
abbrev Fault := OS.Borrowing.Fault
abbrev Ticket := OS.Ownership.Ticket

def failureIs {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

-- Allocation and transfer must return usable authority, rather than merely
-- reporting a successful resource update with no ticket.
def withTicket (state : BorrowState) (operation : OS.Ownership.Mutation) :
    Except Fault (BorrowState × Ticket) := do
  let (after, result) ← OS.Borrowing.mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw .missingLoan

def initial : BorrowState := OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty)

-- A subregion loan freezes the whole allocation, including another writable
-- word. Self-transfer is also forbidden: it would revoke the lender's epoch.
def blockedMutations (state : BorrowState) (ticket : Ticket) : List Bool :=
  [failureIs (OS.Borrowing.mutate state (.store 7 ticket 65540 0xaabbccdd)) .borrowed,
    failureIs (OS.Borrowing.mutate state (.protect 7 ticket readOnly)) .borrowed,
    failureIs (OS.Borrowing.mutate state (.release 7 ticket)) .borrowed,
    failureIs (OS.Borrowing.mutate state (.transfer 7 ticket 9)) .borrowed,
    failureIs (OS.Borrowing.mutate state (.transfer 7 ticket 7)) .borrowed]

-- The two loans overlap and name different borrowers. Ending the older one
-- must leave the newest live scan entry blocking every mutation kind.
def sharedReadLifecycle :
    Except Fault (List Bool × Except Error (BitVec 32) × Except Error (BitVec 32)) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (populated, _) ← OS.Borrowing.mutate owned (.store 7 ticket 65536 0x11223344)
  let (first, a) ← OS.Borrowing.readBorrow populated 7 ticket 11 ⟨65536, 4⟩
  let (both, b) ← OS.Borrowing.readBorrow first 7 ticket 12 ⟨65538, 2⟩
  let checksBefore := blockedMutations both ticket
  let last ← OS.Borrowing.finishLoan both 11 a
  let checksLast := blockedMutations last ticket
  let wrongFinisher := failureIs (OS.Borrowing.finishLoan last 11 b) .wrongBorrower
  let wrongReader := failureIs (OS.Borrowing.authorize last 11 b) .wrongBorrower
  let finished ← OS.Borrowing.finishLoan last 12 b
  let (changed, _) ← OS.Borrowing.mutate finished (.store 7 ticket 65540 0xaabbccdd)
  let (readable, _) ← OS.Borrowing.mutate changed (.protect 7 ticket readOnly)
  return (checksBefore ++ checksLast ++ [wrongFinisher, wrongReader],
    loadDWord (toMemory readable.resources.space) 65536,
    loadDWord (toMemory readable.resources.space) 65540)

example : sharedReadLifecycle = .ok
    ([true, true, true, true, true, true, true, true, true, true, true, true],
      .ok 0x11223344, .ok 0xaabbccdd) := by rfl

-- A later issuance must not make a finished ID usable again, even when the
-- borrower is the same. Stale completion cannot end the replacement loan.
def retiredIdentifiers : Except Fault (List Bool × Except Error (BitVec 32)) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (borrowed, retired) ← OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65536, 4⟩
  let ended ← OS.Borrowing.finishLoan borrowed 11 retired
  let doubleFinish := failureIs (OS.Borrowing.finishLoan ended 11 retired) .missingLoan
  let (later, current) ← OS.Borrowing.readBorrow ended 7 ticket 11 ⟨65536, 4⟩
  let staleRead := failureIs (OS.Borrowing.authorize later 11 retired) .missingLoan
  let staleFinish := failureIs (OS.Borrowing.finishLoan later 11 retired) .missingLoan
  let stillBorrowed := failureIs (OS.Borrowing.mutate later (.store 7 ticket 65536 1)) .borrowed
  let finished ← OS.Borrowing.finishLoan later 11 current
  let (stored, _) ← OS.Borrowing.mutate finished (.store 7 ticket 65536 0x89abcdef)
  return ([doubleFinish, staleRead, staleFinish, stillBorrowed],
    loadDWord (toMemory stored.resources.space) 65536)

example : retiredIdentifiers = .ok ([true, true, true, true], .ok 0x89abcdef) := by rfl

-- Unregistered backing is prepared before the borrowing discipline starts.
-- During the loan, every managed operation kind succeeds on separate regions.
def disjointChanges :
    Except Fault (List Bool × Except Error (BitVec 32) × Except Error (BitVec 32)) := do
  let backing ← (OS.AddressSpace.map OS.AddressSpace.empty ⟨196608, 4⟩ readWrite).mapError
    (fun fault => OS.Borrowing.Fault.ownership (.addressSpace fault))
  let start := OS.Borrowing.empty (OS.Ownership.empty backing)
  let (first, a) ← withTicket start (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (populated, _) ← OS.Borrowing.mutate first (.store 7 a 65536 0x12345678)
  let (borrowed, loan) ← OS.Borrowing.readBorrow populated 7 a 11 ⟨65536, 4⟩
  let (both, b) ← withTicket borrowed (.allocate 7 ⟨131072, 4⟩ readWrite)
  let (adopted, c) ← withTicket both (.adopt 7 ⟨196608, 4⟩)
  let (stored, _) ← OS.Borrowing.mutate adopted (.store 7 b 131072 0x11223344)
  let (readonly, _) ← OS.Borrowing.mutate stored (.protect 7 b readOnly)
  let (transferred, handed) ← withTicket readonly (.transfer 7 b 9)
  let staleOwner := failureIs (OS.Borrowing.mutate transferred (.release 7 b))
    (.ownership .staleEpoch)
  let denied := failureIs (OS.Borrowing.mutate transferred (.store 9 handed 131072 0))
    (.ownership (.addressSpace .denied))
  let (released, _) ← OS.Borrowing.mutate transferred (.release 9 handed)
  let (reused, fresh) ← withTicket released (.allocate 9 ⟨131072, 4⟩ readWrite)
  let (rewritten, _) ← OS.Borrowing.mutate reused (.store 9 fresh 131072 0x89abcdef)
  let (adoptedStored, _) ← OS.Borrowing.mutate rewritten (.store 7 c 196608 0xaabbccdd)
  let remainsLive := failureIs (OS.Borrowing.mutate adoptedStored (.release 7 a)) .borrowed
  let ended ← OS.Borrowing.finishLoan adoptedStored 11 loan
  let (finished, _) ← OS.Borrowing.mutate ended (.release 7 a)
  return ([staleOwner, denied, remainsLive,
      failureIs (OS.Borrowing.mutate finished (.release 7 a)) (.ownership .missingAllocation),
      decide ((toMemory adoptedStored.resources.space).read 65536 = some 0x78),
      decide ((toMemory finished.resources.space).read 65536 = none)],
    loadDWord (toMemory adoptedStored.resources.space) 65536,
    loadDWord (toMemory finished.resources.space) 196608)

example : disjointChanges = .ok
    ([true, true, true, true, true, true], .ok 0x12345678, .ok 0xaabbccdd) := by rfl

-- Interval validation must reject empty, noncanonical and wrapping ranges;
-- containment must check both ends, and owner/epoch checks remain necessary.
def rejectedBorrowRanges : Except Fault (List Bool) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let checks :=
    [failureIs (OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65536, 0⟩) .invalidRegion,
      failureIs (OS.Borrowing.readBorrow owned 7 ticket 11 ⟨0x0000800000000000, 1⟩) .invalidRegion,
      failureIs (OS.Borrowing.readBorrow owned 7 ticket 11 ⟨0xffffffffffffffff, 2⟩) .invalidRegion,
      failureIs (OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65535, 2⟩) .outsideAllocation,
      failureIs (OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65543, 2⟩) .outsideAllocation,
      failureIs (OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65536, 9⟩) .outsideAllocation,
      failureIs (OS.Borrowing.readBorrow owned 8 ticket 11 ⟨65536, 4⟩) (.ownership .wrongOwner),
      failureIs (OS.Borrowing.readBorrow owned 7 ⟨99, 0⟩ 11 ⟨65536, 4⟩)
        (.ownership .missingAllocation)]
  let (transferred, _) ← withTicket owned (.transfer 7 ticket 9)
  return checks ++ [failureIs (OS.Borrowing.readBorrow transferred 7 ticket 11 ⟨65536, 4⟩)
    (.ownership .staleEpoch)]

example : rejectedBorrowRanges = .ok [true, true, true, true, true, true, true, true, true] := by rfl

-- Adoption may include hidden cells. A readable prefix can be borrowed, but
-- the unreadable final cell must reject a loan of the complete allocation.
def unreadableTail : Except Fault (List Bool × Except Error (BitVec 32)) := do
  let mapped ← (OS.AddressSpace.map OS.AddressSpace.empty ⟨65536, 8⟩ readWrite).mapError
    (fun fault => OS.Borrowing.Fault.ownership (.addressSpace fault))
  let populated ← (OS.AddressSpace.storeWord mapped 65536 0x89abcdef).mapError
    (fun fault => OS.Borrowing.Fault.ownership (.addressSpace fault))
  let hidden ← (OS.AddressSpace.protect populated ⟨65543, 1⟩ inaccessible).mapError
    (fun fault => OS.Borrowing.Fault.ownership (.addressSpace fault))
  let (owned, ticket) ← withTicket (OS.Borrowing.empty (OS.Ownership.empty hidden))
    (.adopt 7 ⟨65536, 8⟩)
  let (readablePrefix, _) ← OS.Borrowing.readBorrow owned 7 ticket 11 ⟨65536, 7⟩
  return ([failureIs (OS.Borrowing.readBorrow readablePrefix 7 ticket 12 ⟨65536, 8⟩) .unreadable,
      failureIs (OS.Borrowing.readBorrow readablePrefix 7 ticket 12 ⟨65543, 1⟩) .unreadable,
      decide ((toMemory readablePrefix.resources.space).read 65543 = none)],
    loadDWord (toMemory readablePrefix.resources.space) 65536)

example : unreadableTail = .ok ([true, true, true], .ok 0x89abcdef) := by rfl

def readFailureIs (operation : Except OS.Borrowing.ReadFault (BitVec 32))
    (expected : OS.Borrowing.ReadFault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

-- Authority is checked from stored borrower records and the entire operand
-- must fit the loan even when all neighboring bytes are readable/writable.
def checkedReadBoundaries : Except Fault (Except OS.Borrowing.ReadFault (BitVec 32) × List Bool) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (populated, _) ← OS.Borrowing.mutate owned (.store 7 ticket 65536 0x89abcdef)
  let (first, a) ← OS.Borrowing.readBorrow populated 7 ticket 11 ⟨65536, 4⟩
  let (both, b) ← OS.Borrowing.readBorrow first 7 ticket 12 ⟨65536, 2⟩
  let checks :=
    [readFailureIs (OS.Borrowing.loadWord both 12 a 65536) (.authority .wrongBorrower),
      readFailureIs (OS.Borrowing.loadWord both 12 b 65536) .outsideLoan,
      readFailureIs (OS.Borrowing.loadWord both 11 a 65537) .outsideLoan]
  let ended ← OS.Borrowing.finishLoan both 11 a
  return (OS.Borrowing.loadWord both 11 a 65536,
    checks ++ [readFailureIs (OS.Borrowing.loadWord ended 11 a 65536) (.authority .missingLoan)])

example : checkedReadBoundaries = .ok (.ok 0x89abcdef, [true, true, true, true]) := by rfl

-- An adopted caller space, borrowed through the checked API, witnesses every
-- possible loaded word with the actual compiler bytes and return stack.
open Examples.Compiler.MemoryOps

def caller (value : BitVec 32) : Space where
  cells address := ((dataMemory 0x8b 0x07 value).read address).map fun byte =>
    ⟨byte, ⟨true, (dataMemory 0x8b 0x07 value).writable address,
      (dataMemory 0x8b 0x07 value).executable address⟩⟩

theorem caller_reads (value : BitVec 32) (address : Word) :
    (toMemory (caller value)).read address = (dataMemory 0x8b 0x07 value).read address := by
  simp only [toMemory, caller]
  cases (dataMemory 0x8b 0x07 value).read address <;> rfl

def owned (value : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (caller value)) (caller value) 7 ⟨65536, 4⟩

theorem adopted (value : BitVec 32) :
    OS.Ownership.adopt (OS.Ownership.empty (caller value)) 7 ⟨65536, 4⟩ = .ok (owned value, ⟨0, 0⟩) := by
  apply OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) ?_ (by rfl)
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨offset, bound, same⟩ := List.mem_map.mp member
  have small : offset < 4 := List.mem_range.mp bound
  subst address
  match offset with
  | 0 | 1 | 2 | 3 => rfl
  | offset + 4 => omega

def loan : OS.Borrowing.Loan := ⟨⟨0, 0⟩, 7, 11, ⟨65536, 4⟩⟩

def borrowed (value : BitVec 32) : BorrowState :=
  OS.Borrowing.installLoan (OS.Borrowing.empty (owned value)) loan

theorem loan_issued (value : BitVec 32) :
    OS.Borrowing.readBorrow (OS.Borrowing.empty (owned value)) 7 ⟨0, 0⟩ 11 ⟨65536, 4⟩ =
      .ok (borrowed value, 0) := by
  apply OS.Borrowing.readBorrow_success _ _ _ _ _ ⟨7, 0, ⟨65536, 4⟩⟩
    (OS.Borrowing.empty_wellFormed _ ((OS.Ownership.adopt_wellFormed _ _ _ _
      (OS.Ownership.empty_wellFormed _) (adopted value)).1)) (by rfl) (by decide) (by decide)
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨offset, bound, same⟩ := List.mem_map.mp member
  have small : offset < 4 := List.mem_range.mp bound
  subst address
  match offset with
  | 0 | 1 | 2 | 3 => rfl
  | offset + 4 => omega

theorem borrowed_valid (value : BitVec 32) : OS.Borrowing.WellFormed (borrowed value) :=
  (OS.Borrowing.readBorrow_wellFormed _ _ _ _ _ _
    (OS.Borrowing.empty_wellFormed _ ((OS.Ownership.adopt_wellFormed _ _ _ _
      (OS.Ownership.empty_wellFormed _) (adopted value)).1)) (loan_issued value)).1

theorem checked_read (value : BitVec 32) :
    OS.Borrowing.loadWord (borrowed value) 11 0 65536 = .ok value := by
  apply OS.Borrowing.loadWord_success _ _ _ _ _ loan (by rfl) (by decide)
  exact (loadDWord_congr _ _ _ (fun _ _ => caller_reads value _)).trans (data_value _ _ _)

theorem caller_code (value : BitVec 32) : CodeAt (toMemory (caller value)) 4096 loadBytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  match offset with
  | 0 | 1 | 2 =>
    simp [loadBytes] at present
    subst byte
    rfl
  | offset + 3 => simp [loadBytes] at present

def binaryEntry (value : BitVec 32) : X86.State :=
  { loadEntry value with memory := toMemory (caller value) }

theorem all_values_borrowed_binary (value : BitVec 32) :
    Executes (binaryEntry value) (loadFinal (binaryEntry value) value 8192) 2 := by
  exact (OS.Borrowing.borrowed_load32_correct (borrowed value) 11 0 (loadEntry value) value 8192
    (borrowed_valid value) (checked_read value) (caller_code value)
    ((readWord_congr _ _ _ (fun _ _ => caller_reads value _)).trans (data_stack _ _ _))
    (by decide)).2.1

-- This quantifies every admitted finite history, rather than testing a copied
-- snapshot or one hand-picked path. Ending/reissuing the ID cannot satisfy liveness.
theorem all_values_surviving_read (value : BitVec 32) (after : BorrowState)
    (history : OS.Borrowing.History (borrowed value) after)
    (survives : (after.loans 0).isSome = true) :
    OS.Borrowing.loadWord after 11 0 65536 = .ok value :=
  history.loadWord_stable (borrowed_valid value) 11 0 65536 value (checked_read value) survives

end EDSL.Tests.Borrowing

#audit_edsl
