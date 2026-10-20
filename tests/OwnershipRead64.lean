/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.OwnedRead64
import EDSL.OS.Borrowing.Read64
import EDSL.X86.Machine
import EDSL.Audit

namespace EDSL.Tests.OwnershipRead64
open X86 OS OS.AddressSpace

abbrev OwnedRead := Except Ownership.ReadFault Word
abbrev BorrowState := Borrowing.State

-- Literal input is independent of the store encoder, unaligned, and in the
-- upper canonical half. A readable ninth byte must not extend ownership.
def literalSpace : Space where
  cells address :=
    match address.toNat with
    | 0xffff800000010001 => some ⟨0x10, readOnly⟩
    | 0xffff800000010002 => some ⟨0x32, readOnly⟩
    | 0xffff800000010003 => some ⟨0x54, readOnly⟩
    | 0xffff800000010004 => some ⟨0x76, readOnly⟩
    | 0xffff800000010005 => some ⟨0x98, readOnly⟩
    | 0xffff800000010006 => some ⟨0xba, readOnly⟩
    | 0xffff800000010007 => some ⟨0xdc, readOnly⟩
    | 0xffff800000010008 => some ⟨0xfe, readOnly⟩
    | 0xffff800000010009 => some ⟨0xaa, readOnly⟩
    | 0x10000 => some ⟨0xc3, readExecute⟩
    | 0x20000 => some ⟨0xef, readOnly⟩
    | 0x20001 => some ⟨0xcd, readOnly⟩
    | 0x20002 => some ⟨0xab, readOnly⟩
    | 0x20003 => some ⟨0x89, readOnly⟩
    | 0x20004 => some ⟨0x67, readOnly⟩
    | 0x20005 => some ⟨0x45, readOnly⟩
    | 0x20006 => some ⟨0x23, readOnly⟩
    | 0x20007 => some ⟨0x01, readOnly⟩
    | _ => none

def address : Word := 0xffff800000010001

def ownerLifecycle : Except Ownership.Fault (List OwnedRead × Except Error Word) := do
  let (owned, first) ← Ownership.adopt (Ownership.empty literalSpace) 7 ⟨address, 8⟩
  let original := Ownership.loadWord64 owned 7 first address
  let wrong := Ownership.loadWord64 owned 8 first address
  let (other, handed) ← Ownership.transfer owned 7 first 8
  let stale := Ownership.loadWord64 other 7 first address
  let current := Ownership.loadWord64 other 8 handed address
  let wrongCurrent := Ownership.loadWord64 other 7 handed address
  let (back, ticket) ← Ownership.transfer other 8 handed 7
  let staleBack := Ownership.loadWord64 back 7 first address
  let hidden ← Ownership.protect back 7 ticket inaccessible
  let revoked := Ownership.loadWord64 hidden 7 ticket address
  let restored ← Ownership.protect hidden 7 ticket readOnly
  let readable := Ownership.loadWord64 restored 7 ticket address
  let released ← Ownership.release restored 7 ticket
  let missing := Ownership.loadWord64 released 7 ticket address
  let (reused, fresh) ← Ownership.allocate released 7 ⟨address, 8⟩ readWrite
  let populated ← Ownership.storeWord64 reused 7 fresh address 0x89abcdef01234567
  return ([original, wrong, stale, current, wrongCurrent, staleBack, revoked, readable,
    missing, Ownership.loadWord64 populated 7 ticket address,
    Ownership.loadWord64 populated 7 fresh address], readWord (toMemory populated.space) address)

-- Revocation reports a CPU fault despite valid owner/epoch. Transfer and reuse
-- reject stale authority even when the bytes are currently readable again.
example : ownerLifecycle = .ok
    ([.ok 0xfedcba9876543210, .error (.authority .wrongOwner),
      .error (.authority .staleEpoch), .ok 0xfedcba9876543210,
      .error (.authority .wrongOwner), .error (.authority .staleEpoch),
      .error (.machine (.inaccessibleData address)), .ok 0xfedcba9876543210,
      .error (.authority .missingAllocation), .error (.authority .missingAllocation),
      .ok 0x89abcdef01234567], .ok 0x89abcdef01234567) := by rfl

def onlySeven : Except Ownership.Fault (OwnedRead × Except Error Word) := do
  let (owned, ticket) ← Ownership.adopt (Ownership.empty literalSpace) 7 ⟨address, 7⟩
  return (Ownership.loadWord64 owned 7 ticket address, loadQWord (toMemory owned.space) address)

example : onlySeven = .ok (.error .outsideAllocation, .ok 0xfedcba9876543210) := by rfl

def shiftedOutside : Except Ownership.Fault (OwnedRead × Except Error Word) := do
  let (owned, ticket) ← Ownership.adopt (Ownership.empty literalSpace) 7 ⟨address, 8⟩
  return (Ownership.loadWord64 owned 7 ticket (address + 1),
    readWord (toMemory owned.space) (address + 1))

example : shiftedOutside = .ok (.error .outsideAllocation, .ok 0xaafedcba98765432) := by rfl

def withTicket (state : BorrowState) (operation : Ownership.Mutation) :
    Except Borrowing.Fault (BorrowState × Ownership.Ticket) := do
  let (after, issued) ← Borrowing.mutate state operation
  match issued with
  | some ticket => return (after, ticket)
  | none => throw .missingLoan

def failedWith {ε α : Type} [DecidableEq ε] (result : Except ε α) (fault : ε) : Bool :=
  match result with
  | .error actual => decide (actual = fault)
  | .ok _ => false

-- The live loan covers the other slot, but freezes this entire allocation.
-- Owned reads coexist with it; mutation needs its real successful finish.
def activeLoan : Except Borrowing.Fault (OwnedRead × Bool × OwnedRead) := do
  let (owned, ticket) ← withTicket (Borrowing.empty (Ownership.empty AddressSpace.empty))
    (.allocate 7 ⟨0xffff800000020001, 16⟩ readWrite)
  let (stored, _) ← Borrowing.mutate owned (.store64 7 ticket 0xffff800000020001 0xfedcba9876543210)
  let (borrowed, loan) ← Borrowing.readBorrow stored 7 ticket 11 ⟨0xffff800000020009, 8⟩
  let observed := Borrowing.loadOwnedWord64 borrowed 7 ticket 0xffff800000020001
  let blocked := failedWith
    (Borrowing.mutate borrowed (.store64 7 ticket 0xffff800000020001 0)) .borrowed
  let ended ← Borrowing.finishLoan borrowed 11 loan
  let (updated, _) ← Borrowing.mutate ended (.store64 7 ticket 0xffff800000020001 0x89abcdef01234567)
  return (observed, blocked, Borrowing.loadOwnedWord64 updated 7 ticket 0xffff800000020001)

example : activeLoan = .ok (.ok 0xfedcba9876543210, true, .ok 0x89abcdef01234567) := by rfl

def retObservation (state : X86.State) : Except Error (Word × Word) := do
  match ← X86.step state with
  | .returned final => return (final.rip, final.registers .rsp)
  | _ => throw .unexpectedReturn

-- Two stores in one frame remain enabled around owned reads. Live code and
-- original caller loans survive; the first slot is checked with actual
-- readWord and a decoded c3, rather than a stored witness's assigned value.
def stackSlots : Except Borrowing.Fault
    (OwnedRead × Except Error Word × OwnedRead × Except Borrowing.ReadFault Word ×
      Except Error Byte × Except Error (Word × Word)) := do
  let initial := Borrowing.empty (Ownership.empty literalSpace)
  let (code, codeTicket) ← withTicket initial (.adopt 7 ⟨0x10000, 1⟩)
  let (caller, callerTicket) ← withTicket code (.adopt 7 ⟨0x20000, 8⟩)
  let (codeLoan, _) ← Borrowing.readBorrow caller 7 codeTicket 11 ⟨0x10000, 1⟩
  let (callerLoan, callerId) ← Borrowing.readBorrow codeLoan 7 callerTicket 12 ⟨0x20000, 8⟩
  let (frame, frameTicket) ← withTicket callerLoan (.allocate 7 ⟨0xffff800000020001, 16⟩ readWrite)
  let (first, _) ← Borrowing.mutate frame
    (.store64 7 frameTicket 0xffff800000020001 0xffff800000003333)
  let firstRead := Borrowing.loadOwnedWord64 first 7 frameTicket 0xffff800000020001
  let (second, _) ← Borrowing.mutate first
    (.store64 7 frameTicket 0xffff800000020009 0x89abcdef01234567)
  let memory := toMemory second.resources.space
  let cpu : X86.State :=
    { registers := fun r => if r = .rsp then 0xffff800000020001 else 0
      rip := 0x10000
      flags := 0
      memory := memory }
  return (firstRead, readWord memory 0xffff800000020001,
    Borrowing.loadOwnedWord64 second 7 frameTicket 0xffff800000020009,
    Borrowing.loadWord64 second 12 callerId 0x20000, fetchByte memory 0x10000,
    retObservation cpu)

example : stackSlots = .ok (.ok 0xffff800000003333, .ok 0xffff800000003333,
    .ok 0x89abcdef01234567, .ok 0x0123456789abcdef, .ok 0xc3,
    .ok (0xffff800000003333, 0xffff800000020009)) := by rfl


end EDSL.Tests.OwnershipRead64

#print axioms EDSL.X86.loadQWord_readWord_success_iff
#print axioms EDSL.OS.Ownership.loadWord64_success_iff
#print axioms EDSL.OS.Ownership.loadWord64_exists
#print axioms EDSL.OS.Ownership.loadWord64_readWord
#print axioms EDSL.OS.Borrowing.loadOwnedWord64_success_iff
#print axioms EDSL.OS.Borrowing.store64_owned_readback
#print axioms EDSL.OS.Borrowing.store64_readWord
#print axioms EDSL.OS.Borrowing.store64_preserves_owned_read
#audit_edsl
