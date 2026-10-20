/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicExchange
import EDSL.Audit

namespace EDSL.Tests.OSAtomicExchange
open X86 OS.AddressSpace

abbrev ExchangeFault := OS.AtomicExchange.Fault
abbrev BorrowState := OS.Borrowing.State
abbrev Ticket := OS.Ownership.Ticket

def failureIs {α : Type} (operation : Except ExchangeFault α) (expected : ExchangeFault) : Bool :=
  match operation with
  | .error observed => decide (observed = expected)
  | .ok _ => false

def mutate (state : BorrowState) (operation : OS.Ownership.Mutation) :
    Except ExchangeFault (BorrowState × Option Ticket) :=
  (OS.Borrowing.mutate state operation).mapError .authority

def withTicket (state : BorrowState) (operation : OS.Ownership.Mutation) :
    Except ExchangeFault (BorrowState × Ticket) := do
  let (after, result) ← mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw (.authority .missingLoan)

def initial : BorrowState := OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty)

-- Each old result must come from the current cells. The second exchange must
-- observe the first replacement; the neighboring word and permissions survive.
def chainedExchanges : Except ExchangeFault
    (BitVec 32 × BitVec 32 × Except Error (BitVec 32) × Except Error (BitVec 32) × List Bool) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (populated, _) ← mutate owned (.store 7 ticket 65536 0x11223344)
  let (guarded, _) ← mutate populated (.store 7 ticket 65540 0xa5b6c7d8)
  let (first, oldA) ← OS.AtomicExchange.exchangeWord guarded 7 ticket 65536 0x89abcdef
  let (last, oldB) ← OS.AtomicExchange.exchangeWord first 7 ticket 65536 0x76543210
  return (oldA, oldB, loadDWord (toMemory last.resources.space) 65536,
    loadDWord (toMemory last.resources.space) 65540,
    [((last.resources.space.cells 65536).map (·.permissions.readable)).getD false,
      ((last.resources.space.cells 65539).map (·.permissions.writable)).getD false])

example : chainedExchanges = .ok
    (0x11223344, 0x89abcdef, .ok 0x76543210, .ok 0xa5b6c7d8, [true, true]) := by rfl

-- A loan of only the upper word freezes the lower atomic word too. Finishing
-- one of two loans cannot bypass the remaining scan entry. A separate
-- allocation remains exchangeable, and loan completion re-enables mutation.
def readerExclusion : Except ExchangeFault
    (List Bool × BitVec 32 × BitVec 32 × Except Error (BitVec 32)) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (populated, _) ← mutate owned (.store 7 ticket 65536 0x11223344)
  let (first, a) ← (OS.Borrowing.readBorrow populated 7 ticket 11 ⟨65540, 4⟩).mapError .authority
  let (both, b) ← (OS.Borrowing.readBorrow first 7 ticket 12 ⟨65540, 1⟩).mapError .authority
  let bothBlocked := failureIs (OS.AtomicExchange.exchangeWord both 7 ticket 65536 0)
    (.authority .borrowed)
  let last ← (OS.Borrowing.finishLoan both 11 a).mapError .authority
  let lastBlocked := failureIs (OS.AtomicExchange.exchangeWord last 7 ticket 65536 0)
    (.authority .borrowed)
  let (other, separate) ← withTicket last (.allocate 7 ⟨131072, 4⟩ readWrite)
  let (changed, otherOld) ← OS.AtomicExchange.exchangeWord other 7 separate 131072 0xdeadbeef
  let finished ← (OS.Borrowing.finishLoan changed 12 b).mapError .authority
  let (exchanged, old) ← OS.AtomicExchange.exchangeWord finished 7 ticket 65536 0x89abcdef
  return ([bothBlocked, lastBlocked], otherOld, old,
    loadDWord (toMemory exchanged.resources.space) 131072)

example : readerExclusion = .ok ([true, true], 0, 0x11223344, .ok 0xdeadbeef) := by rfl

-- Ownership remains necessary even for writable coherent RAM. Self-transfer
-- revokes the old epoch, so stale tickets do not regain authority by keeping
-- the same owner number. Failed attempts must not yield a successful RMW.
def authorityChecks : Except ExchangeFault (List Bool × BitVec 32 × Except Error (BitVec 32)) := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (populated, _) ← mutate owned (.store 7 ticket 65536 0x12345678)
  let checks :=
    [failureIs (OS.AtomicExchange.exchangeWord populated 8 ticket 65536 0)
      (.authority (.ownership .wrongOwner)),
     failureIs (OS.AtomicExchange.exchangeWord populated 7 ticket 65544 0)
      (.authority (.ownership .outsideAllocation)),
     failureIs (OS.AtomicExchange.exchangeWord populated 7 ⟨99, 0⟩ 65536 0)
      (.authority (.ownership .missingAllocation))]
  let (transferred, renewed) ← withTicket populated (.transfer 7 ticket 7)
  let stale := failureIs (OS.AtomicExchange.exchangeWord transferred 7 ticket 65536 0)
    (.authority (.ownership .staleEpoch))
  let (changed, old) ← OS.AtomicExchange.exchangeWord transferred 7 renewed 65536 0xaabbccdd
  return (checks ++ [stale], old, loadDWord (toMemory changed.resources.space) 65536)

example : authorityChecks = .ok ([true, true, true, true], 0x12345678, .ok 0xaabbccdd) := by rfl

-- The ordinary authority/store gate would accept this entire unaligned word.
-- The atomic profile must still reject it and produce no successor or event.
def unsupportedAtomicOperand : Except ExchangeFault Bool := do
  let (owned, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  return failureIs (OS.AtomicExchange.exchangeWord owned 7 ticket 65537 0xaabbccdd)
    (.machine (.unsupportedAtomicAddress 65537))

example : unsupportedAtomicOperand = .ok true := by rfl

-- A final-byte permission failure must stop the complete operation. Adoption
-- retains the independently configured byte permissions instead of replacing
-- the tail with an all-writable allocation fixture.
def deniedTail : Except ExchangeFault Bool := do
  let mapped ← (OS.AddressSpace.map OS.AddressSpace.empty ⟨65536, 4⟩ readWrite).mapError
    (fun fault => OS.AtomicExchange.Fault.authority (.ownership (.addressSpace fault)))
  let narrowed ← (OS.AddressSpace.protect mapped ⟨65539, 1⟩ readOnly).mapError
    (fun fault => OS.AtomicExchange.Fault.authority (.ownership (.addressSpace fault)))
  let (owned, ticket) ← withTicket (OS.Borrowing.empty (OS.Ownership.empty narrowed))
    (.adopt 7 ⟨65536, 4⟩)
  return failureIs (OS.AtomicExchange.exchangeWord owned 7 ticket 65536 0xaabbccdd)
    (.authority (.ownership (.addressSpace .denied)))

example : deniedTail = .ok true := by rfl

-- The history theorem quantifies all admitted schedules and words. Its result
-- must connect adjacent events, rather than merely independently reporting a
-- successful swap for each event.
theorem adjacent_old_matches_new {before middle after : BorrowState}
    {ownerA ownerB : Nat} {ticketA ticketB : Ticket} {address : Word}
    {oldA oldB valueA valueB : BitVec 32}
    (first : OS.AtomicExchange.exchangeWord before ownerA ticketA address valueA = .ok (middle, oldA))
    (second : OS.AtomicExchange.exchangeWord middle ownerB ticketB address valueB = .ok (after, oldB)) :
    oldB = valueA := by
  have written := (OS.AtomicExchange.exchangeWord_sound _ _ _ _ _ _ first).readback
  have read := (OS.AtomicExchange.exchangeWord_sound _ _ _ _ _ _ second).2.2.1
  exact Except.ok.inj (read.symm.trans written)

end EDSL.Tests.OSAtomicExchange

#audit_edsl
