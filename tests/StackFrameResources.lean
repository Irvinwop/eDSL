/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame
import EDSL.OS.Borrowing.Read64
import EDSL.Audit

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace EDSL.Tests.StackFrameResources
open X86 OS OS.AddressSpace OS.StackFrame

-- Loader bytes are independent of both word encoders. Frame and outsider
-- allocations start unmapped, immediately below the retained original slot.
def literalSpace : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xc3, readExecute⟩
    | 65544 => some ⟨0x44, readOnly⟩
    | 65545 => some ⟨0x44, readOnly⟩
    | 65546 => some ⟨0, readOnly⟩
    | 65547 => some ⟨0, readOnly⟩
    | 65548 => some ⟨0, readOnly⟩
    | 65549 => some ⟨0x80, readOnly⟩
    | 65550 => some ⟨0xff, readOnly⟩
    | 65551 => some ⟨0xff, readOnly⟩
    | _ => none

def frame : Descriptor :=
  ⟨⟨0, 4096, 65544, 0xffff800000004444, [0xc3], 0, 1⟩, ⟨2, 0⟩, 16⟩

def evolve (state : Shared) (operation : Ownership.Mutation) : Shared :=
  match Borrowing.mutate state operation with | .ok (after, _) => after | .error _ => state

def lend (state : Shared) (ticket : Ownership.Ticket) (region : Region) : Shared :=
  match Borrowing.readBorrow state 0 ticket frame.owner region with
  | .ok (after, _) => after | .error _ => state

def initial : Shared := Borrowing.empty (Ownership.empty literalSpace)
def code : Shared := evolve initial (.adopt 0 ⟨4096, 1⟩)
def caller : Shared := evolve code (.adopt 0 ⟨65544, 8⟩)
def codeLoan : Shared := lend caller ⟨0, 0⟩ ⟨4096, 1⟩
def callerLoan : Shared := lend codeLoan ⟨1, 0⟩ ⟨65544, 8⟩
def allocated : Shared := evolve callerLoan (.allocate frame.owner frame.region readWrite)
def seed : Shared := evolve allocated (.allocate 9 ⟨65520, 8⟩ readWrite)

-- Well-formedness comes from the actual adopt/borrow/allocate transitions,
-- rather than an axiom or a direct claim about a hand-constructed registry.
theorem initialized : Borrowing.WellFormed seed := by
  have history : Borrowing.History initial seed :=
    .next (.mutate (show Borrowing.mutate initial (.adopt 0 ⟨4096, 1⟩) =
      .ok (code, some ⟨0, 0⟩) by rfl))
    (.next (.mutate (show Borrowing.mutate code (.adopt 0 ⟨65544, 8⟩) =
      .ok (caller, some ⟨1, 0⟩) by rfl))
    (.next (.readBorrow (show Borrowing.readBorrow caller 0 ⟨0, 0⟩ frame.owner ⟨4096, 1⟩ =
      .ok (codeLoan, 0) by rfl))
    (.next (.readBorrow (show Borrowing.readBorrow codeLoan 0 ⟨1, 0⟩ frame.owner ⟨65544, 8⟩ =
      .ok (callerLoan, 1) by rfl))
    (.next (.mutate (show Borrowing.mutate callerLoan (.allocate frame.owner frame.region readWrite) =
      .ok (allocated, some frame.ticket) by rfl))
    (.next (.mutate (show Borrowing.mutate allocated (.allocate 9 ⟨65520, 8⟩ readWrite) =
      .ok (seed, some ⟨3, 0⟩) by rfl)) .refl)))))
  exact history.wellFormed (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed _))

theorem ready : Contract frame seed := by
  refine ⟨⟨initialized, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩,
    ⟨⟨1, 0, frame.region⟩, rfl, rfl⟩, by decide, ?_, ?_⟩
  · exact ⟨⟨⟨0, 0⟩, 0, 1, ⟨4096, 1⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨⟨⟨1, 0⟩, 0, 1, ⟨65544, 8⟩⟩, rfl, rfl, rfl⟩
  · refine ⟨by decide, ?_⟩
    intro offset byte found
    cases offset with
    | zero => simp [frame] at found; subst byte; rfl
    | succ offset => simp [frame] at found
  · rfl
  · intro address slot
    have lower : 65528 ≤ address.toNat := slot.1
    have upper : address.toNat + 8 ≤ 65544 := slot.2
    have choices : address.toNat = 65528 ∨ address.toNat = 65529 ∨ address.toNat = 65530 ∨
        address.toNat = 65531 ∨ address.toNat = 65532 ∨ address.toNat = 65533 ∨
        address.toNat = 65534 ∨ address.toNat = 65535 ∨ address.toNat = 65536 := by omega
    rcases choices with h | h | h | h | h | h | h | h | h
    all_goals
      have same : address = BitVec.ofNat 64 address.toNat := by simp
      rw [same, h]
      exact ⟨⟨1, 0, frame.region⟩, rfl, rfl, rfl, by decide, by decide⟩
  · intro identifier loan live
    by_cases one : identifier = 1
    · subst identifier
      have record : (⟨⟨1, 0⟩, 0, 1, ⟨65544, 8⟩⟩ : Borrowing.Loan) = loan := Option.some.inj live
      subst loan
      decide
    · by_cases zero : identifier = 0
      · subst identifier
        have record : (⟨⟨0, 0⟩, 0, 1, ⟨4096, 1⟩⟩ : Borrowing.Loan) = loan := Option.some.inj live
        subst loan
        decide
      · have missing : seed.loans identifier = none := by
          change (if identifier = 1 then _ else if identifier = 0 then _ else none) = none
          simp [one, zero]
        rw [missing] at live
        cases live

def cpu (shared : Shared) : X86.State :=
  ⟨fun r => if r = .rsp then 65536 else 0, 4096, 0, toMemory shared.resources.space⟩

def first : Shared := evolve seed (.store64 frame.owner frame.ticket 65528 0xfedcba9876543210)
def second : Shared := evolve first (.store64 frame.owner frame.ticket 65536 0xffff800000003333)

theorem stores : PrivateHistory frame seed second :=
  .next (middle := first)
    (.store64 (address := 65528) (value := 0xfedcba9876543210) (by decide) (by rfl))
    (.next (.store64 (address := 65536) (value := 0xffff800000003333) (by decide) (by rfl)) .refl)

-- The resource theorem is exercised on an actual initialized world; after an
-- owned observation the next private store is still derived for every value.
example (value : Word) : ∃ after, Borrowing.mutate first
    (.store64 frame.owner frame.ticket 65536 value) = .ok (after, none) := by
  have firstReady := (contract_store64 ready (show Borrowing.mutate seed
    (.store64 frame.owner frame.ticket 65528 0xfedcba9876543210) = .ok (first, none) by rfl)).1
  obtain ⟨_, _, _, _, _⟩ := current_privateSlot (Current.mk firstReady (machine := cpu first) rfl)
    (address := 65528) (by decide)
  exact current_store64_enabled ⟨firstReady, rfl⟩ (machine := cpu first) (by decide) value

example : Borrowing.loadOwnedWord64 first frame.owner frame.ticket 65528 = .ok 0xfedcba9876543210 ∧
    readWord (cpu first).memory 65528 = .ok 0xfedcba9876543210 := ⟨rfl, rfl⟩

-- Independent byte order expectations catch truncation/high-half errors, while
-- readWord at the first slot catches damage from a later same-allocation store.
example : readWord (cpu second).memory 65528 = .ok 0xfedcba9876543210 ∧
    readWord (cpu second).memory 65536 = .ok 0xffff800000003333 ∧
    [second.resources.space.cells 65528, second.resources.space.cells 65535,
      second.resources.space.cells 65536, second.resources.space.cells 65541,
      second.resources.space.cells 65543] =
    [some ⟨0x10, readWrite⟩, some ⟨0xfe, readWrite⟩, some ⟨0x33, readWrite⟩,
      some ⟨0x80, readWrite⟩, some ⟨0xff, readWrite⟩] := ⟨rfl, rfl, rfl⟩

example : Current frame second (cpu second) := stores.current ready rfl
example : readWord (cpu second).memory 65544 = .ok 0xffff800000004444 ∧
    fetchByte (cpu second).memory 4096 = .ok 0xc3 := ⟨rfl, rfl⟩
example (query : Word) (outside : ¬frame.region.Contains query) :
    second.resources.space.cells query = seed.resources.space.cells query :=
  stores.preserves.outside query outside
example : second.loans = seed.loans ∧ second.resources.allocations = seed.resources.allocations ∧
    second.nextLoan = seed.nextLoan ∧ second.resources.frontier = seed.resources.frontier :=
  ⟨stores.preserves.loans, stores.preserves.allocations, stores.preserves.nextLoan, stores.preserves.frontier⟩

-- Readable neighboring RAM cannot extend the complete natural frame interval.
-- The first operand overlaps the outsider, the second crosses into the caller.
example : readWord (cpu seed).memory 65524 = .ok 0 ∧
    Borrowing.loadOwnedWord64 seed frame.owner frame.ticket 65524 = .error .outsideAllocation ∧
    readWord (cpu seed).memory 65537 = .ok 0x4400000000000000 ∧
    Borrowing.loadOwnedWord64 seed frame.owner frame.ticket 65537 = .error .outsideAllocation ∧
    Borrowing.loadOwnedWord64 seed 9 frame.ticket 65528 = .error (.authority .wrongOwner) ∧
    Borrowing.loadOwnedWord64 seed frame.owner ⟨2, 1⟩ 65528 = .error (.authority .staleEpoch) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
example : ¬Slot frame 65524 ∧ ¬Slot frame 65537 := by decide
example : ¬ReadAllowed frame seed ⟨.stack, 65524, 8⟩ := by
  intro allowed
  cases allowed with
  | original original => exact (by decide : (65524 : Word) ≠ frame.call.stack) original.2.1
  | privateSlot _ _ present => exact (by decide : ¬Slot frame 65524) present.fits
example : canStoreQWord (cpu seed).memory 65524 = true ∧
    Borrowing.mutate seed (.store64 frame.owner frame.ticket 65524 7) =
      .error (.ownership .outsideAllocation) := ⟨rfl, rfl⟩

-- A frame loan over the other slot permits owner observation but blocks the
-- actual mutation gate until its real finish, including for a disjoint store.
def loaned : Shared :=
  match Borrowing.readBorrow first frame.owner frame.ticket 7 ⟨65536, 8⟩ with
  | .ok (after, _) => after | .error _ => first

def finished : Shared :=
  match Borrowing.finishLoan loaned 7 2 with | .ok after => after | .error _ => loaned

example : Borrowing.loadOwnedWord64 loaned frame.owner frame.ticket 65528 = .ok 0xfedcba9876543210 ∧
    Borrowing.mutate loaned (.store64 frame.owner frame.ticket 65528 0) = .error .borrowed ∧
    Borrowing.finishLoan loaned 7 2 = .ok finished := ⟨rfl, rfl, rfl⟩
example : ∃ after, Borrowing.mutate finished (.store64 frame.owner frame.ticket 65528 0) =
    .ok (after, none) := by exact ⟨evolve finished (.store64 frame.owner frame.ticket 65528 0), rfl⟩

example : ¬Contract frame loaned := by
  intro contract
  exact contract.unborrowed 2 ⟨frame.ticket, frame.owner, 7, ⟨65536, 8⟩⟩ (by rfl) rfl

-- An unaligned contained operand uses the same frame, without an ABI premise.
def unaligned : Shared := evolve seed (.store64 frame.owner frame.ticket 65529 0x89abcdef01234567)
example : Borrowing.loadOwnedWord64 unaligned frame.owner frame.ticket 65529 = .ok 0x89abcdef01234567 ∧
    readWord (cpu unaligned).memory 65529 = .ok 0x89abcdef01234567 := ⟨rfl, rfl⟩

end EDSL.Tests.StackFrameResources

#print axioms EDSL.OS.StackFrame.Contract.region_valid
#print axioms EDSL.OS.StackFrame.Contract.region_bounds
#print axioms EDSL.OS.StackFrame.current_privateSlot
#print axioms EDSL.OS.StackFrame.current_store64_enabled
#print axioms EDSL.OS.StackFrame.contract_store64
#print axioms EDSL.OS.StackFrame.current_store64
#print axioms EDSL.OS.StackFrame.PrivateHistory.preserves
#print axioms EDSL.OS.StackFrame.PrivateHistory.current
#audit_edsl
