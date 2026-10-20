/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResources
import EDSL.Audit

namespace EDSL.Tests.ArrayResources
open X86 OS.AddressSpace OS.ArrayResources

-- A caller with only code and a complete return slot. No input allocation or
-- mapped input is installed. These mappings enter the actual ownership API.
def caller : Space where
  cells address :=
    if address = 4096 then some ⟨0xc3, readExecute⟩
    else if (⟨65544, 8⟩ : Region).Contains address then
      some ⟨if address = 65545 then 0x20 else 0, readOnly⟩
    else none

def codeOwned : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty caller) caller 7 ⟨4096, 1⟩

def bothOwned : OS.Ownership.World :=
  OS.Ownership.install codeOwned caller 7 ⟨65544, 8⟩

theorem codeOwned_valid : OS.Ownership.WellFormed codeOwned :=
  (OS.Ownership.adopt_wellFormed (OS.Ownership.empty caller) 7 ⟨4096, 1⟩ (codeOwned, ⟨0, 0⟩)
    (OS.Ownership.empty_wellFormed caller) (by rfl)).1

theorem bothOwned_valid : OS.Ownership.WellFormed bothOwned :=
  (OS.Ownership.adopt_wellFormed codeOwned 7 ⟨65544, 8⟩ (bothOwned, ⟨1, 0⟩)
    codeOwned_valid (by rfl)).1

def codeHeld : OS.Borrowing.State := OS.Borrowing.installLoan
  (OS.Borrowing.empty bothOwned) ⟨⟨0, 0⟩, 7, 11, ⟨4096, 1⟩⟩

def emptyHeld : OS.Borrowing.State := OS.Borrowing.installLoan
  codeHeld ⟨⟨1, 0⟩, 7, 11, ⟨65544, 8⟩⟩

theorem codeHeld_valid : OS.Borrowing.WellFormed codeHeld :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨0, 0⟩ 11 ⟨4096, 1⟩ (codeHeld, 0)
    (OS.Borrowing.empty_wellFormed _ bothOwned_valid) (by rfl)).1

theorem emptyHeld_valid : OS.Borrowing.WellFormed emptyHeld :=
  (OS.Borrowing.readBorrow_wellFormed codeHeld 7 ⟨1, 0⟩ 11 ⟨65544, 8⟩
    (emptyHeld, 1) codeHeld_valid (by rfl)).1

def emptyCall (unusedBase : Word) (unusedLoan : Nat) : Call :=
  ⟨10, ⟨0, 1, unusedLoan⟩, 4096, [0xc3], 65544, unusedBase, [], 8192⟩

-- This universal enabledness witness catches accidental span-zero loan,
-- pointer canonicality, input allocation, or input readability requirements.
-- Even an aliased/absent input ID and a noncanonical unused pointer work.
theorem every_unused_pointer_admitted (unusedBase : Word) (unusedLoan : Nat) :
    Contract emptyHeld (emptyCall unusedBase unusedLoan) := by
  refine ⟨emptyHeld_valid, ?_, ?_, ?_, currentArrayAt_nil _ _,
    arrayBound_nil _, ?_, ?_, ?_⟩
  · refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro nonempty; exact False.elim (nonempty rfl)
    · change OS.Ownership.Disjoint ⟨4096, 1⟩ ⟨65544, 8⟩
      decide
    all_goals intro nonempty; exact False.elim (nonempty rfl)
  · refine ⟨show (4096 : Word).toNat + 1 ≤ 2^64 by decide, ?_⟩
    intro index byte present
    cases index with
    | zero => simp [emptyCall] at present; subst byte; rfl
    | succ index => simp [emptyCall] at present
  · change readWord (toMemory caller) 65544 = .ok 8192
    simp [readWord, readStackByte, caller, toMemory, Region.Contains, canonical, readOnly]
  · change canonical 8192 = true
    decide
  · change (65544 : Word).toNat + 8 < 2^64
    decide
  · change canonical ((65544 : Word) + 8) = true
    decide

-- The empty exception never releases code or any byte of the return slot.
example : OS.Borrowing.mutate emptyHeld (.release 7 ⟨0, 0⟩) = .error .borrowed := by rfl
example : OS.Borrowing.mutate emptyHeld (.protect 7 ⟨1, 0⟩ inaccessible) = .error .borrowed := by rfl
example : OS.Borrowing.mutate emptyHeld (.store 7 ⟨1, 0⟩ 65548 0) = .error .borrowed := by rfl

-- An independently specified complete return slot includes byte seven.
-- Removing just that byte cannot satisfy even the empty-input contract.
def missingLastStack : OS.Borrowing.State :=
  { emptyHeld with resources := { emptyHeld.resources with
      space := ⟨fun address => if address = 65551 then none else caller.cells address⟩ } }

example (base : Word) (loan : Nat) : ¬Contract missingLastStack (emptyCall base loan) := by
  intro admitted
  have read := admitted.stack
  change (readWord (toMemory missingLastStack.resources.space) 65544) = .ok 8192 at read
  have failed : readWord (toMemory missingLastStack.resources.space) 65544 =
      .error (.inaccessibleStack 65551) := by rfl
  rw [failed] at read
  cases read

-- Input is allocated and populated AFTER the code/stack loans. The resulting
-- current array contract must bind these current bytes, not the prior zeros.
def arrayAllocated : OS.Borrowing.State :=
  { emptyHeld with resources :=
      OS.Ownership.install emptyHeld.resources (mapUnchecked caller ⟨131072, 8⟩ readWrite) 7 ⟨131072, 8⟩ }

def firstStored : OS.Borrowing.State :=
  { arrayAllocated with resources := { arrayAllocated.resources with
      space := writeWordCells arrayAllocated.resources.space 131072 0x89abcdef } }

def bothStored : OS.Borrowing.State :=
  { firstStored with resources := { firstStored.resources with
      space := writeWordCells firstStored.resources.space 131076 0x10203040 } }

def arrayHeld : OS.Borrowing.State := OS.Borrowing.installLoan bothStored
  ⟨⟨2, 0⟩, 7, 11, ⟨131072, 8⟩⟩

theorem array_history : OS.Borrowing.History emptyHeld arrayHeld :=
  .next (.mutate (show OS.Borrowing.mutate emptyHeld (.allocate 7 ⟨131072, 8⟩ readWrite) =
    .ok (arrayAllocated, some ⟨2, 0⟩) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate arrayAllocated (.store 7 ⟨2, 0⟩ 131072 0x89abcdef) =
    .ok (firstStored, none) from rfl))
  (.next (.mutate (show OS.Borrowing.mutate firstStored (.store 7 ⟨2, 0⟩ 131076 0x10203040) =
    .ok (bothStored, none) from rfl))
  (.next (.readBorrow (show OS.Borrowing.readBorrow bothStored 7 ⟨2, 0⟩ 11 ⟨131072, 8⟩ =
    .ok (arrayHeld, 2) from rfl)) .refl)))

def arrayCall : Call := { emptyCall 131072 2 with values := [0x89abcdef, 0x10203040] }

theorem current_array_admitted : Contract arrayHeld arrayCall := by
  have kept : Retained arrayHeld (emptyCall 131072 2) :=
    ⟨rfl, rfl, fun nonempty => False.elim (nonempty rfl)⟩
  have prior := (every_unused_pointer_admitted 131072 2).frame array_history kept
  refine ⟨prior.wellFormed, ?_, prior.code, prior.stack, ?_,
    show (131072 : Word).toNat + 4 * 2 ≤ 2^64 by decide,
    prior.returnCanonical, prior.stackBound, prior.postStackCanonical⟩
  · exact ⟨prior.held.code, prior.held.stack, fun _ => ⟨_, rfl, rfl, rfl⟩,
      prior.held.code_stack, fun _ => by decide, fun _ => by decide⟩
  · intro index value present
    match index with
    | 0 | 1 => simp [arrayCall, emptyCall] at present; subst value; rfl
    | index + 2 => simp [arrayCall, emptyCall] at present

-- Readable RAM beyond an operand is insufficient authority: the final word
-- is admitted but moving it by one byte crosses the exact eight-byte loan.
example : OS.Borrowing.loadWord arrayHeld 11 2 131077 = .error .outsideLoan := by rfl
example : OS.Borrowing.loadWord arrayHeld 12 2 131076 = .error (.authority .wrongBorrower) := by rfl
example : OS.Borrowing.mutate arrayHeld (.store 7 ⟨2, 0⟩ 131076 0) = .error .borrowed := by rfl

example : ¬currentArrayAt arrayHeld 131072 [0, 0] := by
  intro stale
  have observed := stale 0 0 rfl
  change (.ok (0x89abcdef : BitVec 32) : Except Error (BitVec 32)) = .ok 0 at observed
  exact (by decide : (0x89abcdef : BitVec 32) ≠ 0) (Except.ok.inj observed)

-- Complete RAM coupling rejects a machine that has the right code but omits
-- current input memory; selected code equality alone cannot admit it.
def staleMachine : X86.State := ⟨fun _ => 0, 4096, 0, toMemory caller⟩

example : ¬Admission arrayHeld arrayCall staleMachine := by
  intro admitted
  have same := congrArg (fun memory : Memory => memory.read 131072) admitted.coupled
  change none = some 0xef at same
  cases same

-- Actual Atomics wrappers may change an unrelated word while the array,
-- code, and entire stack retain their current observations. A global-RAM
-- snapshot premise would wrongly rule out this managed peer history.
def peerAllocated : OS.Atomics.State :=
  let resources := OS.Ownership.install arrayHeld.resources
    (mapUnchecked arrayHeld.resources.space ⟨196608, 4⟩ readWrite) 7 ⟨196608, 4⟩
  OS.Atomics.empty { arrayHeld with resources := resources }

def peerPinned : OS.Atomics.State := OS.Atomics.install peerAllocated ⟨7, ⟨3, 0⟩, 22, 196608⟩

def peerWritten (value : BitVec 32) : OS.Atomics.State :=
  { peerPinned with shared := { peerPinned.shared with resources :=
      { peerPinned.shared.resources with
        space := writeWordCells peerPinned.shared.resources.space 196608 value } } }

theorem peer_history (value : BitVec 32) :
    OS.Atomics.History (OS.Atomics.empty arrayHeld) (peerWritten value) :=
  .next (.mutate (show OS.Atomics.mutate (OS.Atomics.empty arrayHeld)
    (.allocate 7 ⟨196608, 4⟩ readWrite) = .ok (peerAllocated, some ⟨3, 0⟩) from rfl))
  (.next (.issue (show OS.Atomics.issue peerAllocated 7 ⟨3, 0⟩ 22 196608 =
    .ok (peerPinned, 0) from rfl))
  (.next (.exchange (show OS.Atomics.exchange peerPinned 22 0 value =
    .ok (peerWritten value, 0) from rfl)) .refl))

theorem live_array_after_peer (value : BitVec 32) :
    Contract (peerWritten value).shared arrayCall :=
  current_array_admitted.frame_atomics (peer_history value) ⟨rfl, rfl, fun _ => rfl⟩

example : (toMemory (peerWritten 1).shared.resources.space) ≠
    toMemory arrayHeld.resources.space := by
  intro same
  have atPeer := congrArg (fun memory : Memory => memory.read 196608) same
  change some 1 = none at atPeer
  cases atPeer

-- A data address above 4GiB must keep its high bits. The expected natural
-- address is independently specified, so truncating either base or EA fails.
example : ((0x100000000 : Word) + BitVec.ofNat 64 (4 * 1)).toNat = 4294967300 := by
  exact element_address (values := [0, 0])
    (show (0x100000000 : Word).toNat + 4 * 2 ≤ 2^64 by decide) (by decide)

end EDSL.Tests.ArrayResources

#audit_edsl
