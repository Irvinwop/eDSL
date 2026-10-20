/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Resources
import EDSL.Audit

namespace EDSL.Tests.FutexResources
open X86 OS.AddressSpace

def initial : OS.Atomics.State :=
  OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty))

def withTicket (state : OS.Atomics.State) (operation : OS.Ownership.Mutation) :
    Except OS.Atomics.Fault (OS.Atomics.State × OS.Ownership.Ticket) := do
  let (after, result) ← OS.Atomics.mutate state operation
  match result with
  | some ticket => return (after, ticket)
  | none => throw .missingHandle

def failureIs {α : Type} (operation : Except OS.Atomics.Fault α) (fault : OS.Atomics.Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = fault)
  | .ok _ => false

def prepare : Except OS.Atomics.Fault (OS.Atomics.State × OS.Futex.Resources.Registration) := do
  let (allocated, ticket) ← withTicket initial (.allocate 7 ⟨65536, 8⟩ readWrite)
  let (neighbor, _) ← OS.Atomics.mutate allocated (.store 7 ticket 65540 0x76543210)
  let (pinned, keeper) ← OS.Atomics.issue neighbor 7 ticket 90 65536
  return (pinned, ⟨7, ticket, 90, 65536, keeper⟩)

-- The call reads the peer's latest exchange, while the adjacent four bytes
-- retain their value. A snapshot-based pin or an overwide exchange fails this.
def retainedRead : Except OS.Atomics.Fault (BitVec 32 × BitVec 32 × Except Error (BitVec 32)) := do
  let (registered, registration) ← prepare
  let (active, call) ← OS.Futex.Resources.retainCall registered registration 90
  let (shared, producer) ← OS.Atomics.issue active 7 registration.ticket 11 65536
  let (first, _) ← OS.Atomics.exchange shared 11 producer 0x89abcdef
  let a ← OS.Futex.Resources.readPinned first 90 call
  let (second, _) ← OS.Atomics.exchange first 11 producer 0xfedcba98
  let b ← OS.Futex.Resources.readPinned second 90 call
  return (a, b, loadDWord (toMemory second.shared.resources.space) 65540)

example : retainedRead = .ok (0x89abcdef, 0xfedcba98, .ok 0x76543210) := by rfl

-- The keeper survives cleanup of a call pin, and a later call cannot revive
-- the old pin. Neither call cleanup nor wrong authority can close the keeper.
def isolatedCleanup : Except OS.Atomics.Fault (List Bool × BitVec 32) := do
  let (registered, registration) ← prepare
  let (active, first) ← OS.Futex.Resources.retainCall registered registration 90
  let before :=
    [failureIs (OS.Futex.Resources.closeCall active registration 90 registration.keeper) .reserved,
     failureIs (OS.Futex.Resources.closeCall active registration 11 first) .wrongActor,
     failureIs (OS.Atomics.mutate active (.release 7 registration.ticket)) .reserved,
     failureIs (OS.Atomics.mutate active (.transfer 7 registration.ticket 8)) .reserved,
     failureIs (OS.Atomics.mutate active (.protect 7 registration.ticket readOnly)) .reserved,
     failureIs (OS.Atomics.readBorrow active 7 registration.ticket 22 ⟨65540, 4⟩) .reserved]
  let closed ← OS.Futex.Resources.closeCall active registration 90 first
  let stillPinned := failureIs (OS.Atomics.mutate closed (.release 7 registration.ticket)) .reserved
  let (renewed, second) ← OS.Futex.Resources.retainCall closed registration 90
  let stale := failureIs (OS.Futex.Resources.readPinned renewed 90 first) .missingHandle
  let staleClose := failureIs (OS.Futex.Resources.closeCall renewed registration 90 first) .missingHandle
  let (written, _) ← OS.Atomics.exchange renewed 90 registration.keeper 0x10203040
  let current ← OS.Futex.Resources.readPinned written 90 second
  return (before ++ [stillPinned, stale, staleClose], current)

example : isolatedCleanup = .ok ([true, true, true, true, true, true, true, true, true], 0x10203040) := by rfl

-- Copying registration fields does not supply keeper authority; unrelated
-- handles cannot be substituted for call cleanup even for the same actor.
def rejectedAuthority : Except OS.Atomics.Fault (List Bool) := do
  let (registered, registration) ← prepare
  let wrongOwner := { registration with owner := 8 }
  let wrongCell := { registration with address := 65540 }
  let wrongActor := { registration with actor := 11 }
  let (other, ticket) ← withTicket registered (.allocate 8 ⟨131072, 4⟩ readWrite)
  let (both, unrelated) ← OS.Atomics.issue other 8 ticket 90 131072
  return [failureIs (OS.Futex.Resources.retainCall both wrongOwner 90) .conflictingCell,
    failureIs (OS.Futex.Resources.retainCall both wrongCell 90) .conflictingCell,
    failureIs (OS.Futex.Resources.retainCall both wrongActor 90) .wrongActor,
    failureIs (OS.Futex.Resources.closeCall both registration 90 unrelated) .conflictingCell,
    failureIs (OS.Atomics.mutate both (.adopt 8 ⟨65536, 4⟩)) (.authority (.ownership .claimedRegion)),
    failureIs (OS.Atomics.mutate both (.allocate 8 ⟨65536, 4⟩ readWrite))
      (.authority (.ownership (.addressSpace .overlap)))]

example : rejectedAuthority = .ok [true, true, true, true, true, true] := by rfl

def allocated : OS.Atomics.State := OS.Atomics.empty (OS.Borrowing.empty
  (OS.Ownership.install (OS.Ownership.empty OS.AddressSpace.empty)
    (mapUnchecked OS.AddressSpace.empty ⟨65536, 8⟩ readWrite) 7 ⟨65536, 8⟩))

def registration : OS.Futex.Resources.Registration := ⟨7, ⟨0, 0⟩, 90, 65536, 0⟩
def live : OS.Atomics.State := OS.Atomics.install allocated registration.handle

theorem allocated_valid : OS.Atomics.WellFormed allocated := by
  have emptyValid := OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _
    (OS.Ownership.empty_wellFormed OS.AddressSpace.empty))
  exact OS.Atomics.mutate_wellFormed initial (.allocate 7 ⟨65536, 8⟩ readWrite)
    (allocated, some ⟨0, 0⟩) emptyValid (by rfl)

theorem live_valid : OS.Atomics.WellFormed live :=
  (OS.Atomics.issue_wellFormed allocated 7 ⟨0, 0⟩ 90 65536 (live, 0) allocated_valid (by rfl)).1

-- Positive enabledness is quantified over every logical caller, rather than
-- assuming that the pin issue operation succeeded.
theorem every_caller_can_retain (actor : Nat) :
    ∃ result, OS.Futex.Resources.retainCall live registration actor = .ok result ∧
      OS.Atomics.WellFormed result.1 ∧ OS.Futex.Resources.Valid result.1 registration := by
  have enabled := OS.Futex.Resources.retainCall_enabled live registration actor live_valid (by rfl)
  exact ⟨_, enabled, (OS.Futex.Resources.retainCall_effect _ _ _ _ live_valid enabled).1,
    (OS.Futex.Resources.retainCall_effect _ _ _ _ live_valid enabled).2.1⟩

-- Every replacement, including zero and high-bit values, is seen by a pin
-- retained before the write. The observation specification is a direct
-- architectural readback property independent of the resource evaluator.
theorem every_peer_replacement_visible (replacement : BitVec 32) :
    ∃ after pin, OS.Atomics.WellFormed after ∧ OS.Futex.Resources.Valid after registration ∧
      OS.Futex.Resources.readPinned after 12 pin = .ok replacement := by
  have retained := OS.Futex.Resources.retainCall_enabled live registration 12 live_valid (by rfl)
  let held := OS.Atomics.install live (registration.callHandle 12)
  have heldValid : OS.Atomics.WellFormed held := (OS.Futex.Resources.retainCall_effect _ _ _ _ live_valid retained).1
  obtain ⟨result, exchanged⟩ := OS.Atomics.exchange_enabled held 90 0 registration.handle replacement heldValid (by rfl)
  refine ⟨result.1, 1, OS.Atomics.exchange_wellFormed _ _ _ _ _ heldValid exchanged,
    OS.Futex.Resources.exchange_keeps_registration _ _ _ _ _ _ (by rfl) exchanged, ?_⟩
  exact OS.Futex.Resources.readPinned_after_exchange held 90 0 12 1 registration.handle (registration.callHandle 12)
    replacement result (by rfl) (by rfl) rfl exchanged

end EDSL.Tests.FutexResources

#audit_edsl
