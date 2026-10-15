/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex
import EDSL.Audit

namespace EDSL.Tests.Mutex
open X86 OS.AddressSpace
abbrev MState := OS.Mutex.State
abbrev Fault := OS.Mutex.Fault
abbrev Lease := OS.Mutex.Lease

def seed (old : BitVec 32) : Space where
  cells address := match address.toNat with
    | 65536 | 65537 | 65538 | 65539 => some ⟨0, readWrite⟩
    | 131072 => some ⟨old.extractLsb' 0 8, readWrite⟩
    | 131073 => some ⟨old.extractLsb' 8 8, readWrite⟩
    | 131074 => some ⟨old.extractLsb' 16 8, readWrite⟩
    | 131075 => some ⟨old.extractLsb' 24 8, readWrite⟩
    | 131076 => some ⟨0xd8, readWrite⟩ | 131077 => some ⟨0xc7, readWrite⟩
    | 131078 => some ⟨0xb6, readWrite⟩ | 131079 => some ⟨0xa5, readWrite⟩
    | _ => none

def withTicket (state : MState) (operation : OS.Ownership.Mutation) : Except Fault (MState × OS.Ownership.Ticket) := do
  let (after, output) ← OS.Mutex.mutate state operation
  let some ticket := output | throw .missingMutex
  pure (after, ticket)

def setupIn (space : Space) : Except Fault (MState × OS.Mutex.Config) := do
  let initial := OS.Mutex.empty (OS.Borrowing.empty (OS.Ownership.empty space))
  let (lock, lockTicket) ← withTicket initial (.adopt 0 ⟨65536, 4⟩)
  let (data, dataTicket) ← withTicket lock (.adopt 0 ⟨131072, 8⟩)
  pure (data, ⟨0, lockTicket, 65536, dataTicket, 131072, fun value => !value.getLsbD 0⟩)

def failureIs {α : Type} (result : Except Fault α) (expected : Fault) : Bool :=
  match result with | .error actual => decide (actual = expected) | .ok _ => false

def acquire (state : MState) (actor : Nat) : Except Fault (MState × Lease × AtomicEvent) := do
  let result ← OS.Mutex.tryAcquire state actor
  let some lease := result.acquired | throw .busy
  pure (result.state, lease, result.event)

-- Two independent owners pass a protected value through the lock. The even
-- invariant is deliberately broken while held and must close before release.
def handoff : Except Fault (List Bool × List (BitVec 32) × List AtomicEvent × Option (BitVec 32) × Option (BitVec 32)) := do
  let (initial, config) ← setupIn (seed 0xfffffffe)
  let registered ← OS.Mutex.register initial config
  let (first, guardA, eventA) ← acquire registered 7
  let before ← OS.Mutex.guardLoad first 7 guardA
  let reentrant ← OS.Mutex.tryAcquire first 7
  let competing ← OS.Mutex.tryAcquire reentrant.state 9
  let denied := failureIs (OS.Mutex.guardStore competing.state 9 guardA 2) .wrongActor
  let odd ← OS.Mutex.guardStore competing.state 7 guardA 0xffffffff
  let rejectsOdd := failureIs (OS.Mutex.release odd 7 guardA) .invalidInvariant
  let restored ← OS.Mutex.guardStore odd 7 guardA 0
  let (releasedA, eventReleaseA) ← OS.Mutex.release restored 7 guardA
  let (second, guardB, eventB) ← acquire releasedA 9
  let received ← OS.Mutex.guardLoad second 9 guardB
  let stale := failureIs (OS.Mutex.guardLoad second 7 guardA) .staleGuard
  let updated ← OS.Mutex.guardStore second 9 guardB 2
  let (releasedB, eventReleaseB) ← OS.Mutex.release updated 9 guardB
  let duplicate := failureIs (OS.Mutex.release releasedB 9 guardB) .missingGuard
  let free ← OS.Mutex.unregister releasedB 0
  let (changed, _) ← OS.Mutex.mutate free (.store 0 config.dataTicket 131072 0x12345678)
  pure ([decide (reentrant.acquired = none), decide (competing.acquired = none), denied, rejectsOdd, stale, duplicate],
    [before, received], [eventA, reentrant.event, competing.event, eventReleaseA, eventB, eventReleaseB],
    (loadDWord (toMemory changed.shared.resources.space) 131072).toOption,
    (loadDWord (toMemory changed.shared.resources.space) 131076).toOption)

example : handoff = .ok (List.replicate 6 true, [0xfffffffe, 0],
    [⟨65536, 0, 1⟩, ⟨65536, 1, 1⟩, ⟨65536, 1, 1⟩, ⟨65536, 1, 0⟩, ⟨65536, 0, 1⟩, ⟨65536, 1, 0⟩],
    some 0x12345678, some 0xa5b6c7d8) := by rfl

-- Reservation covers both entire allocations while unlocked as well as held.
-- A fresh acquisition by the same actor, even after re-registration, must not
-- revive a copied guard. Unrelated mapping, store and borrowing remain usable.
def lifetime : Except Fault (List Bool × List Nat × Option (BitVec 32)) := do
  let (initial, config) ← setupIn (seed 0)
  let registered ← OS.Mutex.register initial config
  let blocked := [
    failureIs (OS.Mutex.mutate registered (.release 0 config.lockTicket)) .reserved,
    failureIs (OS.Mutex.mutate registered (.store 0 config.dataTicket 131076 0)) .reserved,
    failureIs (OS.Mutex.mutate registered (.transfer 0 config.dataTicket 4)) .reserved,
    failureIs (OS.Mutex.mutate registered (.protect 0 config.lockTicket readOnly)) .reserved,
    failureIs (OS.Mutex.readBorrow registered 0 config.dataTicket 4 ⟨131076, 4⟩) .reserved,
    failureIs (OS.Mutex.register registered config) .alreadyRegistered,
    failureIs (OS.Mutex.unregister registered 8) .wrongOwner]
  let (first, old, _) ← acquire registered 4
  let held := failureIs (OS.Mutex.unregister first 0) .busy
  let (other, ticket) ← withTicket first (.allocate 0 ⟨262144, 4⟩ readWrite)
  let (stored, _) ← OS.Mutex.mutate other (.store 0 ticket 262144 0x76543210)
  let (borrowed, reader) ← OS.Mutex.readBorrow stored 0 ticket 11 ⟨262144, 4⟩
  let (released, _) ← OS.Mutex.release borrowed 4 old
  let (again, next, _) ← acquire released 4
  let staleSame := failureIs (OS.Mutex.guardStore again 4 old 0) .staleGuard
  let (done, _) ← OS.Mutex.release again 4 next
  let unregistered ← OS.Mutex.unregister done 0
  let reregistered ← OS.Mutex.register unregistered config
  let (last, newest, _) ← acquire reregistered 4
  let staleObject := failureIs (OS.Mutex.guardStore last 4 old 0) .staleGuard
  let (final, _) ← OS.Mutex.release last 4 newest
  let noReader ← OS.Mutex.finishLoan final 11 reader
  pure (blocked ++ [held, staleSame, staleObject], [old.identifier, next.identifier, newest.identifier],
    (loadDWord (toMemory noReader.shared.resources.space) 262144).toOption)

example : lifetime = .ok (List.replicate 10 true, [0, 1, 2], some 0x76543210) := by rfl

def registrationFailures : Except Fault (List Bool) := do
  let (initial, config) ← setupIn (seed 2)
  let aliases := { config with dataTicket := config.lockTicket, dataAddress := config.lockAddress }
  let stale := { config with dataTicket := ⟨1, 99⟩ }
  let wrongOwner := { config with owner := 9 }
  let (loan, reader) ← OS.Mutex.readBorrow initial 0 config.dataTicket 4 ⟨131076, 4⟩
  let borrowed := failureIs (OS.Mutex.register loan config) (.authority .borrowed)
  let unborrowed ← OS.Mutex.finishLoan loan 4 reader
  let (changed, _) ← OS.Mutex.mutate unborrowed (.store 0 config.lockTicket 65536 1)
  let busy := failureIs (OS.Mutex.register changed config) .initiallyLocked
  let (odd, _) ← OS.Mutex.mutate unborrowed (.store 0 config.dataTicket 131072 3)
  pure [failureIs (OS.Mutex.register initial aliases) .sameAllocation,
    failureIs (OS.Mutex.register initial stale) (.authority (.ownership .staleEpoch)),
    failureIs (OS.Mutex.register initial wrongOwner) (.authority (.ownership .wrongOwner)),
    borrowed, busy, failureIs (OS.Mutex.register odd config) .invalidInvariant]

example : registrationFailures = .ok (List.replicate 6 true) := by rfl

def deniedLastByte : Except Fault Bool := do
  let space : Space := ⟨fun address => if address = 131075 then some ⟨0, readOnly⟩ else (seed 0).cells address⟩
  let (initial, config) ← setupIn space
  pure (failureIs (OS.Mutex.register initial config) (.machine (.writeDenied 131072)))

example : deniedLastByte = .ok true := by rfl

-- Symbolic nonvacuity: admission imposes no selected data bits beyond the
-- independently chosen invariant. Both allocations pass actual adoption.
def lockWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (seed old)) (seed old) 0 ⟨65536, 4⟩

def fullWorld (old : BitVec 32) : OS.Ownership.World :=
  OS.Ownership.install (lockWorld old) (seed old) 0 ⟨131072, 8⟩

theorem lock_adopted (old : BitVec 32) :
    OS.Ownership.adopt (OS.Ownership.empty (seed old)) 0 ⟨65536, 4⟩ = .ok (lockWorld old, ⟨0, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) (by rfl) (by rfl)

theorem lock_valid (old : BitVec 32) : OS.Ownership.WellFormed (lockWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) (lock_adopted old)).1

theorem data_adopted (old : BitVec 32) :
    OS.Ownership.adopt (lockWorld old) 0 ⟨131072, 8⟩ = .ok (fullWorld old, ⟨1, 0⟩) :=
  OS.Ownership.adopt_success _ _ _ (lock_valid old) (by decide) (by rfl) (by rfl)

theorem full_valid (old : BitVec 32) : OS.Ownership.WellFormed (fullWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (lock_valid old) (data_adopted old)).1

def initial (old : BitVec 32) : MState := OS.Mutex.empty (OS.Borrowing.empty (fullWorld old))
def description (invariant : BitVec 32 → Bool) : OS.Mutex.Config :=
  ⟨0, ⟨0, 0⟩, 65536, ⟨1, 0⟩, 131072, invariant⟩
def born (old : BitVec 32) (invariant : BitVec 32 → Bool) : MState :=
  { initial old with mutex := some ⟨description invariant, none⟩ }

theorem initial_valid (old : BitVec 32) : OS.Mutex.WellFormed (initial old) :=
  OS.Mutex.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (full_valid old))

theorem observed_data (old : BitVec 32) :
    loadDWord (toMemory (initial old).shared.resources.space) 131072 = .ok old := by
  change Except.ok (joinDWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8)) = .ok old
  rw [join_extracts]

theorem registered_all_values (old : BitVec 32) (invariant : BitVec 32 → Bool) (closed : invariant old = true) :
    OS.Mutex.register (initial old) (description invariant) = .ok (born old invariant) := by
  apply OS.Mutex.register_enabled
  · rfl
  · change (0 : Nat) ≠ 1; decide
  · exact ⟨⟨0, 0, ⟨65536, 4⟩⟩, rfl, rfl, rfl, by rfl, by rfl⟩
  · exact ⟨⟨0, 0, ⟨131072, 8⟩⟩, rfl, rfl, rfl, by rfl, by rfl⟩
  · change atomicAddressable (65536 : Word) = true; decide
  · intro identifier loan found; cases found
  · rfl
  · exact ⟨old, observed_data old, closed⟩

theorem all_admitted_values_cycle (old temporary value : BitVec 32) (invariant : BitVec 32 → Bool)
    (initialInvariant : invariant old = true) (finalInvariant : invariant value = true) (actor : Nat) :
    ∃ acquired lease intermediate written result,
      OS.Mutex.tryAcquire (born old invariant) actor = .ok acquired ∧ acquired.acquired = some lease ∧
      OS.Mutex.guardStore acquired.state actor lease temporary = .ok intermediate ∧
      OS.Mutex.guardStore intermediate actor lease value = .ok written ∧
      OS.Mutex.release written actor lease = .ok result ∧ OS.Mutex.WellFormed result.1 ∧
      OS.Mutex.Revoked result.1 lease ∧ loadDWord (toMemory result.1.shared.resources.space) 131072 = .ok value := by
  have valid := OS.Mutex.register_wellFormed _ _ _ (initial_valid old) (registered_all_values old invariant initialInvariant)
  exact OS.Mutex.critical_cycle (born old invariant) actor ⟨description invariant, none⟩ temporary value valid rfl rfl finalInvariant

end EDSL.Tests.Mutex

#audit_edsl
