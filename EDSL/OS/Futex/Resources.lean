/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Machine

namespace EDSL.OS.Futex.Resources
open X86 AddressSpace

/-- The keeper retains managed allocation lifetime, rather than a word-value
snapshot. Actor labels and tickets are proof data, not native authentication. -/
structure Registration where
  owner : Nat
  ticket : Ownership.Ticket
  actor : Nat
  address : Word
  keeper : Nat
  deriving DecidableEq, Repr

def Registration.handle (registration : Registration) : Atomics.Handle :=
  ⟨registration.owner, registration.ticket, registration.actor, registration.address⟩

def Registration.callHandle (registration : Registration) (actor : Nat) : Atomics.Handle :=
  ⟨registration.owner, registration.ticket, actor, registration.address⟩

/-- Current stored authority is necessary; an old registration record alone
does not authorize retention, reading, or reclamation. -/
def Valid (state : Atomics.State) (registration : Registration) : Prop :=
  state.handles registration.keeper = some registration.handle

/-- An explicit admitted lower-userspace interval. This is a target contract,
not a proof of the running kernel's access_ok policy. The four-byte containment
check is independent of canonical-address checks in the machine semantics. -/
structure UserInterval where
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

def UserInterval.AdmitsWord (interval : UserInterval) (address : Word) : Prop :=
  interval.lower ≤ address.toNat ∧ address.toNat + 4 ≤ interval.upper ∧ interval.upper ≤ 2^47

instance (interval : UserInterval) (address : Word) : Decidable (interval.AdmitsWord address) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def checkRegistration (state : Atomics.State) (registration : Registration) :
    Except Atomics.Fault Atomics.Handle := do
  let handle ← Atomics.authorize state registration.actor registration.keeper
  if handle ≠ registration.handle then throw .conflictingCell
  return handle

def retainCall (state : Atomics.State) (registration : Registration) (actor : Nat) :
    Except Atomics.Fault (Atomics.State × Nat) := do
  let _ ← checkRegistration state registration
  Atomics.issue state registration.owner registration.ticket actor registration.address

/-- Read a live handle's current physical word, without freezing its allocation
under an ordinary read loan. -/
def readPinned (state : Atomics.State) (actor identifier : Nat) :
    Except Atomics.Fault (BitVec 32) := do
  let handle ← Atomics.authorize state actor identifier
  (loadDWord (toMemory state.shared.resources.space) handle.address).mapError Atomics.Fault.machine

/-- Service cleanup can close a matching call pin, never its registration's
keeper. The service adapter supplies the actual call's pin and phase guard. -/
def closeCall (state : Atomics.State) (registration : Registration) (actor identifier : Nat) :
    Except Atomics.Fault Atomics.State := do
  if identifier = registration.keeper then throw .reserved
  let handle ← Atomics.authorize state actor identifier
  if handle ≠ registration.callHandle actor then throw .conflictingCell
  Atomics.close state actor identifier

theorem checkRegistration_enabled (state : Atomics.State) (registration : Registration)
    (live : Valid state registration) :
    checkRegistration state registration = .ok registration.handle := by
  simp [checkRegistration, Atomics.authorize, Valid, Registration.handle] at live ⊢
  simp [live]

theorem checkRegistration_ok (state : Atomics.State) (registration : Registration)
    (handle : Atomics.Handle) (success : checkRegistration state registration = .ok handle) :
    Valid state registration ∧ handle = registration.handle := by
  cases authorized : Atomics.authorize state registration.actor registration.keeper with
  | error fault => simp [checkRegistration, authorized] at success
  | ok current =>
    by_cases same : current = registration.handle
    · simp [checkRegistration, authorized, same] at success
      subst current
      exact ⟨(Atomics.authorize_ok _ _ _ _ authorized).1, success.symm⟩
    · simp [checkRegistration, authorized, same] at success

theorem compatible_of_keeper (state : Atomics.State) (registration : Registration)
    (valid : Atomics.WellFormed state) (live : Valid state registration) :
    Atomics.compatible state registration.owner registration.ticket registration.address = true := by
  apply List.all_eq_true.mpr
  intro identifier _
  cases found : state.handles identifier with
  | none => rfl
  | some handle =>
    by_cases same : handle.ticket.identifier = registration.ticket.identifier
    · have agrees := valid.agreement identifier handle registration.keeper registration.handle found live same
      simpa [Registration.handle, found, same] using agrees
    · simp [same]

theorem unborrowed_of_keeper (state : Atomics.State) (registration : Registration)
    (value : BitVec 32) (valid : Atomics.WellFormed state) (live : Valid state registration) :
    Borrowing.allowed state.shared (.store registration.owner registration.ticket registration.address value) = true := by
  apply List.all_eq_true.mpr
  intro identifier _
  cases found : state.shared.loans identifier with
  | none => rfl
  | some loan =>
    have different := valid.noReaders registration.keeper registration.handle live identifier loan found
    change decide (some registration.ticket.identifier ≠ some loan.ticket.identifier) = true
    simpa only [Registration.handle, decide_eq_true_eq, ne_eq, Option.some.injEq] using Ne.symm different

/-- Retention is positively enabled by the current keeper invariant. No
successful issuance premise is smuggled into a service transition. -/
theorem retainCall_enabled (state : Atomics.State) (registration : Registration) (actor : Nat)
    (valid : Atomics.WellFormed state) (live : Valid state registration) :
    retainCall state registration actor =
      .ok (Atomics.install state (registration.callHandle actor), state.nextHandle) := by
  obtain ⟨allocation, found, owns, epoch, fits, aligned, writable⟩ :=
    (valid.handles registration.keeper registration.handle live).2
  have authorized : Ownership.authorize state.shared.resources registration.owner registration.ticket = .ok allocation := by
    simp [Ownership.authorize, Registration.handle] at found owns epoch ⊢
    simp [found, owns, epoch]
  have issued := Atomics.issue_success state registration.owner registration.ticket actor registration.address
    allocation valid authorized (compatible_of_keeper state registration valid live)
    (unborrowed_of_keeper state registration 0 valid live) fits aligned writable
  simpa [retainCall, checkRegistration_enabled state registration live, Registration.callHandle] using issued

theorem retainCall_ok (state : Atomics.State) (registration : Registration) (actor : Nat)
    (result : Atomics.State × Nat) (success : retainCall state registration actor = .ok result) :
    Valid state registration ∧
      Atomics.issue state registration.owner registration.ticket actor registration.address = .ok result := by
  cases checked : checkRegistration state registration with
  | error fault => simp [retainCall, checked] at success
  | ok handle =>
    exact ⟨(checkRegistration_ok _ _ _ checked).1, by simpa [retainCall, checked] using success⟩

theorem retainCall_effect (state : Atomics.State) (registration : Registration) (actor : Nat)
    (result : Atomics.State × Nat) (valid : Atomics.WellFormed state)
    (success : retainCall state registration actor = .ok result) :
    Atomics.WellFormed result.1 ∧ Valid result.1 registration ∧
      result.1.handles result.2 = some (registration.callHandle actor) ∧
      result.2 = state.nextHandle ∧ result.2 ≠ registration.keeper ∧
      result.1.shared = state.shared ∧ result.1.nextHandle = state.nextHandle + 1 ∧
      (∀ query, query ≠ result.2 → result.1.handles query = state.handles query) := by
  obtain ⟨live, issued⟩ := retainCall_ok _ _ _ _ success
  have exactResult := Except.ok.inj ((retainCall_enabled state registration actor valid live).symm.trans success)
  subst result
  have keeperBelow := (valid.handles registration.keeper registration.handle live).1
  have different : registration.keeper ≠ state.nextHandle := by omega
  refine ⟨(Atomics.issue_wellFormed _ _ _ _ _ _ valid issued).1, ?_, ?_, rfl, Ne.symm different, rfl, rfl, ?_⟩
  · simpa [Valid, Atomics.install, different] using live
  · simp [Atomics.install]
  · intro query separate
    simp [Atomics.install, separate]

theorem readPinned_ok (state : Atomics.State) (actor identifier : Nat) (value : BitVec 32)
    (success : readPinned state actor identifier = .ok value) :
    ∃ handle, Atomics.authorize state actor identifier = .ok handle ∧
      loadDWord (toMemory state.shared.resources.space) handle.address = .ok value := by
  cases authorized : Atomics.authorize state actor identifier with
  | error fault => simp [readPinned, authorized] at success
  | ok handle =>
    refine ⟨handle, rfl, ?_⟩
    cases loaded : loadDWord (toMemory state.shared.resources.space) handle.address with
    | error fault => simp [readPinned, authorized, loaded, Except.mapError] at success
    | ok current =>
      simp [readPinned, authorized, loaded, Except.mapError] at success
      exact congrArg Except.ok success

theorem readPinned_enabled (state : Atomics.State) (actor identifier : Nat)
    (handle : Atomics.Handle) (valid : Atomics.WellFormed state)
    (authorized : Atomics.authorize state actor identifier = .ok handle) :
    ∃ value, readPinned state actor identifier = .ok value ∧
      loadDWord (toMemory state.shared.resources.space) handle.address = .ok value := by
  have live := (Atomics.authorize_ok _ _ _ _ authorized).1
  obtain ⟨_, _, _, _, _, _, writable⟩ := (valid.handles _ _ live).2
  obtain ⟨value, loaded⟩ := Atomics.load_exists_of_canStore _ _ writable
  exact ⟨value, by simp [readPinned, authorized, loaded, Except.mapError], loaded⟩

/-- A peer exchange is visible through a retained pin; the pin is not a
historical snapshot and does not prevent an authorized writer changing W. -/
theorem readPinned_after_exchange (state : Atomics.State) (writerActor writerId readerActor readerId : Nat)
    (writer reader : Atomics.Handle) (value : BitVec 32) (result : Atomics.State × BitVec 32)
    (writes : Atomics.authorize state writerActor writerId = .ok writer)
    (reads : Atomics.authorize state readerActor readerId = .ok reader)
    (sameAddress : writer.address = reader.address)
    (success : Atomics.exchange state writerActor writerId value = .ok result) :
    readPinned result.1 readerActor readerId = .ok value := by
  obtain ⟨selected, shared, authorized, _, resultEq⟩ := Atomics.exchange_ok _ _ _ _ _ success
  have sameWriter := Except.ok.inj (writes.symm.trans authorized)
  subst selected
  obtain ⟨selected, authorized, transition⟩ := Atomics.exchange_sound _ _ _ _ _ success
  have sameWriter := Except.ok.inj (writes.symm.trans authorized)
  subst selected
  have readerLive : Atomics.authorize result.1 readerActor readerId = .ok reader := by
    rw [resultEq]
    exact reads
  have loaded : loadDWord (toMemory result.1.shared.resources.space) reader.address = .ok value := by
    rw [← sameAddress]
    exact transition.readback
  simp [readPinned, readerLive, loaded, Except.mapError]

theorem exchange_keeps_registration (state : Atomics.State) (registration : Registration)
    (actor identifier : Nat) (value : BitVec 32) (result : Atomics.State × BitVec 32)
    (live : Valid state registration)
    (success : Atomics.exchange state actor identifier value = .ok result) : Valid result.1 registration := by
  obtain ⟨_, _, _, _, same⟩ := Atomics.exchange_ok _ _ _ _ _ success
  rw [same]
  exact live

theorem closeCall_enabled (state : Atomics.State) (registration : Registration) (actor identifier : Nat)
    (live : state.handles identifier = some (registration.callHandle actor))
    (different : identifier ≠ registration.keeper) :
    closeCall state registration actor identifier = .ok
      { state with handles := fun query => if query = identifier then none else state.handles query } := by
  simp [closeCall, different, Atomics.authorize, live, Registration.callHandle, Atomics.close]

theorem closeCall_ok (state : Atomics.State) (registration : Registration) (actor identifier : Nat)
    (after : Atomics.State) (success : closeCall state registration actor identifier = .ok after) :
    identifier ≠ registration.keeper ∧
      state.handles identifier = some (registration.callHandle actor) ∧
      Atomics.close state actor identifier = .ok after := by
  by_cases sameId : identifier = registration.keeper
  · simp [closeCall, sameId] at success
  · cases authorized : Atomics.authorize state actor identifier with
    | error fault => simp [closeCall, sameId, authorized] at success
    | ok handle =>
      by_cases same : handle = registration.callHandle actor
      · subst handle
        exact ⟨sameId, (Atomics.authorize_ok _ _ _ _ authorized).1,
          by simpa [closeCall, sameId, authorized] using success⟩
      · simp [closeCall, sameId, authorized, same] at success

theorem closeCall_effect (state : Atomics.State) (registration : Registration) (actor identifier : Nat)
    (after : Atomics.State) (valid : Atomics.WellFormed state) (registered : Valid state registration)
    (success : closeCall state registration actor identifier = .ok after) :
    Atomics.WellFormed after ∧ Valid after registration ∧ Atomics.Revoked after identifier ∧
      after.shared = state.shared ∧ after.nextHandle = state.nextHandle ∧
      (∀ query, query ≠ identifier → after.handles query = state.handles query) := by
  obtain ⟨different, _, closed⟩ := closeCall_ok _ _ _ _ _ success
  have wellFormed := Atomics.close_wellFormed _ _ _ _ valid closed
  have revoked := Atomics.close_revokes _ _ _ _ valid closed
  obtain ⟨_, _, same⟩ := Atomics.close_ok _ _ _ _ closed
  subst after
  exact ⟨wellFormed, by simpa [Valid, Ne.symm different] using registered, revoked,
    rfl, rfl, fun query separate => by simp [separate]⟩

theorem closedCall_never_revives (state middle after : Atomics.State) (registration : Registration)
    (actor identifier : Nat) (valid : Atomics.WellFormed state)
    (closed : closeCall state registration actor identifier = .ok middle)
    (history : Atomics.History middle after) (queryActor : Nat) :
    Atomics.authorize after queryActor identifier = .error .missingHandle :=
  (Atomics.closed_for_history actor identifier valid (closeCall_ok _ _ _ _ _ closed).2.2 history).unauthorized queryActor

theorem keeper_blocks_mutation (state : Atomics.State) (registration : Registration)
    (operation : Ownership.Mutation) (valid : Atomics.WellFormed state) (live : Valid state registration)
    (target : operation.target = some registration.ticket.identifier) :
    Atomics.mutate state operation = .error .reserved :=
  Atomics.mutate_reserved state operation valid registration.keeper registration.handle live target

theorem keeper_blocks_readLoan (state : Atomics.State) (registration : Registration)
    (lender borrower : Nat) (region : Region) (valid : Atomics.WellFormed state) (live : Valid state registration) :
    Atomics.readBorrow state lender registration.ticket borrower region = .error .reserved :=
  Atomics.readBorrow_reserved state lender registration.ticket borrower region valid
    registration.keeper registration.handle live rfl

/-- Fresh allocation identities cannot overwrite an address in the still-live
registration, even though allocation has no target identity for the pin gate. -/
theorem keeper_blocks_overlapping_allocate (state : Atomics.State) (registration : Registration)
    (owner : Nat) (region : Region) (permissions : Permissions) (valid : Atomics.WellFormed state)
    (live : Valid state registration) (overlap : region.Contains registration.address)
    (result : Atomics.State × Option Ownership.Ticket) :
    Atomics.mutate state (.allocate owner region permissions) ≠ .ok result := by
  intro success
  obtain ⟨_, shared, changed, _⟩ := Atomics.mutate_ok _ _ _ success
  obtain ⟨_, world, allocated, _⟩ := Borrowing.mutate_ok _ _ _ changed
  cases allocatedResult : Ownership.allocate state.shared.resources owner region permissions with
  | error fault => simp [Ownership.Mutation.run, allocatedResult, Except.map] at allocated
  | ok pair =>
    obtain ⟨space, mapped, _⟩ := Ownership.allocate_ok _ _ _ _ _ allocatedResult
    have unmapped := (map_ok _ _ _ _ mapped).2.2.2
    have missing := allUnmapped_inside _ _ unmapped registration.address overlap
    obtain ⟨allocation, found, _, _, fits, _, _⟩ := (valid.handles _ _ live).2
    change Ownership.containsWord allocation registration.address = true at fits
    have fitsNat := of_decide_eq_true fits
    have inside : allocation.region.Contains registration.address := ⟨fitsNat.1, by have := fitsNat.2; omega⟩
    obtain ⟨cell, present⟩ := (valid.shared.1.1 _ _ found).2.2 registration.address inside
    rw [missing] at present
    cases present

/-- Adoption cannot create another ticket overlapping W while its original
allocation remains claimed. -/
theorem keeper_blocks_overlapping_adopt (state : Atomics.State) (registration : Registration)
    (owner : Nat) (region : Region) (valid : Atomics.WellFormed state)
    (live : Valid state registration) (overlap : region.Contains registration.address)
    (result : Atomics.State × Option Ownership.Ticket) :
    Atomics.mutate state (.adopt owner region) ≠ .ok result := by
  intro success
  obtain ⟨_, shared, changed, _⟩ := Atomics.mutate_ok _ _ _ success
  obtain ⟨_, world, adopted, _⟩ := Borrowing.mutate_ok _ _ _ changed
  cases adoptedResult : Ownership.adopt state.shared.resources owner region with
  | error fault => simp [Ownership.Mutation.run, adoptedResult, Except.map] at adopted
  | ok pair =>
    have free := (Ownership.adopt_ok _ _ _ _ adoptedResult).2.2.2
    obtain ⟨allocation, found, _, _, fits, _, _⟩ := (valid.handles _ _ live).2
    change Ownership.containsWord allocation registration.address = true at fits
    have fitsNat := of_decide_eq_true fits
    have inside : allocation.region.Contains registration.address := ⟨fitsNat.1, by have := fitsNat.2; omega⟩
    have separate := Ownership.unclaimed_sound _ _ valid.shared.1 free _ _ found
    exact Ownership.disjoint_outside separate inside overlap

end EDSL.OS.Futex.Resources
