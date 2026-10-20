/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Lifetime

namespace EDSL.OS.Ownership
open X86 AddressSpace

theorem containsWord_inside (allocation : Allocation) (address query : Word)
    (checked : containsWord allocation address = true) (inside : (wordRegion address).Contains query) :
    allocation.region.Contains query := by
  have bounds : allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length := of_decide_eq_true checked
  have lower := inside.1
  change address.toNat ≤ query.toNat at lower
  have upper := inside.2
  change query.toNat < address.toNat + 4 at upper
  exact ⟨by omega, by omega⟩

theorem storeWord_ok (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
    (result : World) (success : storeWord world owner ticket address value = .ok result) :
    ∃ allocation space, authorize world owner ticket = .ok allocation ∧
      containsWord allocation address = true ∧
      AddressSpace.storeWord world.space address value = .ok space ∧ result = { world with space := space } := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [storeWord, authorized] at success
  | ok allocation =>
    by_cases fits : containsWord allocation address = true
    · cases stored : AddressSpace.storeWord world.space address value with
      | error fault => simp [storeWord, authorized, fits, stored, Except.mapError] at success
      | ok space =>
        simp [storeWord, authorized, fits, stored, Except.mapError] at success
        exact ⟨allocation, space, rfl, fits, rfl, success.symm⟩
    · simp [storeWord, authorized, fits] at success

theorem storeWord_success (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
    (allocation : Allocation) (authorized : authorize world owner ticket = .ok allocation)
    (fits : containsWord allocation address = true) (allowed : canStoreDWord (toMemory world.space) address = true) :
    storeWord world owner ticket address value =
      .ok { world with space := writeWordCells world.space address value } := by
  have stored := AddressSpace.storeWord_success world.space address value allowed
  simp [storeWord, authorized, fits, stored, Except.mapError]

theorem storeWord_wellFormed (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
    (result : World) (valid : WellFormed world)
    (success : storeWord world owner ticket address value = .ok result) :
    WellFormed result ∧ Current result owner ticket ∧
    result.allocations = world.allocations ∧ result.frontier = world.frontier ∧
    X86.storeDWord (toMemory world.space) address value = .ok (toMemory result.space) ∧
    loadDWord (toMemory result.space) address = .ok value ∧
    (∀ query, (result.space.cells query).map Cell.permissions = (world.space.cells query).map Cell.permissions) ∧
    (∀ query allocation, authorize world owner ticket = .ok allocation → ¬allocation.region.Contains query →
      result.space.cells query = world.space.cells query) := by
  obtain ⟨allocation, space, authorized, fits, stored, resultEq⟩ := storeWord_ok _ _ _ _ _ _ success
  have current := authorize_current world owner ticket allocation authorized
  have sound := storeWord_sound world.space space address value stored
  subst result
  refine ⟨changeSpace_wellFormed world space valid ?_, current, rfl, rfl,
    sound.1, sound.2.1, sound.2.2.1, ?_⟩
  · intro identifier entry found query inside
    obtain ⟨old, existing⟩ := (valid.1 _ _ found).2.2 query inside
    have same := sound.2.2.1 query
    cases live : space.cells query with
    | none => simp [live, existing] at same
    | some cell => exact ⟨cell, rfl⟩
  · intro query other same outside
    have equal := Except.ok.inj (authorized.symm.trans same)
    cases equal
    exact sound.2.2.2 query (fun inside => outside (containsWord_inside allocation address query fits inside))

theorem containsQWord_inside (allocation : Allocation) (address query : Word)
    (checked : containsQWord allocation address = true) (inside : (qwordRegion address).Contains query) :
    allocation.region.Contains query := by
  have bounds : allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 8 ≤ allocation.region.base.toNat + allocation.region.length := of_decide_eq_true checked
  have lower := inside.1
  change address.toNat ≤ query.toNat at lower
  have upper := inside.2
  change query.toNat < address.toNat + 8 at upper
  exact ⟨by omega, by omega⟩

theorem storeWord64_ok (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : Word)
    (result : World) (success : storeWord64 world owner ticket address value = .ok result) :
    ∃ allocation space, authorize world owner ticket = .ok allocation ∧
      containsQWord allocation address = true ∧
      AddressSpace.storeQWord world.space address value = .ok space ∧ result = { world with space := space } := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [storeWord64, authorized] at success
  | ok allocation =>
    by_cases fits : containsQWord allocation address = true
    · cases stored : AddressSpace.storeQWord world.space address value with
      | error fault => simp [storeWord64, authorized, fits, stored, Except.mapError] at success
      | ok space =>
        simp [storeWord64, authorized, fits, stored, Except.mapError] at success
        exact ⟨allocation, space, rfl, fits, rfl, success.symm⟩
    · simp [storeWord64, authorized, fits] at success

theorem storeWord64_success (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : Word)
    (allocation : Allocation) (authorized : authorize world owner ticket = .ok allocation)
    (fits : containsQWord allocation address = true) (allowed : canStoreQWord (toMemory world.space) address = true) :
    storeWord64 world owner ticket address value =
      .ok { world with space := writeQWordCells world.space address value } := by
  have stored := AddressSpace.storeQWord_success world.space address value allowed
  simp [storeWord64, authorized, fits, stored, Except.mapError]

/-- Exact qword footprint and registry effects require no invariant premise;
success itself supplies the checked owner, epoch, bounds and machine gate. -/
theorem storeWord64_sound (world : World) (owner : Nat) (ticket : Ticket) (address value : Word)
    (result : World) (success : storeWord64 world owner ticket address value = .ok result) :
    Current result owner ticket ∧ result.allocations = world.allocations ∧ result.frontier = world.frontier ∧
    X86.storeQWord (toMemory world.space) address value = .ok (toMemory result.space) ∧
    loadQWord (toMemory result.space) address = .ok value ∧
    (∀ query, (result.space.cells query).map Cell.permissions = (world.space.cells query).map Cell.permissions) ∧
    (∀ query, ¬(qwordRegion address).Contains query → result.space.cells query = world.space.cells query) := by
  obtain ⟨allocation, space, authorized, _, stored, same⟩ := storeWord64_ok _ _ _ _ _ _ success
  have current := authorize_current world owner ticket allocation authorized
  have sound := storeQWord_sound world.space space address value stored
  subst result
  exact ⟨current, rfl, rfl, sound⟩

theorem storeWord64_wellFormed (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : Word)
    (result : World) (valid : WellFormed world)
    (success : storeWord64 world owner ticket address value = .ok result) :
    WellFormed result ∧ Current result owner ticket ∧
    result.allocations = world.allocations ∧ result.frontier = world.frontier ∧
    X86.storeQWord (toMemory world.space) address value = .ok (toMemory result.space) ∧
    loadQWord (toMemory result.space) address = .ok value ∧
    (∀ query, (result.space.cells query).map Cell.permissions = (world.space.cells query).map Cell.permissions) ∧
    (∀ query allocation, authorize world owner ticket = .ok allocation → ¬allocation.region.Contains query →
      result.space.cells query = world.space.cells query) := by
  obtain ⟨allocation, space, authorized, fits, stored, resultEq⟩ := storeWord64_ok _ _ _ _ _ _ success
  have current := authorize_current world owner ticket allocation authorized
  have sound := storeQWord_sound world.space space address value stored
  subst result
  refine ⟨changeSpace_wellFormed world space valid ?_, current, rfl, rfl,
    sound.1, sound.2.1, sound.2.2.1, ?_⟩
  · intro identifier entry found query inside
    obtain ⟨old, existing⟩ := (valid.1 _ _ found).2.2 query inside
    have same := sound.2.2.1 query
    cases live : space.cells query with
    | none => simp [live, existing] at same
    | some cell => exact ⟨cell, rfl⟩
  · intro query other same outside
    have equal := Except.ok.inj (authorized.symm.trans same)
    cases equal
    exact sound.2.2.2 query (fun inside => outside (containsQWord_inside allocation address query fits inside))

end EDSL.OS.Ownership
