/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Facts

namespace EDSL.OS.Ownership
open X86 AddressSpace

theorem transfer_ok (world : World) (owner : Nat) (ticket : Ticket) (newOwner : Nat)
    (result : World × Ticket) (success : transfer world owner ticket newOwner = .ok result) :
    ∃ allocation, authorize world owner ticket = .ok allocation ∧
      result = (replace world ticket.identifier (some { allocation with owner := newOwner, epoch := allocation.epoch + 1 }),
        ⟨ticket.identifier, allocation.epoch + 1⟩) := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [transfer, authorized] at success
  | ok allocation =>
    simp [transfer, authorized] at success
    exact ⟨allocation, rfl, success.symm⟩

theorem transfer_success (world : World) (owner : Nat) (ticket : Ticket) (newOwner : Nat)
    (current : Current world owner ticket) : ∃ result, transfer world owner ticket newOwner = .ok result := by
  obtain ⟨allocation, authorized⟩ := current_authorized current
  refine ⟨(replace world ticket.identifier (some { allocation with owner := newOwner, epoch := allocation.epoch + 1 }),
    ⟨ticket.identifier, allocation.epoch + 1⟩), ?_⟩
  simp [transfer, authorized]

theorem transfer_wellFormed (world : World) (owner : Nat) (ticket : Ticket) (newOwner : Nat)
    (result : World × Ticket) (valid : WellFormed world)
    (success : transfer world owner ticket newOwner = .ok result) :
    WellFormed result.1 ∧ Current result.1 newOwner result.2 ∧
    result.1.space = world.space ∧ result.1.frontier = world.frontier ∧
    (∀ principal, ¬ Current result.1 principal ticket) := by
  obtain ⟨allocation, authorized, resultEq⟩ := transfer_ok world owner ticket newOwner result success
  obtain ⟨found, owns, epoch⟩ := authorize_ok world owner ticket allocation authorized
  subst result
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · constructor
    · intro identifier entry live
      by_cases same : identifier = ticket.identifier
      · subst identifier
        simp [replace] at live
        cases live
        exact valid.1 ticket.identifier allocation found
      · have old : world.allocations identifier = some entry := by simpa [replace, same] using live
        exact valid.1 _ _ old
    · intro left a right b liveA liveB different
      by_cases sameA : left = ticket.identifier
      · subst left
        simp [replace] at liveA
        cases liveA
        have sameB : right ≠ ticket.identifier := Ne.symm different
        have oldB : world.allocations right = some b := by simpa [replace, sameB] using liveB
        exact valid.2 ticket.identifier allocation right b found oldB different
      · have oldA : world.allocations left = some a := by simpa [replace, sameA] using liveA
        by_cases sameB : right = ticket.identifier
        · subst right
          simp [replace] at liveB
          cases liveB
          exact valid.2 left a ticket.identifier allocation oldA found different
        · have oldB : world.allocations right = some b := by simpa [replace, sameB] using liveB
          exact valid.2 _ _ _ _ oldA oldB different
  · exact ⟨{ allocation with owner := newOwner, epoch := allocation.epoch + 1 }, by simp [replace], rfl, rfl⟩
  · rintro principal ⟨entry, live, _, currentEpoch⟩
    simp [replace] at live
    cases live
    change allocation.epoch + 1 = ticket.epoch at currentEpoch
    omega

theorem release_ok (world : World) (owner : Nat) (ticket : Ticket) (result : World)
    (success : release world owner ticket = .ok result) :
    ∃ allocation space, authorize world owner ticket = .ok allocation ∧
      AddressSpace.unmap world.space allocation.region = .ok space ∧
      result = { replace world ticket.identifier none with space := space } := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [release, authorized] at success
  | ok allocation =>
    cases unmapped : AddressSpace.unmap world.space allocation.region with
    | error fault => simp [release, authorized, unmapped, Except.mapError] at success
    | ok space =>
      simp [release, authorized, unmapped, Except.mapError] at success
      exact ⟨allocation, space, rfl, unmapped, success.symm⟩

theorem release_success (world : World) (owner : Nat) (ticket : Ticket)
    (valid : WellFormed world) (current : Current world owner ticket) :
    ∃ result, release world owner ticket = .ok result := by
  obtain ⟨allocation, authorized⟩ := current_authorized current
  have found := (authorize_ok _ _ _ _ authorized).1
  have region := valid.1 _ _ found
  have mapped := mapped_of_inside world.space allocation.region region.2.1 region.2.2
  have unmapped := unmap_success world.space allocation.region region.2.1 mapped
  refine ⟨{ replace world ticket.identifier none with space := unmapUnchecked world.space allocation.region }, ?_⟩
  simp [release, authorized, unmapped, Except.mapError]

theorem release_wellFormed (world : World) (owner : Nat) (ticket : Ticket) (result : World)
    (valid : WellFormed world) (success : release world owner ticket = .ok result) :
    WellFormed result ∧ result.frontier = world.frontier ∧
    result.allocations ticket.identifier = none ∧
    (∀ address, (∃ allocation, authorize world owner ticket = .ok allocation ∧
      allocation.region.Contains address) → result.space.cells address = none) := by
  obtain ⟨allocation, space, authorized, unmapped, resultEq⟩ := release_ok world owner ticket result success
  have found := (authorize_ok world owner ticket allocation authorized).1
  obtain ⟨spaceEq, _, _⟩ := unmap_ok _ _ _ unmapped
  subst result
  subst space
  refine ⟨?_, rfl, by simp [replace], ?_⟩
  · constructor
    · intro identifier entry live
      have same : identifier ≠ ticket.identifier := by
        intro equal
        subst identifier
        simp [replace] at live
      have old : world.allocations identifier = some entry := by simpa [replace, same] using live
      obtain ⟨below, regionValid, mapped⟩ := valid.1 _ _ old
      refine ⟨below, regionValid, ?_⟩
      intro address inside
      obtain ⟨cell, stored⟩ := mapped address inside
      have outside := disjoint_outside (valid.2 _ _ _ _ found old (Ne.symm same)) inside
      exact ⟨cell, (unmap_frame _ _ _ outside).trans stored⟩
    · intro left a right b liveA liveB different
      have notA : left ≠ ticket.identifier := by intro equal; subst left; simp [replace] at liveA
      have notB : right ≠ ticket.identifier := by intro equal; subst right; simp [replace] at liveB
      exact valid.2 _ _ _ _ (by simpa [replace, notA] using liveA)
        (by simpa [replace, notB] using liveB) different
  · rintro address ⟨other, same, inside⟩
    have equal := Except.ok.inj (authorized.symm.trans same)
    cases equal
    exact unmap_inside _ _ _ inside

theorem protect_ok (world : World) (owner : Nat) (ticket : Ticket) (permissions : Permissions)
    (result : World) (success : protect world owner ticket permissions = .ok result) :
    ∃ allocation space, authorize world owner ticket = .ok allocation ∧
      AddressSpace.protect world.space allocation.region permissions = .ok space ∧
      result = { world with space := space } := by
  cases authorized : authorize world owner ticket with
  | error fault => simp [protect, authorized] at success
  | ok allocation =>
    cases changed : AddressSpace.protect world.space allocation.region permissions with
    | error fault => simp [protect, authorized, changed, Except.mapError] at success
    | ok space =>
      simp [protect, authorized, changed, Except.mapError] at success
      exact ⟨allocation, space, rfl, changed, success.symm⟩

theorem protect_success (world : World) (owner : Nat) (ticket : Ticket) (permissions : Permissions)
    (valid : WellFormed world) (current : Current world owner ticket)
    (supported : permissions.supported = true) : ∃ result, protect world owner ticket permissions = .ok result := by
  obtain ⟨allocation, authorized⟩ := current_authorized current
  have found := (authorize_ok _ _ _ _ authorized).1
  have region := valid.1 _ _ found
  have mapped := mapped_of_inside world.space allocation.region region.2.1 region.2.2
  have changed := AddressSpace.protect_success world.space allocation.region permissions region.2.1 supported mapped
  refine ⟨{ world with space := protectUnchecked world.space allocation.region permissions }, ?_⟩
  simp [protect, authorized, changed, Except.mapError]

theorem protect_wellFormed (world : World) (owner : Nat) (ticket : Ticket) (permissions : Permissions)
    (result : World) (valid : WellFormed world)
    (success : protect world owner ticket permissions = .ok result) :
    WellFormed result ∧ result.allocations = world.allocations ∧ result.frontier = world.frontier ∧
    (∀ address, contents result.space address = contents world.space address) := by
  obtain ⟨allocation, space, _, changed, resultEq⟩ := protect_ok world owner ticket permissions result success
  obtain ⟨spaceEq, _, _, _⟩ := AddressSpace.protect_ok _ _ _ _ changed
  subst result
  subst space
  refine ⟨changeSpace_wellFormed _ _ valid ?_, rfl, rfl, ?_⟩
  · intro identifier entry found address inside
    obtain ⟨cell, stored⟩ := (valid.1 _ _ found).2.2 address inside
    by_cases affected : allocation.region.Contains address
    · exact ⟨{ cell with permissions := permissions }, by simp [protectUnchecked, affected, stored]⟩
    · exact ⟨cell, (protect_frame _ _ _ _ affected).trans stored⟩
  · exact protect_preserves_contents _ _ _

theorem release_frame (world : World) (owner : Nat) (ticket : Ticket) (result : World)
    (success : release world owner ticket = .ok result) (address : Word)
    (outside : ∀ allocation, authorize world owner ticket = .ok allocation → ¬allocation.region.Contains address) :
    result.space.cells address = world.space.cells address := by
  obtain ⟨allocation, space, authorized, unmapped, same⟩ := release_ok _ _ _ _ success
  have spaceEq := (unmap_ok _ _ _ unmapped).1
  subst result
  subst space
  exact unmap_frame _ _ _ (outside allocation authorized)

theorem protect_frame (world : World) (owner : Nat) (ticket : Ticket) (permissions : Permissions)
    (result : World) (success : protect world owner ticket permissions = .ok result) (address : Word)
    (outside : ∀ allocation, authorize world owner ticket = .ok allocation → ¬allocation.region.Contains address) :
    result.space.cells address = world.space.cells address := by
  obtain ⟨allocation, space, authorized, changed, same⟩ := protect_ok _ _ _ _ _ success
  have spaceEq := (AddressSpace.protect_ok _ _ _ _ changed).1
  subst result
  subst space
  exact AddressSpace.protect_frame _ _ _ _ (outside allocation authorized)

end EDSL.OS.Ownership
