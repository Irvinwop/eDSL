/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Model

namespace EDSL.OS.Ownership
open X86 AddressSpace

theorem addresses_inside (region : Region) (valid : region.valid = true)
    (address : Word) (member : address ∈ region.addresses) : region.Contains address := by
  obtain ⟨offset, bound, equality⟩ := List.mem_map.mp member
  have offsetBound := List.mem_range.mp bound
  simp only [Region.valid, decide_eq_true_eq] at valid
  have small : offset < 2^64 := by omega
  have sum : region.base.toNat + offset < 2^64 := by omega
  subst address
  change region.base.toNat ≤ (region.base + BitVec.ofNat 64 offset).toNat ∧
    (region.base + BitVec.ofNat 64 offset).toNat < region.base.toNat + region.length
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]
  omega

theorem mapped_of_inside (space : Space) (region : Region) (valid : region.valid = true)
    (mapped : ∀ address, region.Contains address → ∃ cell, space.cells address = some cell) :
    allMapped space region = true := by
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨cell, found⟩ := mapped address (addresses_inside region valid address member)
  simp [found]

theorem fresh_identity (world : World) (valid : WellFormed world) :
    world.allocations world.frontier = none := by
  cases found : world.allocations world.frontier with
  | none => rfl
  | some allocation => have bound := (valid.1 _ _ found).1; omega

theorem authorize_success (world : World) (owner : Nat) (ticket : Ticket) (allocation : Allocation)
    (found : world.allocations ticket.identifier = some allocation)
    (owns : allocation.owner = owner) (epoch : allocation.epoch = ticket.epoch) :
    authorize world owner ticket = .ok allocation := by
  simp [authorize, found, owns, epoch]

theorem current_authorized {world : World} {owner : Nat} {ticket : Ticket}
    (current : Current world owner ticket) : ∃ allocation, authorize world owner ticket = .ok allocation := by
  obtain ⟨allocation, found, owns, epoch⟩ := current
  exact ⟨allocation, authorize_success world owner ticket allocation found owns epoch⟩

theorem current_unique_owner {world : World} {left right : Nat} {ticket : Ticket}
    (first : Current world left ticket) (second : Current world right ticket) : left = right := by
  obtain ⟨a, foundA, ownerA, _⟩ := first
  obtain ⟨b, foundB, ownerB, _⟩ := second
  have same := Option.some.inj (foundA.symm.trans foundB)
  cases same
  exact ownerA.symm.trans ownerB

theorem unclaimed_sound (world : World) (region : Region) (valid : WellFormed world)
    (checked : unclaimed world region = true) (identifier : Nat) (allocation : Allocation)
    (found : world.allocations identifier = some allocation) : Disjoint region allocation.region := by
  have below := (valid.1 _ _ found).1
  have check := List.all_eq_true.mp checked identifier (List.mem_range.mpr below)
  simpa [found] using check

theorem install_current (world : World) (space : Space) (owner : Nat) (region : Region) :
    Current (install world space owner region) owner ⟨world.frontier, 0⟩ := by
  exact ⟨⟨owner, 0, region⟩, by simp [install], rfl, rfl⟩

theorem disjoint_of_no_overlap (left right : Region) (leftValid : left.valid = true)
    (rightValid : right.valid = true)
    (safe : ∀ address, left.Contains address → ¬right.Contains address) : Disjoint left right := by
  by_cases before : left.base.toNat + left.length ≤ right.base.toNat
  · exact Or.inl before
  by_cases after : right.base.toNat + right.length ≤ left.base.toNat
  · exact Or.inr after
  have leftLength := (of_decide_eq_true leftValid).1
  have rightLength := (of_decide_eq_true rightValid).1
  by_cases order : right.base.toNat ≤ left.base.toNat
  · exact False.elim (safe left.base ⟨by omega, by omega⟩ ⟨order, by omega⟩)
  · exact False.elim (safe right.base ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)

theorem install_wellFormed (world : World) (space : Space) (owner : Nat) (region : Region)
    (valid : WellFormed world) (regionValid : region.valid = true)
    (mapped : ∀ address, region.Contains address → ∃ cell, space.cells address = some cell)
    (preserved : ∀ address cell, world.space.cells address = some cell → space.cells address = some cell)
    (separate : ∀ identifier allocation, world.allocations identifier = some allocation →
      Disjoint region allocation.region) : WellFormed (install world space owner region) := by
  constructor
  · intro identifier allocation found
    by_cases new : identifier = world.frontier
    · subst identifier
      simp [install] at found
      cases found
      exact ⟨by simp [install], regionValid, mapped⟩
    · have old : world.allocations identifier = some allocation := by simpa [install, new] using found
      obtain ⟨below, regionValid, live⟩ := valid.1 _ _ old
      refine ⟨by simp only [install]; omega, regionValid, ?_⟩
      intro address inside
      obtain ⟨cell, stored⟩ := live address inside
      exact ⟨cell, preserved address cell stored⟩
  · intro left a right b foundA foundB different
    by_cases newA : left = world.frontier
    · subst left
      simp [install] at foundA
      cases foundA
      have newB : right ≠ world.frontier := Ne.symm different
      have oldB : world.allocations right = some b := by simpa [install, newB] using foundB
      exact separate _ _ oldB
    · have oldA : world.allocations left = some a := by simpa [install, newA] using foundA
      by_cases newB : right = world.frontier
      · subst right
        simp [install] at foundB
        cases foundB
        exact disjoint_symm (separate _ _ oldA)
      · have oldB : world.allocations right = some b := by simpa [install, newB] using foundB
        exact valid.2 _ _ _ _ oldA oldB different

theorem allocate_ok (world : World) (owner : Nat) (region : Region) (permissions : Permissions)
    (result : World × Ticket) (success : allocate world owner region permissions = .ok result) :
    ∃ space, AddressSpace.map world.space region permissions = .ok space ∧
      result = (install world space owner region, ⟨world.frontier, 0⟩) := by
  by_cases collision : (world.allocations world.frontier).isSome = true
  · simp [allocate, collision] at success
  · cases mapped : AddressSpace.map world.space region permissions with
    | error fault => simp [allocate, collision, mapped, Except.mapError] at success
    | ok space =>
      simp [allocate, collision, mapped, Except.mapError] at success
      exact ⟨space, rfl, success.symm⟩

theorem allocate_wellFormed (world : World) (owner : Nat) (region : Region) (permissions : Permissions)
    (result : World × Ticket) (valid : WellFormed world)
    (success : allocate world owner region permissions = .ok result) :
    WellFormed result.1 ∧ Current result.1 owner result.2 ∧
    result.1.frontier = world.frontier + 1 := by
  obtain ⟨space, mapped, resultEq⟩ := allocate_ok world owner region permissions result success
  subst result
  obtain ⟨spaceEq, regionValid, _, free⟩ := map_ok world.space space region permissions mapped
  have newMapped : ∀ address, region.Contains address → ∃ cell, space.cells address = some cell := by
    intro address inside
    exact ⟨⟨0, permissions⟩, by rw [spaceEq]; exact map_inside _ _ _ _ inside⟩
  have separate : ∀ identifier allocation, world.allocations identifier = some allocation →
      Disjoint region allocation.region := by
    intro identifier allocation found
    obtain ⟨_, allocationValid, live⟩ := valid.1 _ _ found
    apply disjoint_of_no_overlap region allocation.region regionValid allocationValid
    intro address insideNew insideOld
    obtain ⟨cell, existing⟩ := live address insideOld
    have missing := allUnmapped_inside world.space region free address insideNew
    rw [existing] at missing
    cases missing
  exact ⟨install_wellFormed world space owner region valid regionValid newMapped
    (fun address cell existing => map_preserves_existing _ _ _ _ mapped address cell existing) separate,
    install_current _ _ _ _, rfl⟩

theorem allocate_success (world : World) (owner : Nat) (region : Region) (permissions : Permissions)
    (valid : WellFormed world) (regionValid : region.valid = true)
    (supported : permissions.supported = true) (free : allUnmapped world.space region = true) :
    allocate world owner region permissions =
      .ok (install world (mapUnchecked world.space region permissions) owner region, ⟨world.frontier, 0⟩) := by
  have identity := fresh_identity world valid
  have mapped := map_success world.space region permissions regionValid supported free
  simp [allocate, identity, mapped, Except.mapError]

theorem allocate_initialized (world : World) (owner : Nat) (region : Region) (permissions : Permissions)
    (result : World × Ticket) (success : allocate world owner region permissions = .ok result) :
    (∀ address, region.Contains address → result.1.space.cells address = some ⟨0, permissions⟩) ∧
    (∀ address cell, world.space.cells address = some cell → result.1.space.cells address = some cell) := by
  obtain ⟨space, mapped, same⟩ := allocate_ok _ _ _ _ _ success
  subst result
  have spaceEq := (map_ok _ _ _ _ mapped).1
  exact ⟨fun address inside => by simpa only [spaceEq, install] using map_inside world.space region permissions address inside,
    fun address cell existing => map_preserves_existing _ _ _ _ mapped address cell existing⟩

theorem adopt_ok (world : World) (owner : Nat) (region : Region) (result : World × Ticket)
    (success : adopt world owner region = .ok result) :
    result = (install world world.space owner region, ⟨world.frontier, 0⟩) ∧
    region.valid = true ∧ allMapped world.space region = true ∧ unclaimed world region = true := by
  by_cases collision : (world.allocations world.frontier).isSome = true
  · simp [adopt, collision] at success
  · by_cases valid : region.valid = true
    · by_cases mapped : allMapped world.space region = true
      · by_cases free : unclaimed world region = true
        · simp [adopt, collision, valid, mapped, free] at success
          exact ⟨success.symm, valid, mapped, free⟩
        · simp [adopt, collision, valid, mapped, free] at success
      · simp [adopt, collision, valid, mapped] at success
    · simp [adopt, collision, valid] at success

theorem adopt_wellFormed (world : World) (owner : Nat) (region : Region) (result : World × Ticket)
    (valid : WellFormed world) (success : adopt world owner region = .ok result) :
    WellFormed result.1 ∧ Current result.1 owner result.2 ∧ result.1.space = world.space ∧
    result.1.frontier = world.frontier + 1 := by
  obtain ⟨resultEq, regionValid, mapped, free⟩ := adopt_ok world owner region result success
  subst result
  exact ⟨install_wellFormed world world.space owner region valid regionValid
    (fun address inside => allMapped_inside _ _ mapped address inside)
    (fun _ _ stored => stored) (unclaimed_sound world region valid free),
    install_current _ _ _ _, rfl, rfl⟩

theorem adopt_success (world : World) (owner : Nat) (region : Region)
    (valid : WellFormed world) (regionValid : region.valid = true)
    (mapped : allMapped world.space region = true) (free : unclaimed world region = true) :
    adopt world owner region = .ok (install world world.space owner region, ⟨world.frontier, 0⟩) := by
  have identity := fresh_identity world valid
  simp [adopt, identity, regionValid, mapped, free]

theorem changeSpace_wellFormed (world : World) (space : Space) (valid : WellFormed world)
    (mapped : ∀ identifier allocation, world.allocations identifier = some allocation →
      ∀ address, allocation.region.Contains address → ∃ cell, space.cells address = some cell) :
    WellFormed { world with space := space } := by
  refine ⟨?_, valid.2⟩
  intro identifier allocation found
  have original := valid.1 identifier allocation found
  exact ⟨original.1, original.2.1, mapped identifier allocation found⟩

end EDSL.OS.Ownership
