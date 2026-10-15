/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Store

namespace EDSL.OS.Ownership
open X86 AddressSpace

/-- Every checked managed transition. Raw mappings/stores and arbitrary
environment interference are deliberately outside this authority discipline. -/
inductive Step : World → World → Prop where
  | allocate {before owner region permissions result}
      (success : Ownership.allocate before owner region permissions = .ok result) : Step before result.1
  | adopt {before owner region result}
      (success : Ownership.adopt before owner region = .ok result) : Step before result.1
  | transfer {before owner ticket newOwner result}
      (success : Ownership.transfer before owner ticket newOwner = .ok result) : Step before result.1
  | release {before owner ticket after}
      (success : Ownership.release before owner ticket = .ok after) : Step before after
  | protect {before owner ticket permissions after}
      (success : Ownership.protect before owner ticket permissions = .ok after) : Step before after
  | store {before owner ticket address value after}
      (success : Ownership.storeWord before owner ticket address value = .ok after) : Step before after

inductive History : World → World → Prop where
  | refl {world} : History world world
  | next {before middle after} (first : Step before middle) (tail : History middle after) : History before after

/-- Old identifiers cannot be introduced again. If one remains live, its epoch
does not decrease. Regions/owners may change only as constrained by Step. -/
def Advances (before after : World) : Prop :=
  before.frontier ≤ after.frontier ∧
  ∀ identifier, identifier < before.frontier → ∀ allocation,
    after.allocations identifier = some allocation →
    ∃ previous, before.allocations identifier = some previous ∧ previous.epoch ≤ allocation.epoch

theorem advances_refl (world : World) : Advances world world :=
  ⟨Nat.le_refl _, fun _ _ allocation found => ⟨allocation, found, Nat.le_refl _⟩⟩

theorem advances_trans {before middle after : World}
    (first : Advances before middle) (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.1 last.1, ?_⟩
  intro identifier below allocation found
  have frontier := first.1
  obtain ⟨previous, old, epoch⟩ := last.2 identifier (by omega) allocation found
  obtain ⟨original, originalAt, originalEpoch⟩ := first.2 identifier below previous old
  exact ⟨original, originalAt, Nat.le_trans originalEpoch epoch⟩

theorem install_advances (world : World) (space : Space) (owner : Nat) (region : Region) :
    Advances world (install world space owner region) := by
  refine ⟨by simp [install], ?_⟩
  intro identifier below allocation found
  have different : identifier ≠ world.frontier := by omega
  exact ⟨allocation, by simpa [install, different] using found, Nat.le_refl _⟩

theorem Step.advances {before after : World} (step : Step before after) : Advances before after := by
  cases step with
  | allocate success =>
    obtain ⟨space, _, same⟩ := allocate_ok _ _ _ _ _ success
    rw [same]
    exact install_advances _ _ _ _
  | adopt success =>
    obtain ⟨same, _, _, _⟩ := adopt_ok _ _ _ _ success
    rw [same]
    exact install_advances _ _ _ _
  | @transfer owner ticket newOwner result success =>
    obtain ⟨allocation, authorized, same⟩ := transfer_ok _ _ _ _ _ success
    have old := (authorize_ok _ _ _ _ authorized).1
    subst result
    refine ⟨Nat.le_refl _, ?_⟩
    intro identifier _ current found
    by_cases sameId : identifier = ticket.identifier
    · subst identifier
      simp [replace] at found
      cases found
      exact ⟨allocation, old, by simp⟩
    · exact ⟨current, by simpa [replace, sameId] using found, Nat.le_refl _⟩
  | @release owner ticket after success =>
    obtain ⟨_, space, _, _, same⟩ := release_ok _ _ _ _ success
    subst after
    refine ⟨Nat.le_refl _, ?_⟩
    intro identifier _ allocation found
    by_cases sameId : identifier = ticket.identifier
    · subst identifier; simp [replace] at found
    · exact ⟨allocation, by simpa [replace, sameId] using found, Nat.le_refl _⟩
  | protect success =>
    obtain ⟨_, _, _, _, same⟩ := protect_ok _ _ _ _ _ success
    rw [same]
    exact advances_refl _
  | store success =>
    obtain ⟨_, _, _, _, _, same⟩ := storeWord_ok _ _ _ _ _ _ success
    rw [same]
    exact advances_refl _

theorem Step.wellFormed {before after : World} (step : Step before after) (valid : WellFormed before) :
    WellFormed after := by
  cases step with
  | allocate success => exact (allocate_wellFormed _ _ _ _ _ valid success).1
  | adopt success => exact (adopt_wellFormed _ _ _ _ valid success).1
  | transfer success => exact (transfer_wellFormed _ _ _ _ _ valid success).1
  | release success => exact (release_wellFormed _ _ _ _ valid success).1
  | protect success => exact (protect_wellFormed _ _ _ _ _ valid success).1
  | store success => exact (storeWord_wellFormed _ _ _ _ _ _ valid success).1

theorem History.advances {before after : World} (history : History before after) : Advances before after := by
  induction history with
  | refl => exact advances_refl _
  | next first _ induction => exact advances_trans first.advances induction

theorem History.wellFormed {before after : World} (history : History before after) (valid : WellFormed before) :
    WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ induction => exact induction (first.wellFormed valid)

/-- The ticket is behind the allocation's epoch, or its identifier has been
removed below the frontier. Future fresh allocations cannot use that identity. -/
def Invalidated (world : World) (ticket : Ticket) : Prop :=
  ticket.identifier < world.frontier ∧ ∀ allocation,
    world.allocations ticket.identifier = some allocation → ticket.epoch < allocation.epoch

theorem Invalidated.never_current {world : World} {ticket : Ticket} (invalid : Invalidated world ticket)
    (owner : Nat) : ¬ Current world owner ticket := by
  rintro ⟨allocation, found, _, sameEpoch⟩
  have newer := invalid.2 allocation found
  omega

theorem Invalidated.persists {before after : World} {ticket : Ticket}
    (invalid : Invalidated before ticket) (history : History before after) : Invalidated after ticket := by
  have advances := history.advances
  have below := invalid.1
  have frontier := advances.1
  refine ⟨by omega, ?_⟩
  intro allocation found
  obtain ⟨previous, old, epoch⟩ := advances.2 ticket.identifier invalid.1 allocation found
  have newer := invalid.2 previous old
  omega

theorem release_invalidates (world : World) (owner : Nat) (ticket : Ticket) (result : World)
    (valid : WellFormed world) (success : release world owner ticket = .ok result) : Invalidated result ticket := by
  obtain ⟨allocation, _, authorized, _, _⟩ := release_ok _ _ _ _ success
  have below := issued_below valid (authorize_current _ _ _ _ authorized)
  have resultFacts := release_wellFormed _ _ _ _ valid success
  refine ⟨by rw [resultFacts.2.1]; exact below, ?_⟩
  intro entry found
  rw [resultFacts.2.2.1] at found
  cases found

theorem transfer_invalidates (world : World) (owner : Nat) (ticket : Ticket) (newOwner : Nat)
    (result : World × Ticket) (valid : WellFormed world)
    (success : transfer world owner ticket newOwner = .ok result) : Invalidated result.1 ticket := by
  obtain ⟨allocation, authorized, same⟩ := transfer_ok _ _ _ _ _ success
  obtain ⟨found, _, epoch⟩ := authorize_ok _ _ _ _ authorized
  have below := (valid.1 _ _ found).1
  subst result
  refine ⟨below, ?_⟩
  intro entry live
  simp [replace] at live
  cases live
  change ticket.epoch < allocation.epoch + 1
  omega

/-- Same-address remapping, repeated transfers and other permitted histories
cannot revive a revoked ticket. This is a logical discipline, not a promise
that an unchecked stale machine pointer faults after address reuse. -/
theorem revoked_for_history {before after : World} {ticket : Ticket}
    (invalid : Invalidated before ticket) (history : History before after) (owner : Nat) :
    ¬ Current after owner ticket :=
  (invalid.persists history).never_current owner

end EDSL.OS.Ownership
