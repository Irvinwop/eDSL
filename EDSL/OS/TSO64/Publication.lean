/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Model

namespace EDSL.OS.TSO64
open X86 AddressSpace

theorem OwnsRegion.authorize {world : World} {actor : Nat} {ticket : Ownership.Ticket}
    {region : Region} (owns : OwnsRegion world actor ticket region) :
    ∃ allocation, Ownership.authorize world.legacy.shared.resources actor ticket = .ok allocation ∧
      Borrowing.Subregion region allocation.region := by
  cases found : world.legacy.shared.resources.allocations ticket.identifier with
  | none => simp [OwnsRegion, found] at owns
  | some allocation =>
    have gates : allocation.owner = actor ∧ allocation.epoch = ticket.epoch ∧
        Borrowing.Subregion region allocation.region := by simpa [OwnsRegion, found] using owns
    exact ⟨allocation, by simp [Ownership.authorize, found, gates.1, gates.2.1], gates.2.2⟩

theorem legacy_unreserved {world : World} {actor : Nat} {ticket : Ownership.Ticket} {store : Store}
    (free : Atomics.reserved world.legacy ticket.identifier = false) :
    Atomics.allowed world.legacy (operation actor ticket store) = true := by
  apply List.all_eq_true.mpr
  intro identifier member
  have absent := List.any_eq_false.mp free identifier member
  cases found : world.legacy.handles identifier with
  | none => rfl
  | some handle =>
    have different : handle.ticket.identifier ≠ ticket.identifier := by simpa [found] using absent
    cases value : store.value <;>
      simpa only [operation, value, Ownership.Mutation.target, decide_eq_true_eq,
        ne_eq, Option.some.injEq] using Ne.symm different

/-- Present gates derive publication enabledness for every tagged value. No
future mutation, future execution, successor invariant, or desired old value
is an admission premise. -/
theorem StoreGate.enabled {world : World} {actor : Nat} {ticket : Ownership.Ticket} {store : Store}
    (gate : StoreGate world actor ticket store) :
    ∃ after, Atomics64.mutate world (operation actor ticket store) = .ok (after, none) := by
  obtain ⟨owns, scalarGate, _, no64, no32, noLoan⟩ := gate
  obtain ⟨allocation, authorized, fits⟩ := owns.authorize
  have noLegacy := legacy_unreserved (actor := actor) (store := store) no32
  cases store with
  | mk address value =>
    cases value with
    | dword value =>
      have bounds : Ownership.containsWord allocation address = true := by
        change decide (Borrowing.Subregion ⟨address, 4⟩ allocation.region) = true
        exact decide_eq_true fits
      have writable : canStoreDWord (published world) address = true := (Bool.and_eq_true_iff.mp scalarGate).2
      have stored := Ownership.storeWord_success _ _ _ _ value _ authorized bounds writable
      simp only [operation] at noLoan noLegacy ⊢
      simp [Atomics64.mutate, Atomics64.allowed, Ownership.Mutation.target, no64, Atomics.mutate,
        noLegacy, Borrowing.mutate, noLoan, Ownership.Mutation.run, stored, Except.map, Except.mapError]
    | qword value =>
      have bounds : Ownership.containsQWord allocation address = true := by
        change decide (Borrowing.Subregion ⟨address, 8⟩ allocation.region) = true
        exact decide_eq_true fits
      have writable : canStoreQWord (published world) address = true := (Bool.and_eq_true_iff.mp scalarGate).2
      have stored := Ownership.storeWord64_success _ _ _ _ value _ authorized bounds writable
      simp only [operation] at noLoan noLegacy ⊢
      simp [Atomics64.mutate, Atomics64.allowed, Ownership.Mutation.target, no64, Atomics.mutate,
        noLegacy, Borrowing.mutate, noLoan, Ownership.Mutation.run, stored, Except.map, Except.mapError]

/-- Exact publication through existing OS semantics, including the projection
back to the Mixed byte update. This is an ordinary store effect, not an RMW. -/
structure Publication (before after : World) (store : Store) : Prop where
  stable : Stable before after
  projection : published after = store.publish (published before)

theorem publication {world : World} {actor : Nat} {ticket : Ownership.Ticket} {store : Store}
    {result : World × Option Ownership.Ticket}
    (success : Atomics64.mutate world (operation actor ticket store) = .ok result) :
    Publication world result.1 store := by
  obtain ⟨_, legacy, changed, same⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, changedShared, legacyEq⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, changedResources, sharedEq⟩ := Borrowing.mutate_ok _ _ _ changedShared
  cases store with
  | mk address value =>
    cases value with
    | dword value =>
      cases stored : Ownership.storeWord world.legacy.shared.resources actor ticket address value with
      | error fault => simp [operation, Ownership.Mutation.run, stored, Except.map] at changedResources
      | ok output =>
        simp only [operation, Ownership.Mutation.run, stored, Except.map, Except.ok.injEq] at changedResources
        subst resources
        obtain ⟨_, space, _, _, written, outputEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
        have sound := AddressSpace.storeWord_sound _ _ _ _ written
        rw [same, legacyEq, sharedEq, outputEq]
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sound.2.2.1⟩, ?_⟩
        have machine := sound.1
        unfold storeDWord at machine
        split at machine
        · exact (Except.ok.inj machine).symm
        · cases machine
    | qword value =>
      cases stored : Ownership.storeWord64 world.legacy.shared.resources actor ticket address value with
      | error fault => simp [operation, Ownership.Mutation.run, stored, Except.map] at changedResources
      | ok output =>
        simp only [operation, Ownership.Mutation.run, stored, Except.map, Except.ok.injEq] at changedResources
        subst resources
        obtain ⟨_, space, _, _, written, outputEq⟩ := Ownership.storeWord64_ok _ _ _ _ _ _ stored
        have sound := AddressSpace.storeQWord_sound _ _ _ _ written
        rw [same, legacyEq, sharedEq, outputEq]
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sound.2.2.1⟩, ?_⟩
        have machine := sound.1
        unfold X86.storeQWord at machine
        split at machine
        · exact (Except.ok.inj machine).symm
        · cases machine

/-- Every live code/caller loan's bytes survive ordinary checked publication.
This reuses the allocation frame of the current borrowing gate. -/
theorem publication_loans {world : World} {actor : Nat} {ticket : Ownership.Ticket} {store : Store}
    {result : World × Option Ownership.Ticket} (valid : Atomics64.WellFormed world)
    (success : Atomics64.mutate world (operation actor ticket store) = .ok result)
    (identifier : Nat) (loan : Borrowing.Loan)
    (live : world.legacy.shared.loans identifier = some loan) (address : Word)
    (inside : loan.region.Contains address) :
    result.1.legacy.shared.resources.space.cells address = world.legacy.shared.resources.space.cells address := by
  obtain ⟨_, legacy, changed, same⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, changedShared, legacyEq⟩ := Atomics.mutate_ok _ _ _ changed
  have advance := (Borrowing.Step.mutate changedShared).advances valid.legacy.shared
  have stable := (publication success).stable
  have afterLive : shared.1.loans identifier = some loan := by
    have retained := stable.loans
    rw [same, legacyEq] at retained
    exact congrFun retained identifier |>.trans live
  have frame := (advance.2 identifier (valid.legacy.shared.2 _ _ live).1 loan afterLive).2 address inside
  simpa only [same, legacyEq] using frame

end EDSL.OS.TSO64
