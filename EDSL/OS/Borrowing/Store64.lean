/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Facts

namespace EDSL.OS.Borrowing
open X86 AddressSpace

/-- Exact effects of the existing checked mutation gate for ordinary eight-byte
RAM stores. This grants neither atomicity nor authority to bypass other gates. -/
structure StoreEffect64 (before after : State) (address value : Word) : Prop where
  allocations : after.resources.allocations = before.resources.allocations
  frontier : after.resources.frontier = before.resources.frontier
  loans : after.loans = before.loans
  nextLoan : after.nextLoan = before.nextLoan
  machine : X86.storeQWord (toMemory before.resources.space) address value =
    .ok (toMemory after.resources.space)
  readback : loadQWord (toMemory after.resources.space) address = .ok value
  permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
    (before.resources.space.cells query).map Cell.permissions
  outside : ∀ query, ¬(qwordRegion address).Contains query →
    after.resources.space.cells query = before.resources.space.cells query

theorem store64_shape {before after : State} {owner : Nat}
    {ticket : Ownership.Ticket} {address value : Word}
    (success : mutate before (.store64 owner ticket address value) = .ok (after, none)) :
    ∃ world, Ownership.storeWord64 before.resources owner ticket address value = .ok world ∧
      after = { before with resources := world } := by
  obtain ⟨_, resources, changed, same⟩ := mutate_ok _ _ _ success
  cases stored : Ownership.storeWord64 before.resources owner ticket address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at changed
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at changed
    subst resources
    exact ⟨world, rfl, congrArg Prod.fst same⟩

theorem store64_none {before : State} {owner : Nat} {ticket : Ownership.Ticket}
    {address value : Word} {result : State × Option Ownership.Ticket}
    (success : mutate before (.store64 owner ticket address value) = .ok result) : result.2 = none := by
  obtain ⟨_, resources, changed, same⟩ := mutate_ok _ _ _ success
  cases stored : Ownership.storeWord64 before.resources owner ticket address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at changed
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at changed
    subst resources
    rw [same]

theorem store64_effect {before after : State} {owner : Nat}
    {ticket : Ownership.Ticket} {address value : Word}
    (success : mutate before (.store64 owner ticket address value) = .ok (after, none)) :
    StoreEffect64 before after address value := by
  obtain ⟨world, stored, same⟩ := store64_shape success
  obtain ⟨_, space, _, _, osStore, worldEq⟩ := Ownership.storeWord64_ok _ _ _ _ _ _ stored
  have sound := AddressSpace.storeQWord_sound _ _ _ _ osStore
  rw [same, worldEq]
  exact ⟨rfl, rfl, rfl, rfl, sound.1, sound.2.1, sound.2.2.1, sound.2.2.2⟩

theorem StoreEffect64.projection {before after : State} {address value : Word}
    (effect : StoreEffect64 before after address value) :
    toMemory after.resources.space =
      X86.writeQWordUnchecked (toMemory before.resources.space) address value := by
  have machine := effect.machine
  unfold X86.storeQWord at machine
  split at machine
  · exact (Except.ok.inj machine).symm
  · cases machine

theorem StoreEffect64.mapped {before after : State} {address value : Word}
    (effect : StoreEffect64 before after address value) (query : Word) :
    (after.resources.space.cells query).isSome = (before.resources.space.cells query).isSome := by
  have same := effect.permissions query
  cases afterAt : after.resources.space.cells query <;>
    cases beforeAt : before.resources.space.cells query <;>
    simp_all

/-- Byte values are irrelevant to the checked store permission preflight.
Mappedness and every permission are retained by this exact cell premise. -/
theorem canStoreQWord_permissions {before after : Space}
    (permissions : ∀ query, (after.cells query).map Cell.permissions =
      (before.cells query).map Cell.permissions) (address : Word) :
    canStoreQWord (toMemory after) address = canStoreQWord (toMemory before) address := by
  have point (query : Word) :
      (toMemory after).writable query = (toMemory before).writable query ∧
      ((toMemory after).read query).isSome = ((toMemory before).read query).isSome := by
    have same := permissions query
    cases afterAt : after.cells query <;> cases beforeAt : before.cells query <;>
      simp_all [toMemory]
    split <;> simp_all
  simp only [canStoreQWord, qwordWritable,
    (point address).1, (point (address + 1)).1, (point (address + 2)).1,
    (point (address + 3)).1, (point (address + 4)).1, (point (address + 5)).1,
    (point (address + 6)).1, (point (address + 7)).1,
    (point address).2, (point (address + 1)).2, (point (address + 2)).2,
    (point (address + 3)).2, (point (address + 4)).2, (point (address + 5)).2,
    (point (address + 6)).2, (point (address + 7)).2]

theorem store64_preservesAllocation {before after : State} {owner : Nat}
    {ticket : Ownership.Ticket} {address value : Word}
    (valid : Ownership.WellFormed before.resources)
    (success : mutate before (.store64 owner ticket address value) = .ok (after, none))
    (identifier : Nat) (different : identifier ≠ ticket.identifier) :
    Ownership.PreservesAllocation before.resources after.resources identifier := by
  obtain ⟨_, resources, changed, same⟩ := mutate_ok _ _ _ success
  have framed := Ownership.Mutation.run_preserves (.store64 owner ticket address value)
    before.resources resources identifier valid changed (by
      simpa [Ownership.Mutation.target, eq_comm] using different)
  rw [congrArg (fun pair : State × Option Ownership.Ticket => pair.1.resources) same]
  exact framed

theorem unborrowed64 (shared : State) (owner : Nat) (ticket : Ownership.Ticket) (address value : Word)
    (readers : ∀ identifier loan, shared.loans identifier = some loan →
      loan.ticket.identifier ≠ ticket.identifier) :
    allowed shared (.store64 owner ticket address value) = true := by
  apply List.all_eq_true.mpr
  intro identifier _
  cases present : shared.loans identifier with
  | none => rfl
  | some loan =>
    have different := readers _ _ present
    simpa only [Ownership.Mutation.target, decide_eq_true_eq, ne_eq, Option.some.injEq] using Ne.symm different

theorem store64_admitted (shared : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) (allocation : Ownership.Allocation)
    (authorized : Ownership.authorize shared.resources owner ticket = .ok allocation)
    (fits : Ownership.containsQWord allocation address = true)
    (writable : canStoreQWord (toMemory shared.resources.space) address = true)
    (readers : ∀ identifier loan, shared.loans identifier = some loan →
      loan.ticket.identifier ≠ ticket.identifier) :
    ∃ after, mutate shared (.store64 owner ticket address value) = .ok (after, none) := by
  have stored := Ownership.storeWord64_success _ _ _ _ value _ authorized fits writable
  let after := { shared with resources :=
    { shared.resources with space := writeQWordCells shared.resources.space address value } }
  exact ⟨after, by simp [mutate, unborrowed64 _ _ _ _ _ readers,
    Ownership.Mutation.run, stored, Except.map, Except.mapError, after]⟩

/-- A live loan freezes its entire allocation, even when its region misses the
store operand. The finite scan is complete under the existing invariant. -/
theorem store64_borrowed (shared : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address value : Word) (valid : WellFormed shared) (identifier : Nat) (loan : Loan)
    (live : shared.loans identifier = some loan) (same : loan.ticket.identifier = ticket.identifier) :
    mutate shared (.store64 owner ticket address value) = .error .borrowed := by
  have blocked : allowed shared (.store64 owner ticket address value) ≠ true := by
    intro checked
    have excludes := allowed_sound shared _ valid checked identifier loan live
    simp [Ownership.Mutation.target, same] at excludes
  simp [mutate, blocked]

end EDSL.OS.Borrowing
