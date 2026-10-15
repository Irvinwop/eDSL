/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics

namespace EDSL.OS.Mutex
open X86 AddressSpace

/-- Current authority for one complete readable/writable word. Lock alignment
is checked separately, so this predicate also describes an ordinary payload. -/
def WordValid (shared : Borrowing.State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) : Prop :=
  ∃ allocation, shared.resources.allocations ticket.identifier = some allocation ∧
    allocation.owner = owner ∧ allocation.epoch = ticket.epoch ∧
    Ownership.containsWord allocation address = true ∧
    canStoreDWord (toMemory shared.resources.space) address = true

theorem WordValid.authorize {shared : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} (valid : WordValid shared owner ticket address) :
    ∃ allocation, Ownership.authorize shared.resources owner ticket = .ok allocation ∧
      Ownership.containsWord allocation address = true := by
  obtain ⟨allocation, found, owns, epoch, fits, _⟩ := valid
  exact ⟨allocation, by simp [Ownership.authorize, found, owns, epoch], fits⟩

theorem WordValid.writable {shared : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} (valid : WordValid shared owner ticket address) :
    canStoreDWord (toMemory shared.resources.space) address = true := by
  obtain ⟨_, _, _, _, _, writable⟩ := valid
  exact writable

theorem WordValid.load_exists {shared : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} (valid : WordValid shared owner ticket address) :
    ∃ value, loadDWord (toMemory shared.resources.space) address = .ok value :=
  Atomics.load_exists_of_canStore _ _ valid.writable

/-- Exact allocation framing retains the contained operand, including hidden
cells and all permissions. No lock alignment is inferred from this theorem. -/
theorem WordValid.frame {before after : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word}
    (valid : WordValid before owner ticket address)
    (world : Ownership.WellFormed before.resources)
    (preserves : Ownership.PreservesAllocation before.resources after.resources ticket.identifier) :
    WordValid after owner ticket address := by
  obtain ⟨allocation, found, owns, epoch, fits, writable⟩ := valid
  obtain ⟨preserved, cells⟩ := preserves allocation found
  refine ⟨allocation, preserved, owns, epoch, fits, ?_⟩
  let loan : Borrowing.Loan := ⟨ticket, owner, 0, allocation.region⟩
  have regionValid := (world.1 _ _ found).2.1
  have subregion : Borrowing.Subregion (wordRegion address) loan.region := of_decide_eq_true fits
  have point (offset : Nat) (bound : offset < 4) :
      after.resources.space.cells (address + BitVec.ofNat 64 offset) =
        before.resources.space.cells (address + BitVec.ofNat 64 offset) :=
    cells _ (Borrowing.word_inside loan regionValid address subregion offset bound)
  have c0 := point 0 (by decide)
  have c1 := point 1 (by decide)
  have c2 := point 2 (by decide)
  have c3 := point 3 (by decide)
  simp only [BitVec.add_zero] at c0
  change after.resources.space.cells (address + 1) = before.resources.space.cells (address + 1) at c1
  change after.resources.space.cells (address + 2) = before.resources.space.cells (address + 2) at c2
  change after.resources.space.cells (address + 3) = before.resources.space.cells (address + 3) at c3
  simp only [canStoreDWord, dwordWritable, toMemory]
  rw [c0, c1, c2, c3]
  exact writable

/-- Exact allocation framing also retains the current word observation. This
is useful when a lock exchange frames the distinct protected payload. -/
theorem WordValid.load_frame {before after : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word}
    (valid : WordValid before owner ticket address)
    (world : Ownership.WellFormed before.resources)
    (preserves : Ownership.PreservesAllocation before.resources after.resources ticket.identifier) :
    loadDWord (toMemory after.resources.space) address =
      loadDWord (toMemory before.resources.space) address := by
  obtain ⟨allocation, found, _, _, fits, _⟩ := valid
  obtain ⟨_, cells⟩ := preserves allocation found
  let loan : Borrowing.Loan := ⟨ticket, owner, 0, allocation.region⟩
  have regionValid := (world.1 _ _ found).2.1
  have subregion : Borrowing.Subregion (wordRegion address) loan.region := of_decide_eq_true fits
  apply loadDWord_congr
  intro offset bound
  exact (toMemory_agrees_at _ _ _
    (cells _ (Borrowing.word_inside loan regionValid address subregion offset bound))).1

/-- Retaining current allocation metadata and every cell permission retains
word authority even when another store changes the operand's contents. -/
theorem WordValid.permissions {before after : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word}
    (valid : WordValid before owner ticket address)
    (allocations : after.resources.allocations = before.resources.allocations)
    (permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
      (before.resources.space.cells query).map Cell.permissions) :
    WordValid after owner ticket address := by
  obtain ⟨allocation, found, owns, epoch, fits, writable⟩ := valid
  refine ⟨allocation, by rw [allocations]; exact found, owns, epoch, fits, ?_⟩
  rw [Atomics.canStore_permissions permissions]
  exact writable

/-- Exact effects of one admitted borrowing word store. These statements do
not grant any caller authority to bypass a surrounding protocol's guards. -/
structure StoreEffect (before after : Borrowing.State) (address : Word) (value : BitVec 32) : Prop where
  allocations : after.resources.allocations = before.resources.allocations
  frontier : after.resources.frontier = before.resources.frontier
  loans : after.loans = before.loans
  nextLoan : after.nextLoan = before.nextLoan
  machine : X86.storeDWord (toMemory before.resources.space) address value =
    .ok (toMemory after.resources.space)
  readback : loadDWord (toMemory after.resources.space) address = .ok value
  permissions : ∀ query, (after.resources.space.cells query).map Cell.permissions =
    (before.resources.space.cells query).map Cell.permissions
  outside : ∀ query, ¬(wordRegion address).Contains query →
    after.resources.space.cells query = before.resources.space.cells query

theorem store_shape {before after : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} {value : BitVec 32}
    (success : Borrowing.mutate before (.store owner ticket address value) = .ok (after, none)) :
    ∃ world, Ownership.storeWord before.resources owner ticket address value = .ok world ∧
      after = { before with resources := world } := by
  obtain ⟨_, resources, changed, same⟩ := Borrowing.mutate_ok _ _ _ success
  cases stored : Ownership.storeWord before.resources owner ticket address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at changed
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at changed
    subst resources
    exact ⟨world, rfl, (congrArg Prod.fst same)⟩

theorem store_none {before : Borrowing.State} {owner : Nat} {ticket : Ownership.Ticket}
    {address : Word} {value : BitVec 32} {result : Borrowing.State × Option Ownership.Ticket}
    (success : Borrowing.mutate before (.store owner ticket address value) = .ok result) : result.2 = none := by
  obtain ⟨_, resources, changed, same⟩ := Borrowing.mutate_ok _ _ _ success
  cases stored : Ownership.storeWord before.resources owner ticket address value with
  | error fault => simp [Ownership.Mutation.run, stored, Except.map] at changed
  | ok world =>
    simp [Ownership.Mutation.run, stored, Except.map] at changed
    subst resources
    rw [same]

theorem store_effect {before after : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} {value : BitVec 32}
    (success : Borrowing.mutate before (.store owner ticket address value) = .ok (after, none)) :
    StoreEffect before after address value := by
  obtain ⟨world, stored, same⟩ := store_shape success
  obtain ⟨_, space, _, _, osStore, worldEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
  have sound := AddressSpace.storeWord_sound _ _ _ _ osStore
  rw [same, worldEq]
  exact ⟨rfl, rfl, rfl, rfl, sound.1, sound.2.1, sound.2.2.1, sound.2.2.2⟩

theorem StoreEffect.wordValid {before after : Borrowing.State} {address : Word} {value : BitVec 32}
    (effect : StoreEffect before after address value) {owner : Nat}
    {ticket : Ownership.Ticket} {operand : Word} (valid : WordValid before owner ticket operand) :
    WordValid after owner ticket operand :=
  valid.permissions effect.allocations effect.permissions

/-- All metadata, cells, and permissions of a different live allocation are
framed by an admitted store, using the ownership model's disjointness proof. -/
theorem store_preservesAllocation {before after : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} {value : BitVec 32}
    (valid : Ownership.WellFormed before.resources)
    (success : Borrowing.mutate before (.store owner ticket address value) = .ok (after, none))
    (identifier : Nat) (different : identifier ≠ ticket.identifier) :
    Ownership.PreservesAllocation before.resources after.resources identifier := by
  obtain ⟨_, resources, changed, same⟩ := Borrowing.mutate_ok _ _ _ success
  have framed := Ownership.Mutation.run_preserves (.store owner ticket address value)
    before.resources resources identifier valid changed (by
      simpa [Ownership.Mutation.target, eq_comm] using different)
  rw [congrArg (fun pair : Borrowing.State × Option Ownership.Ticket => pair.1.resources) same]
  exact framed

/-- XCHG has the same OS-cell update and resource effects as its internal
checked store gate; its distinct RMW transition remains supplied by
`AtomicExchange.exchangeWord_sound`. -/
theorem exchange_effect {before : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} {value : BitVec 32}
    {result : Borrowing.State × BitVec 32}
    (success : AtomicExchange.exchangeWord before owner ticket address value = .ok result) :
    StoreEffect before result.1 address value :=
  store_effect (AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ success)

theorem exchange_preservesAllocation {before : Borrowing.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address : Word} {value : BitVec 32}
    {result : Borrowing.State × BitVec 32}
    (valid : Ownership.WellFormed before.resources)
    (success : AtomicExchange.exchangeWord before owner ticket address value = .ok result)
    (identifier : Nat) (different : identifier ≠ ticket.identifier) :
    Ownership.PreservesAllocation before.resources result.1.resources identifier :=
  store_preservesAllocation valid (AtomicExchange.exchangeWord_guarded _ _ _ _ _ _ success)
    identifier different

end EDSL.OS.Mutex
