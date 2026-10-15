/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordStore

namespace EDSL.OS.Ownership
open X86 AddressSpace

/-- Proof-level identity and transfer epoch. Raw machine pointers contain
neither field; these values do not implement hardware temporal protection. -/
structure Ticket where
  identifier : Nat
  epoch : Nat
  deriving DecidableEq, Repr

structure Allocation where
  owner : Nat
  epoch : Nat
  region : Region
  deriving DecidableEq, Repr

/-- Bytes/permissions project through the existing OS model. Identities and
epochs are unbounded natural numbers, so successful reuse never wraps them. -/
structure World where
  space : Space
  frontier : Nat
  allocations : Nat → Option Allocation

def empty (space : Space := AddressSpace.empty) : World := ⟨space, 0, fun _ => none⟩

def Current (world : World) (owner : Nat) (ticket : Ticket) : Prop :=
  ∃ allocation, world.allocations ticket.identifier = some allocation ∧
    allocation.owner = owner ∧ allocation.epoch = ticket.epoch

def Disjoint (left right : Region) : Prop :=
  left.base.toNat + left.length ≤ right.base.toNat ∨
    right.base.toNat + right.length ≤ left.base.toNat

instance (left right : Region) : Decidable (Disjoint left right) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- All live resources have valid fully mapped intervals (including hidden
cells), distinct identities below the monotone frontier, and disjoint regions.
Unregistered cells may hold code, a caller stack or loader-installed data. -/
def WellFormed (world : World) : Prop :=
  (∀ identifier allocation, world.allocations identifier = some allocation →
    identifier < world.frontier ∧ allocation.region.valid = true ∧
    ∀ address, allocation.region.Contains address → ∃ cell, world.space.cells address = some cell) ∧
  (∀ left a right b, world.allocations left = some a → world.allocations right = some b →
    left ≠ right → Disjoint a.region b.region)

inductive Fault where
  | missingAllocation
  | staleEpoch
  | wrongOwner
  | outsideAllocation
  | identityCollision
  | claimedRegion
  | addressSpace (fault : AddressSpace.Fault)
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def authorize (world : World) (owner : Nat) (ticket : Ticket) : Except Fault Allocation :=
  match world.allocations ticket.identifier with
  | none => .error .missingAllocation
  | some allocation =>
    if allocation.epoch ≠ ticket.epoch then .error .staleEpoch
    else if allocation.owner ≠ owner then .error .wrongOwner
    else .ok allocation

def replace (world : World) (identifier : Nat) (allocation : Option Allocation) : World :=
  { world with allocations := fun query => if query = identifier then allocation else world.allocations query }

def install (world : World) (space : Space) (owner : Nat) (region : Region) : World :=
  { space := space, frontier := world.frontier + 1
    allocations := fun query => if query = world.frontier then some ⟨owner, 0, region⟩
      else world.allocations query }

/-- Fresh abstract mapping at a caller-selected address; this is not an
allocator search algorithm or a claim that Linux mmap always succeeds. -/
def allocate (world : World) (owner : Nat) (region : Region) (permissions : Permissions) :
    Except Fault (World × Ticket) := do
  if (world.allocations world.frontier).isSome then throw .identityCollision
  let space ← (AddressSpace.map world.space region permissions).mapError Fault.addressSpace
  return (install world space owner region, ⟨world.frontier, 0⟩)

def unclaimed (world : World) (region : Region) : Bool :=
  (List.range world.frontier).all fun identifier =>
    match world.allocations identifier with
    | none => true
    | some allocation => decide (Disjoint region allocation.region)

/-- Register existing loader/caller mappings without replacing bytes or
permissions. The finite scan is complete under the explicit WellFormed premise
of the soundness theorem. Exact segment ranges may be adopted; holes may not. -/
def adopt (world : World) (owner : Nat) (region : Region) : Except Fault (World × Ticket) := do
  if (world.allocations world.frontier).isSome then throw .identityCollision
  if !region.valid then throw (.addressSpace .invalidRegion)
  if !allMapped world.space region then throw (.addressSpace .notMapped)
  if !unclaimed world region then throw .claimedRegion
  return (install world world.space owner region, ⟨world.frontier, 0⟩)

/-- Transfer always revokes the old epoch, including transfer to the same owner.
It preserves all bytes/permissions. Tickets are copyable proof values, so this
registry is unique current authority, not a linear-token separation logic. -/
def transfer (world : World) (owner : Nat) (ticket : Ticket) (newOwner : Nat) :
    Except Fault (World × Ticket) := do
  let allocation ← authorize world owner ticket
  let next := { allocation with owner := newOwner, epoch := allocation.epoch + 1 }
  return (replace world ticket.identifier (some next), ⟨ticket.identifier, next.epoch⟩)

def release (world : World) (owner : Nat) (ticket : Ticket) : Except Fault World := do
  let allocation ← authorize world owner ticket
  let space ← (AddressSpace.unmap world.space allocation.region).mapError Fault.addressSpace
  return { replace world ticket.identifier none with space := space }

def protect (world : World) (owner : Nat) (ticket : Ticket) (permissions : Permissions) :
    Except Fault World := do
  let allocation ← authorize world owner ticket
  let space ← (AddressSpace.protect world.space allocation.region permissions).mapError Fault.addressSpace
  return { world with space := space }

/-- The entire operand lies within one allocation in natural-address arithmetic.
The machine store separately validates canonicality and every mapped permission. -/
def containsWord (allocation : Allocation) (address : Word) : Bool :=
  decide (allocation.region.base.toNat ≤ address.toNat ∧
    address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length)

def storeWord (world : World) (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32) :
    Except Fault World := do
  let allocation ← authorize world owner ticket
  if !containsWord allocation address then throw .outsideAllocation
  let space ← (AddressSpace.storeWord world.space address value).mapError Fault.addressSpace
  return { world with space := space }

theorem empty_wellFormed (space : Space) : WellFormed (empty space) := by
  simp [WellFormed, empty]

theorem authorize_ok (world : World) (owner : Nat) (ticket : Ticket) (allocation : Allocation)
    (success : authorize world owner ticket = .ok allocation) :
    world.allocations ticket.identifier = some allocation ∧
    allocation.owner = owner ∧ allocation.epoch = ticket.epoch := by
  cases found : world.allocations ticket.identifier with
  | none => simp [authorize, found] at success
  | some current =>
    by_cases epoch : current.epoch = ticket.epoch
    · by_cases owns : current.owner = owner
      · simp [authorize, found, epoch, owns] at success
        cases success
        exact ⟨rfl, owns, epoch⟩
      · simp [authorize, found, epoch, owns] at success
    · simp [authorize, found, epoch] at success

theorem authorize_current (world : World) (owner : Nat) (ticket : Ticket) (allocation : Allocation)
    (success : authorize world owner ticket = .ok allocation) : Current world owner ticket :=
  ⟨allocation, authorize_ok world owner ticket allocation success⟩

theorem disjoint_outside {left right : Region} (separate : Disjoint left right)
    {address : Word} (inside : right.Contains address) : ¬left.Contains address := by
  intro overlap
  rcases separate with before | after
  all_goals
    have := inside.1
    have := inside.2
    have := overlap.1
    have := overlap.2
    omega

theorem disjoint_symm {left right : Region} (separate : Disjoint left right) : Disjoint right left :=
  separate.symm

theorem issued_below {world : World} (valid : WellFormed world) {owner : Nat} {ticket : Ticket}
    (current : Current world owner ticket) : ticket.identifier < world.frontier := by
  obtain ⟨allocation, found, _, _⟩ := current
  exact (valid.1 _ _ found).1

end EDSL.OS.Ownership
