/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.History

namespace EDSL.OS.Ownership
open X86 AddressSpace

/-- An executable managed operation. A target identifies the existing allocation
whose authority or cells may change; fresh allocation/adoption have no target. -/
inductive Mutation where
  | allocate (owner : Nat) (region : Region) (permissions : Permissions)
  | adopt (owner : Nat) (region : Region)
  | transfer (owner : Nat) (ticket : Ticket) (newOwner : Nat)
  | release (owner : Nat) (ticket : Ticket)
  | protect (owner : Nat) (ticket : Ticket) (permissions : Permissions)
  | store (owner : Nat) (ticket : Ticket) (address : Word) (value : BitVec 32)
  | store64 (owner : Nat) (ticket : Ticket) (address : Word) (value : Word)
  deriving DecidableEq, Repr

def Mutation.target : Mutation → Option Nat
  | .allocate .. | .adopt .. => none
  | .transfer _ ticket _ | .release _ ticket | .protect _ ticket _ | .store _ ticket _ _ |
      .store64 _ ticket _ _ =>
      some ticket.identifier

def Mutation.run (operation : Mutation) (world : World) : Except Fault (World × Option Ticket) :=
  match operation with
  | .allocate owner region permissions =>
      (Ownership.allocate world owner region permissions).map fun result => (result.1, some result.2)
  | .adopt owner region =>
      (Ownership.adopt world owner region).map fun result => (result.1, some result.2)
  | .transfer owner ticket newOwner =>
      (Ownership.transfer world owner ticket newOwner).map fun result => (result.1, some result.2)
  | .release owner ticket => (Ownership.release world owner ticket).map fun after => (after, none)
  | .protect owner ticket permissions =>
      (Ownership.protect world owner ticket permissions).map fun after => (after, none)
  | .store owner ticket address value =>
      (Ownership.storeWord world owner ticket address value).map fun after => (after, none)
  | .store64 owner ticket address value =>
      (Ownership.storeWord64 world owner ticket address value).map fun after => (after, none)

/-- Exact allocation metadata, bytes and permissions are framed together. This
property concerns a registered live allocation, rather than arbitrary raw cells. -/
def PreservesAllocation (before after : World) (identifier : Nat) : Prop :=
  ∀ allocation, before.allocations identifier = some allocation →
    after.allocations identifier = some allocation ∧
    ∀ address, allocation.region.Contains address → after.space.cells address = before.space.cells address

theorem PreservesAllocation.refl (world : World) (identifier : Nat) :
    PreservesAllocation world world identifier :=
  fun _ found => ⟨found, fun _ _ => rfl⟩

theorem PreservesAllocation.trans {before middle after : World} {identifier : Nat}
    (first : PreservesAllocation before middle identifier)
    (last : PreservesAllocation middle after identifier) : PreservesAllocation before after identifier := by
  intro allocation found
  obtain ⟨middleAt, firstCells⟩ := first allocation found
  obtain ⟨afterAt, lastCells⟩ := last allocation middleAt
  exact ⟨afterAt, fun address inside => (lastCells address inside).trans (firstCells address inside)⟩

theorem Mutation.run_step (operation : Mutation) (world : World) (result : World × Option Ticket)
    (success : operation.run world = .ok result) : Step world result.1 := by
  cases operation with
  | allocate owner region permissions =>
    cases completed : Ownership.allocate world owner region permissions with
    | error fault => simp [run, completed, Except.map] at success
    | ok output =>
      simp [run, completed, Except.map] at success
      subst result
      exact .allocate completed
  | adopt owner region =>
    cases completed : Ownership.adopt world owner region with
    | error fault => simp [run, completed, Except.map] at success
    | ok output =>
      simp [run, completed, Except.map] at success
      subst result
      exact .adopt completed
  | transfer owner ticket newOwner =>
    cases completed : Ownership.transfer world owner ticket newOwner with
    | error fault => simp [run, completed, Except.map] at success
    | ok output =>
      simp [run, completed, Except.map] at success
      subst result
      exact .transfer completed
  | release owner ticket =>
    cases completed : Ownership.release world owner ticket with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      exact .release completed
  | protect owner ticket permissions =>
    cases completed : Ownership.protect world owner ticket permissions with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      exact .protect completed
  | store owner ticket address value =>
    cases completed : Ownership.storeWord world owner ticket address value with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      exact .store completed
  | store64 owner ticket address value =>
    cases completed : Ownership.storeWord64 world owner ticket address value with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      exact .store64 completed

theorem Mutation.run_wellFormed (operation : Mutation) (world : World) (result : World × Option Ticket)
    (valid : WellFormed world) (success : operation.run world = .ok result) : WellFormed result.1 :=
  (operation.run_step world result success).wellFormed valid

/-- Under the ownership invariant, every successful operation preserves every
existing allocation except its named target. The claim includes hidden cells
and permissions, so protecting or unmapping cannot masquerade as preservation. -/
theorem Mutation.run_preserves (operation : Mutation) (world : World) (result : World × Option Ticket)
    (identifier : Nat) (valid : WellFormed world) (success : operation.run world = .ok result)
    (different : operation.target ≠ some identifier) : PreservesAllocation world result.1 identifier := by
  cases operation with
  | allocate owner region permissions =>
    cases completed : Ownership.allocate world owner region permissions with
    | error fault => simp [run, completed, Except.map] at success
    | ok output =>
      simp [run, completed, Except.map] at success
      subst result
      intro allocation found
      have below := (valid.1 _ _ found).1
      have fresh : identifier ≠ world.frontier := by omega
      obtain ⟨space, _, same⟩ := allocate_ok _ _ _ _ _ completed
      refine ⟨?_, ?_⟩
      · rw [same]
        simpa [install, fresh] using found
      · intro address inside
        obtain ⟨cell, mapped⟩ := (valid.1 _ _ found).2.2 address inside
        exact ((allocate_initialized _ _ _ _ _ completed).2 address cell mapped).trans mapped.symm
  | adopt owner region =>
    cases completed : Ownership.adopt world owner region with
    | error fault => simp [run, completed, Except.map] at success
    | ok output =>
      simp [run, completed, Except.map] at success
      subst result
      intro allocation found
      have below := (valid.1 _ _ found).1
      have fresh : identifier ≠ world.frontier := by omega
      obtain ⟨same, _, _, _⟩ := adopt_ok _ _ _ _ completed
      rw [same]
      exact ⟨by simpa [install, fresh] using found, fun _ _ => rfl⟩
  | transfer owner ticket newOwner =>
    cases completed : Ownership.transfer world owner ticket newOwner with
    | error fault => simp [run, completed, Except.map] at success
    | ok output =>
      simp [run, completed, Except.map] at success
      subst result
      have other : identifier ≠ ticket.identifier := by simpa [target, eq_comm] using different
      obtain ⟨_, _, same⟩ := transfer_ok _ _ _ _ _ completed
      rw [same]
      intro allocation found
      exact ⟨by simpa [replace, other] using found, fun _ _ => rfl⟩
  | release owner ticket =>
    cases completed : Ownership.release world owner ticket with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      have other : identifier ≠ ticket.identifier := by simpa [target, eq_comm] using different
      obtain ⟨changed, _, authorized, _, same⟩ := release_ok _ _ _ _ completed
      intro allocation found
      refine ⟨?_, ?_⟩
      · rw [same]
        simpa [replace, other] using found
      · intro address inside
        apply release_frame _ _ _ _ completed address
        intro affected authorizedAffected
        have affectedAt := (authorize_ok _ _ _ _ authorizedAffected).1
        exact disjoint_outside (valid.2 _ _ _ _ affectedAt found (Ne.symm other)) inside
  | protect owner ticket permissions =>
    cases completed : Ownership.protect world owner ticket permissions with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      have other : identifier ≠ ticket.identifier := by simpa [target, eq_comm] using different
      have facts := protect_wellFormed _ _ _ _ _ valid completed
      intro allocation found
      refine ⟨by rw [facts.2.1]; exact found, ?_⟩
      intro address inside
      apply protect_frame _ _ _ _ _ completed address
      intro affected authorized
      have affectedAt := (authorize_ok _ _ _ _ authorized).1
      exact disjoint_outside (valid.2 _ _ _ _ affectedAt found (Ne.symm other)) inside
  | store owner ticket address value =>
    cases completed : Ownership.storeWord world owner ticket address value with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      have other : identifier ≠ ticket.identifier := by simpa [target, eq_comm] using different
      have facts := storeWord_wellFormed _ _ _ _ _ _ valid completed
      intro allocation found
      refine ⟨by rw [facts.2.2.1]; exact found, ?_⟩
      intro query inside
      obtain ⟨affected, _, authorized, _, _, _⟩ := storeWord_ok _ _ _ _ _ _ completed
      have affectedAt := (authorize_ok _ _ _ _ authorized).1
      exact facts.2.2.2.2.2.2.2 query affected authorized
        (disjoint_outside (valid.2 _ _ _ _ affectedAt found (Ne.symm other)) inside)
  | store64 owner ticket address value =>
    cases completed : Ownership.storeWord64 world owner ticket address value with
    | error fault => simp [run, completed, Except.map] at success
    | ok after =>
      simp [run, completed, Except.map] at success
      subst result
      have other : identifier ≠ ticket.identifier := by simpa [target, eq_comm] using different
      have facts := storeWord64_wellFormed _ _ _ _ _ _ valid completed
      intro allocation found
      refine ⟨by rw [facts.2.2.1]; exact found, ?_⟩
      intro query inside
      obtain ⟨affected, _, authorized, _, _, _⟩ := storeWord64_ok _ _ _ _ _ _ completed
      have affectedAt := (authorize_ok _ _ _ _ authorized).1
      exact facts.2.2.2.2.2.2.2 query affected authorized
        (disjoint_outside (valid.2 _ _ _ _ affectedAt found (Ne.symm other)) inside)

end EDSL.OS.Ownership
