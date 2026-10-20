/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Model

namespace EDSL.OS.TSO64.Queue
open X86

/-- Plain-memory authority policy. This staged queue API does not change the
current scheduler or enable managed MOV instructions in that scheduler. -/
inductive Profile where
  | ownedOnly
  | sharedCell
  deriving DecidableEq, Repr

/-- Capture the complete authority descriptor at issue. An address alone cannot
identify the original handle or the persistent cell it authorized. -/
structure ManagedRef where
  identifier : Atomics64.HandleId64
  handle : Atomics64.Handle
  cell : Atomics64.Cell
  deriving DecidableEq, Repr

/-- One oldest-first FIFO can retain both ordinary authority and a managed
whole-qword occurrence. Occurrence allocation is a separate caller obligation. -/
inductive Entry where
  | ordinary (ticket : Ownership.Ticket) (store : Store)
  | managed (reference : ManagedRef) (value : Word) (occurrence : Nat)
  deriving DecidableEq, Repr

def Entry.store : Entry → Store
  | .ordinary _ store => store
  | .managed reference value _ => ⟨reference.cell.address, .qword value⟩

/-- The byte semantics remain the existing Mixed FIFO, with no second memory. -/
def payload (entries : List Entry) : Buffer := entries.map Entry.store

/-- Current grant membership and exact reauthorization of the original complete
descriptor. This predicate grants no authority through a buffered overlay. -/
def Current (world : World) (resources : Resources) (reference : ManagedRef) : Prop :=
  reference.identifier ∈ resources.atomics ∧
    Atomics64.authorize world resources.actor reference.identifier =
      .ok (reference.handle, reference.cell)

/-- Decide constructor equality directly, so checked admission/publication can
reduce in the kernel without transporting a decision across a proposition
equivalence. No global equality instance for Except is introduced. -/
private def authorizeMatches
    (actual : Except Atomics64.Fault (Atomics64.Handle × Atomics64.Cell))
    (expected : Atomics64.Handle × Atomics64.Cell) : Decidable (actual = .ok expected) :=
  match actual with
  | .error _ => isFalse (fun same => by cases same)
  | .ok descriptor =>
      match decEq descriptor expected with
      | .isTrue same => isTrue (congrArg Except.ok same)
      | .isFalse different => isFalse (fun same => different (Except.ok.inj same))

instance (world : World) (resources : Resources) (reference : ManagedRef) :
    Decidable (Current world resources reference) :=
  match (inferInstance : Decidable (reference.identifier ∈ resources.atomics)) with
  | .isFalse absent => isFalse (fun current => absent current.1)
  | .isTrue member =>
      match authorizeMatches (Atomics64.authorize world resources.actor reference.identifier)
          (reference.handle, reference.cell) with
      | .isFalse different => isFalse (fun current => different current.2)
      | .isTrue authorized => isTrue ⟨member, authorized⟩

/-- Ordinary entries retain the exact existing StoreGate and original grant
membership. Managed entries require the explicit shared-cell profile. -/
def Valid (world : World) (resources : Resources) (entry : Entry)
    (profile : Profile := .ownedOnly) : Prop :=
  match entry with
  | .ordinary ticket store =>
      ticket ∈ resources.grants ∧ StoreGate world resources.actor ticket store
  | .managed reference _ _ => profile = .sharedCell ∧ Current world resources reference

instance (world : World) (resources : Resources) (entry : Entry) (profile : Profile) :
    Decidable (Valid world resources entry profile) := by
  cases entry <;> unfold Valid <;> infer_instance

/-- Admit the original store without publishing it. Prefer the existing ordinary
grant; only an exact-address qword may fall back to current managed authority.
The supplied occurrence is retained, not allocated from queue length or value. -/
def admit (world : World) (resources : Resources) (store : Store) (occurrence : Nat)
    (profile : Profile := .ownedOnly) : Except Fault Entry :=
  match grantFor world resources store with
  | some ticket => .ok (.ordinary ticket store)
  | none =>
      match profile, store.value with
      | .sharedCell, .qword value =>
          match atomicFor world resources store.address with
          | none => .error .noAtomicGrant
          | some (identifier, handle, cell) =>
              .ok (.managed ⟨identifier, handle, cell⟩ value occurrence)
      | _, _ => .error .noGrant

@[simp] theorem payload_nil : payload [] = [] := rfl

@[simp] theorem payload_cons (entry : Entry) (entries : List Entry) :
    payload (entry :: entries) = entry.store :: payload entries := rfl

theorem payload_append (first second : List Entry) :
    payload (first ++ second) = payload first ++ payload second := List.map_append

theorem payload_enqueue (entries : List Entry) (entry : Entry) :
    payload (entries ++ [entry]) = payload entries ++ [entry.store] := by
  simp only [payload_append, payload_cons, payload_nil]

@[simp] theorem valid_ordinary (world : World) (resources : Resources)
    (ticket : Ownership.Ticket) (store : Store) (profile : Profile) :
    Valid world resources (.ordinary ticket store) profile ↔
      ticket ∈ resources.grants ∧ StoreGate world resources.actor ticket store := Iff.rfl

@[simp] theorem valid_managed (world : World) (resources : Resources)
    (reference : ManagedRef) (value : Word) (occurrence : Nat) (profile : Profile) :
    Valid world resources (.managed reference value occurrence) profile ↔
      profile = .sharedCell ∧ Current world resources reference := Iff.rfl

@[simp] theorem not_valid_managed_ownedOnly (world : World) (resources : Resources)
    (reference : ManagedRef) (value : Word) (occurrence : Nat) :
    ¬Valid world resources (.managed reference value occurrence) .ownedOnly := by
  intro valid
  cases valid.1

end EDSL.OS.TSO64.Queue
