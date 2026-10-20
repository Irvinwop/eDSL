/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AddressSpace

namespace EDSL.OS.AddressSpace
open X86

/-- Cell identity carries contents and all permissions across an interface. -/
def AgreesOn (left right : Space) (base : Word) (length : Nat) : Prop :=
  ∀ offset, offset < length →
    left.cells (base + BitVec.ofNat 64 offset) =
      right.cells (base + BitVec.ofNat 64 offset)

/-- Abstract operations use natural half-open regions; machine operands use
modular word addresses. Disjointness states their relation explicitly. -/
def Region.Avoids (region : Region) (base : Word) (length : Nat) : Prop :=
  ∀ offset, offset < length → ¬region.Contains (base + BitVec.ofNat 64 offset)

theorem agrees_read (left right : Space) (base : Word) (length : Nat)
    (same : AgreesOn left right base length) :
    MemoryAgreesOn (toMemory left) (toMemory right) base length := by
  intro offset bound
  exact (toMemory_agrees_at left right _ (same offset bound)).1

theorem agrees_code (left right : Space) (base : Word) (bytes : List Byte)
    (same : AgreesOn left right base bytes.length)
    (code : CodeAt (toMemory right) base bytes) :
    CodeAt (toMemory left) base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have observed := toMemory_agrees_at left right _ (same offset bound)
  unfold fetchByte
  rw [observed.1, observed.2.2]
  exact code.2 offset byte atOffset

theorem map_agrees (space : Space) (region : Region) (permissions : Permissions)
    (base : Word) (length : Nat) (outside : region.Avoids base length) :
    AgreesOn (mapUnchecked space region permissions) space base length := by
  intro offset bound
  exact map_frame space region permissions _ (outside offset bound)

theorem protect_agrees (space : Space) (region : Region) (permissions : Permissions)
    (base : Word) (length : Nat) (outside : region.Avoids base length) :
    AgreesOn (protectUnchecked space region permissions) space base length := by
  intro offset bound
  exact protect_frame space region permissions _ (outside offset bound)

theorem unmap_agrees (space : Space) (region : Region)
    (base : Word) (length : Nat) (outside : region.Avoids base length) :
    AgreesOn (unmapUnchecked space region) space base length := by
  intro offset bound
  exact unmap_frame space region _ (outside offset bound)


end EDSL.OS.AddressSpace
