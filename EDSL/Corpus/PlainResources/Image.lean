/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainResources.Current

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.PlainResources
open X86 OS OS.AddressSpace Grading.ConcurrentTask

/-- A faster index for an already present checked slice. Everything outside
that slice is the supplied COMPLETE space, including all nonexecutable cells. -/
def indexSlice (original : Space) (image : ScalarCall64.Image) : Space where
  cells address := if (⟨image.base, image.bytes.length⟩ : Region).Contains address then
    some ⟨(image.bytes[address.toNat - image.base.toNat]?).getD 0, readExecute⟩
    else original.cells address

theorem indexSlice_eq (original : Space) (image : ScalarCall64.Image)
    (slice : ∀ index (bound : index < image.bytes.length),
      original.cells (image.base + BitVec.ofNat 64 index) = some ⟨image.bytes[index], readExecute⟩) :
    indexSlice original image = original := by
  apply congrArg Space.mk
  funext address
  change (if (⟨image.base, image.bytes.length⟩ : Region).Contains address then
    some (⟨(image.bytes[address.toNat - image.base.toNat]?).getD 0, readExecute⟩ : AddressSpace.Cell)
    else original.cells address) = original.cells address
  split
  next inside =>
    let offset := address.toNat - image.base.toNat
    change image.base.toNat ≤ address.toNat ∧ address.toNat < image.base.toNat + image.bytes.length at inside
    have bound : offset < image.bytes.length := by dsimp [offset]; omega
    have small : offset < 2^64 := by dsimp [offset]; have := address.isLt; omega
    have sum : image.base.toNat + offset = address.toNat := by dsimp [offset]; omega
    have same : image.base + BitVec.ofNat 64 offset = address := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
        sum, Nat.mod_eq_of_lt address.isLt]
    have present := slice offset bound
    rw [same] at present
    rw [present]
    change some (⟨(image.bytes[offset]?).getD 0, readExecute⟩ : AddressSpace.Cell) = _
    rw [List.getElem?_eq_getElem bound, Option.getD_some]
  next => rfl

/-- Whole-space transport, without an ELF name, decoder shape, method or Claim.
In particular this conclusion retains exact bytes AND permissions at EVERY
loaded address, rather than merely the selected executable function interval. -/
theorem Cohort.full_image {original installed : Space} {catalog : Plain64.Catalog}
    {layout : Layout} {old : Word} {first second : Choice}
    (cohort : Cohort original catalog layout old first second) (same : original = installed)
    {address : Word} {cell : AddressSpace.Cell} (live : installed.cells address = some cell) :
    cohort.state.world.legacy.shared.resources.space.cells address = some cell := by
  apply cohort.resources.managed.retained address cell
  simpa only [same] using live

theorem Cohort.fresh_target {original installed : Space} {catalog : Plain64.Catalog}
    {layout : Layout} {old : Word} {first second : Choice}
    (cohort : Cohort original catalog layout old first second) (same : original = installed) :
    allUnmapped installed ⟨layout.target, 8⟩ = true := by
  simpa only [same] using cohort.resources.freshTarget

/-- A reusable checked-result eliminator. Totality must be proved for the
ACTUAL operation, not supplied as validity/retained-image/Pre premises. -/
theorem checked_get {Error Value : Type} (operation : Except Error Value)
    (total : operation.toOption.isSome = true) :
    operation = .ok (operation.toOption.get total) := by
  cases operation with
  | error fault => cases total
  | ok value => rfl

end EDSL.Corpus.PlainResources

#audit_edsl
