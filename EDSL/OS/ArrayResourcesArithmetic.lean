/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResourcesModel

namespace EDSL.OS.ArrayResources
open X86 AddressSpace

/-- Exact full-width address arithmetic for every actual element. The bound
permits an endpoint at 2^64, but every accessed element starts below it. -/
theorem element_address {base : Word} {values : List (BitVec 32)}
    (bound : ArrayBound base values) {index : Nat} (inside : index < values.length) :
    (base + BitVec.ofNat 64 (4 * index)).toNat = base.toNat + 4 * index := by
  have baseBound := base.isLt
  have limit : base.toNat + 4 * values.length ≤ 2^64 := bound
  have offset : 4 * index < 2^64 := by omega
  have sum : base.toNat + 4 * index < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt offset, Nat.mod_eq_of_lt sum]

theorem element_fits {base : Word} {values : List (BitVec 32)}
    (bound : ArrayBound base values) {index : Nat} (inside : index < values.length) :
    Borrowing.Subregion (wordRegion (base + BitVec.ofNat 64 (4 * index)))
      (arrayRegion base values) := by
  have address := element_address bound inside
  simp only [Borrowing.Subregion, wordRegion, arrayRegion, address]
  omega

/-- The current input loan admits the actual four-byte element read. Initial
values are bound independently by currentArrayAt, not by authority alone. -/
theorem element_loadWord {shared : Borrowing.State} {call : Call}
    (contract : Contract shared call) {index : Nat} {value : BitVec 32}
    (present : call.values[index]? = some value) :
    Borrowing.loadWord shared (Threads.principal call.worker) call.loans.input
      (call.base + BitVec.ofNat 64 (4 * index)) = .ok value := by
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  have nonempty : call.values ≠ [] := by intro empty; simp [empty] at inside
  obtain ⟨loan, live, borrower, region⟩ := contract.held.input nonempty
  have authorized : Borrowing.authorize shared (Threads.principal call.worker)
      call.loans.input = .ok loan := by simp [Borrowing.authorize, live, borrower]
  apply Borrowing.loadWord_success _ _ _ _ _ loan authorized
  · rw [region]
    exact element_fits contract.bound inside
  · exact contract.array index value present

/-- All four actual operand bytes, including the last word's last byte, are
in the input span. Canonicality is supplied by the live current loan. -/
theorem element_bytes {shared : Borrowing.State} {call : Call}
    (contract : Contract shared call) {index offset : Nat}
    (inside : index < call.values.length) (byte : offset < 4) :
    call.inputRegion.Contains
      ((call.base + BitVec.ofNat 64 (4 * index)) + BitVec.ofNat 64 offset) ∧
    canonical ((call.base + BitVec.ofNat 64 (4 * index)) + BitVec.ofNat 64 offset) = true := by
  have nonempty : call.values ≠ [] := by intro empty; simp [empty] at inside
  obtain ⟨loan, live, _, region⟩ := contract.held.input nonempty
  obtain ⟨_, _, _, _, _, _, valid, _⟩ := contract.wellFormed.2 _ _ live
  have fits : Borrowing.Subregion
      (wordRegion (call.base + BitVec.ofNat 64 (4 * index))) loan.region := by
    rw [region]
    exact element_fits contract.bound inside
  have contained := Borrowing.word_inside loan valid _ fits offset byte
  exact ⟨region ▸ contained, valid_contains_canonical loan.region valid _ contained⟩

theorem arrayRead_permission {shared : Borrowing.State} {call : Call}
    (contract : Contract shared call) {read : Sequential.Read} (footprint : ArrayRead call read) :
    ReadPermission shared call.worker read := by
  obtain ⟨_, width, index, inside, address⟩ := footprint
  have nonempty : call.values ≠ [] := by intro empty; simp [empty] at inside
  obtain ⟨loan, live, borrower, region⟩ := contract.held.input nonempty
  refine ⟨call.loans.input, loan, by simp [Borrowing.authorize, live, borrower], ?_⟩
  rw [width, address, region]
  exact element_fits contract.bound inside

theorem stackRead_permission {shared : Borrowing.State} {call : Call}
    (contract : Contract shared call) :
    ReadPermission shared call.worker ⟨.stack, call.stack, 8⟩ := by
  obtain ⟨loan, live, borrower, region⟩ := contract.held.stack
  refine ⟨call.loans.stack, loan, by simp [Borrowing.authorize, live, borrower], ?_⟩
  rw [region]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem no_empty_arrayRead {call : Call} (empty : call.values = []) (read : Sequential.Read) :
    ¬ArrayRead call read := by
  rintro ⟨_, _, index, inside, _⟩
  simp [empty] at inside

end EDSL.OS.ArrayResources
