/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.Read
import EDSL.OS.Borrowing.Store64

namespace EDSL.OS.Borrowing
open X86 AddressSpace

/-- A live read-only loan authorizes a complete eight-byte DATA read, without
requiring write permission or extending its region through readable neighbors. -/
def loadWord64 (state : State) (borrower identifier : Nat) (address : Word) :
    Except ReadFault Word := do
  let loan ← (authorize state borrower identifier).mapError ReadFault.authority
  if !decide (Subregion (qwordRegion address) loan.region) then throw .outsideLoan
  (loadQWord (toMemory state.resources.space) address).mapError ReadFault.machine

theorem loadWord64_ok (state : State) (borrower identifier : Nat) (address value : Word)
    (success : loadWord64 state borrower identifier address = .ok value) :
    ∃ loan, authorize state borrower identifier = .ok loan ∧
      Subregion (qwordRegion address) loan.region ∧
      loadQWord (toMemory state.resources.space) address = .ok value := by
  cases authorized : authorize state borrower identifier with
  | error fault => simp [loadWord64, authorized, Except.mapError] at success
  | ok loan =>
    by_cases fits : Subregion (qwordRegion address) loan.region
    · cases observed : loadQWord (toMemory state.resources.space) address with
      | error fault => simp [loadWord64, authorized, Except.mapError, fits, observed] at success
      | ok word =>
        simp [loadWord64, authorized, Except.mapError, fits, observed] at success
        cases success
        exact ⟨loan, rfl, fits, rfl⟩
    · simp [loadWord64, authorized, Except.mapError, fits] at success

theorem loadWord64_success (state : State) (borrower identifier : Nat) (address value : Word)
    (loan : Loan) (authorized : authorize state borrower identifier = .ok loan)
    (fits : Subregion (qwordRegion address) loan.region)
    (observed : loadQWord (toMemory state.resources.space) address = .ok value) :
    loadWord64 state borrower identifier address = .ok value := by
  simp [loadWord64, authorized, fits, observed, Except.mapError]

/-- Natural-address containment supplies every modular machine operand byte. -/
theorem qword_inside (loan : Loan) (regionValid : loan.region.valid = true) (address : Word)
    (fits : Subregion (qwordRegion address) loan.region) (offset : Nat) (bound : offset < 8) :
    loan.region.Contains (address + BitVec.ofNat 64 offset) := by
  have valid : 0 < loan.region.length ∧ loan.region.base.toNat + loan.region.length ≤ 2^64 ∧
      (loan.region.base.toNat + loan.region.length ≤ 2^47 ∨ 2^64 - 2^47 ≤ loan.region.base.toNat) :=
    of_decide_eq_true regionValid
  have lower := fits.1
  have upper := fits.2
  change loan.region.base.toNat ≤ address.toNat at lower
  change address.toNat + 8 ≤ loan.region.base.toNat + loan.region.length at upper
  have small : offset < 2^64 := by omega
  have sum : address.toNat + offset < 2^64 := by omega
  change loan.region.base.toNat ≤ (address + BitVec.ofNat 64 offset).toNat ∧
    (address + BitVec.ofNat 64 offset).toNat < loan.region.base.toNat + loan.region.length
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]
  omega

/-- Well-formed loans supply readable cells and canonicality for all eight
bytes. Write permission is deliberately absent from this contract. -/
theorem loadWord64_exists (state : State) (borrower identifier : Nat) (address : Word)
    (loan : Loan) (valid : WellFormed state)
    (authorized : authorize state borrower identifier = .ok loan)
    (fits : Subregion (qwordRegion address) loan.region) :
    ∃ value, loadWord64 state borrower identifier address = .ok value := by
  have live := (authorize_ok _ _ _ _ authorized).1
  obtain ⟨_, _, _, _, _, regionValid, readable⟩ := (valid.2 _ _ live).2
  have byteAt : ∀ offset, offset < 8 → ∃ byte,
      readDataByte (toMemory state.resources.space) (address + BitVec.ofNat 64 offset) = .ok byte := by
    intro offset bound
    have inside := qword_inside loan regionValid address fits offset bound
    obtain ⟨cell, stored, canRead⟩ := readable _ inside
    have canonical := valid_contains_canonical loan.region regionValid _ inside
    exact ⟨cell.byte, by simp [readDataByte, canonical, toMemory, stored, canRead]⟩
  obtain ⟨b0, at0⟩ := byteAt 0 (by decide)
  obtain ⟨b1, at1⟩ := byteAt 1 (by decide)
  obtain ⟨b2, at2⟩ := byteAt 2 (by decide)
  obtain ⟨b3, at3⟩ := byteAt 3 (by decide)
  obtain ⟨b4, at4⟩ := byteAt 4 (by decide)
  obtain ⟨b5, at5⟩ := byteAt 5 (by decide)
  obtain ⟨b6, at6⟩ := byteAt 6 (by decide)
  obtain ⟨b7, at7⟩ := byteAt 7 (by decide)
  have noWrap : ¬ address.toNat + 7 ≥ 2^64 := by
    have regionBound := (of_decide_eq_true regionValid).2.1
    have upper := fits.2
    change address.toNat + 8 ≤ loan.region.base.toNat + loan.region.length at upper
    omega
  simp only [BitVec.add_zero] at at0 at1 at2 at3 at4 at5 at6 at7
  refine ⟨joinQWord b0 b1 b2 b3 b4 b5 b6 b7, loadWord64_success _ _ _ _ _ loan authorized fits ?_⟩
  simp [loadQWord, noWrap, at0, at1, at2, at3, at4, at5, at6, at7]

/-- This uses the same loan-ID frontier and exact-cell history as loadWord;
including store64 in that history also protects surviving four-byte reads. -/
theorem History.loadWord64_stable {before after : State} (history : History before after)
    (valid : WellFormed before) (borrower identifier : Nat) (address value : Word)
    (success : loadWord64 before borrower identifier address = .ok value)
    (survives : (after.loans identifier).isSome = true) :
    loadWord64 after borrower identifier address = .ok value := by
  obtain ⟨loan, authorized, fits, observed⟩ := loadWord64_ok _ _ _ _ _ success
  obtain ⟨live, owns⟩ := authorize_ok _ _ _ _ authorized
  obtain ⟨below, _, _, _, _, _, regionValid, _⟩ := valid.2 identifier loan live
  cases endpoint : after.loans identifier with
  | none => simp [endpoint] at survives
  | some finalLoan =>
    obtain ⟨original, cells⟩ := history.loan_stable valid identifier below finalLoan endpoint
    have same := Option.some.inj (original.symm.trans live)
    cases same
    have finalAuthority : authorize after borrower identifier = .ok loan := by
      simp [authorize, endpoint, owns]
    apply loadWord64_success _ _ _ _ _ loan finalAuthority fits
    apply (loadQWord_congr _ _ _ ?_).trans observed
    intro offset bound
    exact (toMemory_agrees_at _ _ _ (cells _ (qword_inside loan regionValid address fits offset bound))).1

theorem Revoked.loadWord64_denied {state : State} {identifier : Nat}
    (revoked : Revoked state identifier) (borrower : Nat) (address : Word) :
    loadWord64 state borrower identifier address = .error (.authority .missingLoan) := by
  simp [loadWord64, revoked.unauthorized borrower, Except.mapError]

end EDSL.OS.Borrowing
