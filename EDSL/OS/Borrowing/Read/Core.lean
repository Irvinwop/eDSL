/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing.History

namespace EDSL.OS.Borrowing
open X86 AddressSpace

inductive ReadFault where
  | authority (fault : Fault)
  | outsideLoan
  | machine (fault : X86.Error)
  deriving DecidableEq, Repr

@[simp] theorem readThrow_error (fault : ReadFault) : (throw fault : Except ReadFault α) = .error fault := rfl

/-- All four bytes must fit in the stored loan; merely owning another readable
allocation or having a readable neighbor does not extend this authority. -/
def loadWord (state : State) (borrower identifier : Nat) (address : Word) :
    Except ReadFault (BitVec 32) := do
  let loan ← (authorize state borrower identifier).mapError ReadFault.authority
  if !decide (Subregion (wordRegion address) loan.region) then throw .outsideLoan
  (loadDWord (toMemory state.resources.space) address).mapError ReadFault.machine

theorem loadWord_ok (state : State) (borrower identifier : Nat) (address : Word) (value : BitVec 32)
    (success : loadWord state borrower identifier address = .ok value) :
    ∃ loan, authorize state borrower identifier = .ok loan ∧
      Subregion (wordRegion address) loan.region ∧
      loadDWord (toMemory state.resources.space) address = .ok value := by
  cases authorized : authorize state borrower identifier with
  | error fault => simp [loadWord, authorized, Except.mapError] at success
  | ok loan =>
    by_cases fits : Subregion (wordRegion address) loan.region
    · cases observed : loadDWord (toMemory state.resources.space) address with
      | error fault => simp [loadWord, authorized, Except.mapError, fits, observed] at success
      | ok word =>
        simp [loadWord, authorized, Except.mapError, fits, observed] at success
        cases success
        exact ⟨loan, rfl, fits, rfl⟩
    · simp [loadWord, authorized, Except.mapError, fits] at success

theorem loadWord_success (state : State) (borrower identifier : Nat) (address : Word) (value : BitVec 32)
    (loan : Loan) (authorized : authorize state borrower identifier = .ok loan)
    (fits : Subregion (wordRegion address) loan.region)
    (observed : loadDWord (toMemory state.resources.space) address = .ok value) :
    loadWord state borrower identifier address = .ok value := by
  simp [loadWord, authorized, fits, observed, Except.mapError]

/-- Nonwrapping natural subregions give the modular machine operand's cells. -/
theorem word_inside (loan : Loan) (regionValid : loan.region.valid = true) (address : Word)
    (fits : Subregion (wordRegion address) loan.region) (offset : Nat) (bound : offset < 4) :
    loan.region.Contains (address + BitVec.ofNat 64 offset) := by
  have valid : 0 < loan.region.length ∧ loan.region.base.toNat + loan.region.length ≤ 2^64 ∧
      (loan.region.base.toNat + loan.region.length ≤ 2^47 ∨ 2^64 - 2^47 ≤ loan.region.base.toNat) :=
    of_decide_eq_true regionValid
  have lower := fits.1
  have upper := fits.2
  change loan.region.base.toNat ≤ address.toNat at lower
  change address.toNat + 4 ≤ loan.region.base.toNat + loan.region.length at upper
  have small : offset < 2^64 := by omega
  have sum : address.toNat + offset < 2^64 := by omega
  change loan.region.base.toNat ≤ (address + BitVec.ofNat 64 offset).toNat ∧
    (address + BitVec.ofNat 64 offset).toNat < loan.region.base.toNat + loan.region.length
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]
  omega

/-- Well-formed readable loans admit every contained four-byte operand. -/
theorem loadWord_exists (state : State) (borrower identifier : Nat) (address : Word)
    (loan : Loan) (valid : WellFormed state)
    (authorized : authorize state borrower identifier = .ok loan)
    (fits : Subregion (wordRegion address) loan.region) :
    ∃ value, loadWord state borrower identifier address = .ok value := by
  have live := (authorize_ok _ _ _ _ authorized).1
  obtain ⟨_, _, _, _, _, regionValid, readable⟩ := (valid.2 _ _ live).2
  have byteAt : ∀ offset, offset < 4 → ∃ byte,
      readDataByte (toMemory state.resources.space) (address + BitVec.ofNat 64 offset) = .ok byte := by
    intro offset bound
    have inside := word_inside loan regionValid address fits offset bound
    obtain ⟨cell, stored, canRead⟩ := readable _ inside
    have canonical := valid_contains_canonical loan.region regionValid _ inside
    exact ⟨cell.byte, by simp [readDataByte, canonical, toMemory, stored, canRead]⟩
  obtain ⟨b0, at0⟩ := byteAt 0 (by decide)
  obtain ⟨b1, at1⟩ := byteAt 1 (by decide)
  obtain ⟨b2, at2⟩ := byteAt 2 (by decide)
  obtain ⟨b3, at3⟩ := byteAt 3 (by decide)
  have noWrap : ¬ address.toNat + 3 ≥ 2^64 := by
    have regionBound := (of_decide_eq_true regionValid).2.1
    have upper := fits.2
    change address.toNat + 4 ≤ loan.region.base.toNat + loan.region.length at upper
    omega
  simp only [BitVec.add_zero] at at0 at1 at2 at3
  refine ⟨joinDWord b0 b1 b2 b3, loadWord_success _ _ _ _ _ loan authorized fits ?_⟩
  simp [loadDWord, noWrap, at0, at1, at2, at3]

/-- A successful read has the same value after any admitted history in which
its loan remains live. The endpoint liveness test suffices because IDs never return. -/
theorem History.loadWord_stable {before after : State} (history : History before after)
    (valid : WellFormed before) (borrower identifier : Nat) (address : Word) (value : BitVec 32)
    (success : loadWord before borrower identifier address = .ok value)
    (survives : (after.loans identifier).isSome = true) :
    loadWord after borrower identifier address = .ok value := by
  obtain ⟨loan, authorized, fits, observed⟩ := loadWord_ok _ _ _ _ _ success
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
    apply loadWord_success _ _ _ _ _ loan finalAuthority fits
    apply (loadDWord_congr _ _ _ ?_).trans observed
    intro offset bound
    exact (toMemory_agrees_at _ _ _ (cells _ (word_inside loan regionValid address fits offset bound))).1

/-- A relational cell snapshot transports independently supplied readable bytes.
The initial BufferAt premise still binds the bytes to memory. -/
theorem buffer_frame (before after : State) (region : Region) (base : Word) (bytes : List Byte)
    (same : ∀ address, region.Contains address →
      after.resources.space.cells address = before.resources.space.cells address)
    (inside : ∀ offset, offset < bytes.length → region.Contains (base + BitVec.ofNat 64 offset))
    (buffer : BufferAt (toMemory before.resources.space) base bytes) :
    BufferAt (toMemory after.resources.space) base bytes := by
  refine ⟨buffer.1, ?_⟩
  intro offset byte present
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? present
  have reads := (toMemory_agrees_at _ _ _ (same _ (inside offset bound))).1
  unfold readDataByte
  rw [reads]
  exact buffer.2 offset byte present

theorem History.buffer_stable {before after : State} (history : History before after)
    (valid : WellFormed before) (identifier : Nat) (below : identifier < before.nextLoan)
    (loan : Loan) (live : after.loans identifier = some loan) (base : Word) (bytes : List Byte)
    (inside : ∀ offset, offset < bytes.length → loan.region.Contains (base + BitVec.ofNat 64 offset))
    (buffer : BufferAt (toMemory before.resources.space) base bytes) :
    BufferAt (toMemory after.resources.space) base bytes :=
  buffer_frame before after loan.region base bytes
    (history.loan_stable valid identifier below loan live).2 inside buffer

end EDSL.OS.Borrowing
