/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Geometry
import EDSL.Comparison64.Domain

set_option warningAsError true

namespace EDSL.OS.Borrowing
open X86 AddressSpace

private theorem canStoreQWord_cells {before after : Space} {address : Word}
    (noWrap : address.toNat + 7 < 2^64)
    (cells : ∀ query, (qwordRegion address).Contains query →
      after.cells query = before.cells query) :
    canStoreQWord (toMemory after) address = canStoreQWord (toMemory before) address := by
  have point (offset : Word) (small : offset.toNat < 8) :
      (toMemory after).read (address + offset) = (toMemory before).read (address + offset) ∧
      (toMemory after).writable (address + offset) =
        (toMemory before).writable (address + offset) := by
    have total : address.toNat + offset.toNat < 2^64 := by omega
    have inside : (qwordRegion address).Contains (address + offset) := by
      change address.toNat ≤ (address + offset).toNat ∧
        (address + offset).toNat < address.toNat + 8
      simp only [BitVec.toNat_add, Nat.mod_eq_of_lt total]
      omega
    have agrees := toMemory_agrees_at after before _ (cells _ inside)
    exact ⟨agrees.1, agrees.2.1⟩
  have zero : (toMemory after).read address = (toMemory before).read address ∧
      (toMemory after).writable address = (toMemory before).writable address := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using point 0 (by decide)
  simp (disch := decide) only [canStoreQWord, qwordWritable, zero.1, zero.2,
    (point 1 (by decide)).1, (point 1 (by decide)).2,
    (point 2 (by decide)).1, (point 2 (by decide)).2,
    (point 3 (by decide)).1, (point 3 (by decide)).2,
    (point 4 (by decide)).1, (point 4 (by decide)).2,
    (point 5 (by decide)).1, (point 5 (by decide)).2,
    (point 6 (by decide)).1, (point 6 (by decide)).2,
    (point 7 (by decide)).1, (point 7 (by decide)).2]

/-- Checked history transports the original code/caller loans. Only the private
allocation must retain its metadata and cells: unrelated allocations may be
issued or written, so equality of the complete allocation tables is unnecessary. -/
theorem transportStackContract {frame : StackFrame.Descriptor} {before after : State}
    (contract : StackFrame.Contract frame before) (history : History before after)
    (loans : after.loans = before.loans)
    (preserves : Ownership.PreservesAllocation before.resources after.resources
      frame.ticket.identifier) : StackFrame.Contract frame after := by
  obtain ⟨codeLoan, codeCells⟩ := contract.pureCall.codeLoan.frame contract.wellFormed history
    (congrFun loans frame.call.codeLoan)
  obtain ⟨stackLoan, stackCells⟩ := contract.pureCall.stackLoan.frame contract.wellFormed history
    (congrFun loans frame.call.stackLoan)
  have pureCall : CallResources.Contract frame.call after :=
    ⟨history.wellFormed contract.wellFormed, codeLoan, stackLoan,
      agrees_code _ _ _ _ codeCells contract.pureCall.code,
      (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans contract.pureCall.stack,
      contract.pureCall.returnCanonical, contract.pureCall.stackBound,
      contract.pureCall.postStackCanonical⟩
  obtain ⟨allocation, found, owner, epoch, region⟩ := contract.authority
  have retained := (preserves allocation found).1
  refine ⟨pureCall,
    ⟨allocation, Ownership.authorize_success _ _ _ _ retained owner epoch, region⟩,
    contract.topBound, ?_, ?_⟩
  · intro address slot
    obtain ⟨entry, present, owns, version, fits, writable⟩ := contract.ready address slot
    obtain ⟨current, cells⟩ := preserves entry present
    refine ⟨entry, current, owns, version, fits, ?_⟩
    have limit := (of_decide_eq_true (contract.wellFormed.1.1 _ _ present).2.1).2.1
    have bounds := of_decide_eq_true fits
    have noWrap : address.toNat + 7 < 2^64 := by
      change entry.region.base.toNat ≤ address.toNat ∧
        address.toNat + 8 ≤ entry.region.base.toNat + entry.region.length at bounds
      omega
    rw [canStoreQWord_cells noWrap (fun query inside =>
      cells query (Ownership.containsQWord_inside entry address query fits inside))]
    exact writable
  · intro identifier loan live
    exact contract.unborrowed identifier loan (by rwa [← loans])

end EDSL.OS.Borrowing

namespace EDSL.CallStack.CapacityDomain
open X86 OS OS.AddressSpace

/-- Exact supported family for this fixed loader geometry. Capacities below
eight have no complete qword slots; CPU caller admission separately needs 16. -/
def Supported (capacity : Nat) : Prop := 0 < capacity ∧ capacity ≤ 4096

instance (capacity : Nat) : Decidable (Supported capacity) :=
  inferInstanceAs (Decidable (0 < capacity ∧ capacity ≤ 4096))

theorem supported32 : Supported 32 := by decide

/-- Natural subtraction is checked below; this interval ends at the original
caller slot, independently of the machine's later stack pointer. -/
def privateRegion (capacity : Nat) : Region :=
  ⟨BitVec.ofNat 64 (65544 - capacity), capacity⟩

def ticket (bytes : List Byte) : Ownership.Ticket :=
  ⟨(Grading.Domain.shared bytes).resources.frontier, 0⟩

def frame (capacity : Nat) (bytes : List Byte) : StackFrame.Descriptor :=
  ⟨Comparison64.Domain.call bytes, ticket bytes, capacity⟩

def shared (capacity : Nat) (bytes : List Byte) : Borrowing.State :=
  { Grading.Domain.shared bytes with resources :=
      (Ownership.install (Grading.Domain.shared bytes).resources
        (mapUnchecked (Grading.Domain.shared bytes).resources.space
          (privateRegion capacity) readWrite)
        (frame capacity bytes).owner (privateRegion capacity)) }

theorem frame_region (capacity : Nat) (bytes : List Byte) :
    (frame capacity bytes).region = privateRegion capacity := rfl

theorem private_bounds (capacity : Nat) (supported : Supported capacity) :
    (privateRegion capacity).base.toNat = 65544 - capacity ∧
      (privateRegion capacity).base.toNat + (privateRegion capacity).length = 65544 := by
  have upper := supported.2
  have small : 65544 - capacity < 2^64 := by omega
  constructor
  · simp only [privateRegion, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  · simp only [privateRegion, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    omega

theorem private_inside_iff (capacity : Nat) (supported : Supported capacity) (address : Word) :
    (privateRegion capacity).Contains address ↔
      65544 - capacity ≤ address.toNat ∧ address.toNat < 65544 := by
  unfold Region.Contains
  rw [(private_bounds capacity supported).2, (private_bounds capacity supported).1]

theorem private_valid (capacity : Nat) (supported : Supported capacity) :
    (privateRegion capacity).valid = true := by
  simp only [Region.valid, decide_eq_true_eq, (private_bounds capacity supported).2]
  exact ⟨supported.1, by decide, Or.inl (by decide)⟩

/-- The complete interval is separated from code, original caller RAM and both
old arrays, with no modular wrapping or alignment premise. -/
theorem private_separate (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    Ownership.Disjoint (privateRegion capacity) (Grading.Domain.codeRegion bytes) ∧
      Ownership.Disjoint (privateRegion capacity) Grading.Domain.stackRegion ∧
      Ownership.Disjoint (privateRegion capacity) Grading.Domain.regionA ∧
      Ownership.Disjoint (privateRegion capacity) Grading.Domain.regionB := by
  have upper := supported.2
  simp only [Ownership.Disjoint]
  rw [(private_bounds capacity supported).2, (private_bounds capacity supported).1]
  change (65544 ≤ 4096 ∨ 4096 + bytes.length ≤ 65544 - capacity) ∧
    (65544 ≤ 65544 ∨ 65544 + 8 ≤ 65544 - capacity) ∧
    (65544 ≤ 131072 ∨ 131072 + 16 ≤ 65544 - capacity) ∧
    (65544 ≤ 196608 ∨ 196608 + 8 ≤ 65544 - capacity)
  omega

theorem ticket_fresh (capacity : Nat) (bytes : List Byte) :
    ticket bytes = ⟨4, 0⟩ ∧ (shared capacity bytes).resources.frontier = 5 := ⟨rfl, rfl⟩

theorem private_free (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    allUnmapped (Grading.Domain.space bytes) (privateRegion capacity) = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := (private_inside_iff capacity supported address).mp
    (Ownership.addresses_inside _ (private_valid capacity supported) address member)
  have upper := supported.2
  rw [Grading.Domain.cells_far bytes bound address (by omega)]
  have stack : ¬Grading.Domain.stackRegion.Contains address := by
    change ¬(65544 ≤ address.toNat ∧ address.toNat < 65552)
    omega
  have first : ¬Grading.Domain.regionA.Contains address := by
    change ¬(131072 ≤ address.toNat ∧ address.toNat < 131088)
    omega
  have second : ¬Grading.Domain.regionB.Contains address := by
    change ¬(196608 ≤ address.toNat ∧ address.toNat < 196616)
    omega
  simp only [Grading.Domain.payload, stack, first, second, ↓reduceIte, Option.isNone_none]

theorem ownership_allocated (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Ownership.allocate (Grading.Domain.shared bytes).resources (frame capacity bytes).owner
      (privateRegion capacity) readWrite = .ok ((shared capacity bytes).resources, ticket bytes) :=
  Ownership.allocate_success _ _ _ _
    (Comparison64.Domain.contract bytes positive bound).wellFormed.1
    (private_valid capacity supported) (by decide) (private_free capacity supported bytes bound)

theorem allocated (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Borrowing.mutate (Grading.Domain.shared bytes)
      (.allocate (frame capacity bytes).owner (privateRegion capacity) readWrite) =
      .ok (shared capacity bytes, some (ticket bytes)) := by
  have allowed : Borrowing.allowed (Grading.Domain.shared bytes)
      (.allocate (frame capacity bytes).owner (privateRegion capacity) readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (Grading.Domain.shared bytes).loans identifier <;> rfl
  simp only [Borrowing.mutate, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Ownership.Mutation.run, ownership_allocated capacity supported bytes positive bound,
    Except.map, Except.mapError]
  rfl

theorem allocation_history (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Borrowing.History (Grading.Domain.shared bytes) (shared capacity bytes) :=
  .next (.mutate (allocated capacity supported bytes positive bound)) .refl

theorem loan_cells_preserved (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (identifier : Nat) (loan : Borrowing.Loan)
    (live : (Grading.Domain.shared bytes).loans identifier = some loan) :
    (shared capacity bytes).loans identifier = some loan ∧
      ∀ address, loan.region.Contains address →
        (shared capacity bytes).resources.space.cells address =
          (Grading.Domain.shared bytes).resources.space.cells address := by
  have valid := (Comparison64.Domain.contract bytes positive bound).wellFormed
  exact ⟨live, ((allocation_history capacity supported bytes positive bound).loan_stable valid
    identifier (valid.2 identifier loan live).1 loan live).2⟩

theorem call_contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    CallResources.Contract (frame capacity bytes).call (shared capacity bytes) := by
  have base := Comparison64.Domain.contract bytes positive bound
  have history := allocation_history capacity supported bytes positive bound
  obtain ⟨codeLoan, codeCells⟩ := base.codeLoan.frame base.wellFormed history rfl
  obtain ⟨stackLoan, stackCells⟩ := base.stackLoan.frame base.wellFormed history rfl
  exact ⟨history.wellFormed base.wellFormed, codeLoan, stackLoan,
    agrees_code _ _ _ _ codeCells base.code,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans base.stack,
    base.returnCanonical, base.stackBound, base.postStackCanonical⟩

theorem private_cells (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (address : Word) (inside : (privateRegion capacity).Contains address) :
    (shared capacity bytes).resources.space.cells address = some ⟨0, readWrite⟩ :=
  (Ownership.allocate_initialized _ _ _ _ _
    (ownership_allocated capacity supported bytes positive bound)).1 address inside

/-- All wholly contained qwords, including unaligned starts, check all eight
current cells and their canonical read/write permissions. -/
theorem private_writable (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (address : Word) (slot : StackFrame.Slot (frame capacity bytes) address) :
    canStoreQWord (toMemory (shared capacity bytes).resources.space) address = true := by
  change (privateRegion capacity).base.toNat ≤ address.toNat ∧
    address.toNat + 8 ≤ (privateRegion capacity).base.toNat +
      (privateRegion capacity).length at slot
  rw [(private_bounds capacity supported).2, (private_bounds capacity supported).1] at slot
  have current (offset : Word) (small : offset.toNat < 8) :
      (toMemory (shared capacity bytes).resources.space).read (address + offset) = some 0 ∧
      (toMemory (shared capacity bytes).resources.space).writable (address + offset) = true ∧
      canonical (address + offset) = true := by
    have total : address.toNat + offset.toNat < 2^64 := by omega
    have natural : (address + offset).toNat = address.toNat + offset.toNat := by
      simp only [BitVec.toNat_add, Nat.mod_eq_of_lt total]
    have inside : (privateRegion capacity).Contains (address + offset) := by
      rw [private_inside_iff capacity supported, natural]
      omega
    have cell := private_cells capacity supported bytes positive bound (address + offset) inside
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [toMemory]; rw [cell]; rfl
    · dsimp only [toMemory]; rw [cell]; rfl
    · simp only [canonical, natural, decide_eq_true_eq]
      exact Or.inl (by omega)
  have read (offset : Word) (small : offset.toNat < 8) := (current offset small).1
  have write (offset : Word) (small : offset.toNat < 8) := (current offset small).2.1
  have canon (offset : Word) (small : offset.toNat < 8) := (current offset small).2.2
  have atZero :
      (toMemory (shared capacity bytes).resources.space).read address = some 0 ∧
      (toMemory (shared capacity bytes).resources.space).writable address = true ∧
      canonical address = true := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using current 0 (by decide)
  simp (disch := decide) only [canStoreQWord, qwordAddressable, qwordWritable,
    read, write, canon, atZero.1, atZero.2.1, atZero.2.2,
    Option.isSome_some, Bool.and_true, decide_eq_true_eq]
  omega

theorem unborrowed (capacity : Nat) (bytes : List Byte) :
    ∀ identifier loan, (shared capacity bytes).loans identifier = some loan →
      loan.ticket.identifier ≠ (frame capacity bytes).ticket.identifier := by
  intro identifier loan live
  by_cases below : identifier < 4
  · simp only [shared, Grading.Domain.shared, below, ↓reduceIte, Option.some.injEq] at live
    subst loan
    change identifier ≠ 4
    omega
  · simp only [shared, Grading.Domain.shared, below, ↓reduceIte, reduceCtorEq] at live

/-- Present authority from the checked allocation establishes the entire
capacity, with explicit bounds and no future execution premises. -/
theorem contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    StackFrame.Contract (frame capacity bytes) (shared capacity bytes) := by
  have current := (Ownership.allocate_wellFormed _ _ _ _ _
    (Comparison64.Domain.contract bytes positive bound).wellFormed.1
    (ownership_allocated capacity supported bytes positive bound)).2.1
  obtain ⟨allocation, found, owner, epoch⟩ := current
  have actual : allocation = ⟨(frame capacity bytes).owner, 0, privateRegion capacity⟩ := by
    simpa only [shared, ticket, Ownership.install, ↓reduceIte, Option.some.injEq] using found.symm
  have region : allocation.region = (frame capacity bytes).region := by
    rw [actual, frame_region]
  refine ⟨call_contract capacity supported bytes positive bound,
    ⟨allocation, Ownership.authorize_success _ _ _ _ found owner epoch, region⟩,
    by change capacity ≤ 65544; have := supported.2; omega, ?_, unborrowed capacity bytes⟩
  intro address slot
  refine ⟨allocation, found, owner, epoch, ?_,
    private_writable capacity supported bytes positive bound address slot⟩
  simpa only [Ownership.containsQWord, region, decide_eq_true_eq,
    StackFrame.Slot, Borrowing.Subregion, qwordRegion] using slot

end EDSL.CallStack.CapacityDomain
