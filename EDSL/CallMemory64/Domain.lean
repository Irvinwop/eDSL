/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Domain
import EDSL.OS.CallMemory64.History

set_option warningAsError true

namespace EDSL.CallMemory64.Domain
open X86 OS OS.AddressSpace

/-- One ordinary DATA8 allocation, beyond every existing loader allocation. -/
def target : Word := 262144

def region : Region := qwordRegion target

/-- Issued after the actual private-stack allocation, from its next frontier. -/
def ticket (bytes : List Byte) : Ownership.Ticket :=
  ⟨(CallStack.Domain.shared bytes).resources.frontier, 0⟩

def descriptor (bytes : List Byte) : OS.CallMemory64.Descriptor :=
  ⟨CallStack.Domain.frame bytes, ticket bytes, target⟩

/-- The endpoint of the checked fresh allocation proved by `allocated`. -/
def allocatedShared (bytes : List Byte) : Borrowing.State :=
  { CallStack.Domain.shared bytes with resources :=
      (Ownership.install (CallStack.Domain.shared bytes).resources
        (mapUnchecked (CallStack.Domain.shared bytes).resources.space region readWrite)
        (descriptor bytes).owner region) }

theorem ticket_fresh (bytes : List Byte) :
    ticket bytes = ⟨5, 0⟩ ∧
      (CallStack.Domain.shared bytes).resources.frontier = 5 ∧
      (allocatedShared bytes).resources.frontier = 6 := ⟨rfl, rfl, rfl⟩

theorem separate (bytes : List Byte) :
    (descriptor bytes).ticket.identifier ≠ (descriptor bytes).frame.ticket.identifier := by
  change 5 ≠ 4
  decide

theorem target_free (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    allUnmapped (CallStack.Domain.shared bytes).resources.space region = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside region (by decide) address member
  change 262144 ≤ address.toNat ∧ address.toNat < 262152 at inside
  have privateOutside : ¬CallStack.Domain.privateRegion.Contains address := by
    change ¬(65528 ≤ address.toNat ∧ address.toNat < 65544)
    omega
  change ((mapUnchecked (Grading.Domain.space bytes) CallStack.Domain.privateRegion
    readWrite).cells address).isNone = true
  rw [map_frame _ _ _ _ privateOutside, Grading.Domain.cells_far bytes bound address (by omega)]
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

theorem ownership_allocated (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Ownership.allocate (CallStack.Domain.shared bytes).resources (descriptor bytes).owner
      region readWrite = .ok ((allocatedShared bytes).resources, ticket bytes) :=
  Ownership.allocate_success _ _ _ _
    (CallStack.Domain.contract bytes positive bound).wellFormed.1
    (by decide) (by decide) (target_free bytes bound)

/-- The actual borrowing gate issues ticket 5 while retaining the original
four live loans and the private-stack ticket 4 in this same world. -/
theorem allocated (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.mutate (CallStack.Domain.shared bytes)
      (.allocate (descriptor bytes).owner region readWrite) =
      .ok (allocatedShared bytes, some (ticket bytes)) := by
  have allowed : Borrowing.allowed (CallStack.Domain.shared bytes)
      (.allocate (descriptor bytes).owner region readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (CallStack.Domain.shared bytes).loans identifier <;> rfl
  simp only [Borrowing.mutate, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Ownership.Mutation.run, ownership_allocated bytes positive bound,
    Except.map, Except.mapError]
  rfl

theorem allocation_history (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.History (CallStack.Domain.shared bytes) (allocatedShared bytes) :=
  .next (.mutate (allocated bytes positive bound)) .refl

/-- Every prior live allocation retains its metadata and all actual cells. -/
theorem allocation_preserves (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (identifier : Nat) :
    Ownership.PreservesAllocation (CallStack.Domain.shared bytes).resources
      (allocatedShared bytes).resources identifier := by
  apply Ownership.Mutation.run_preserves
    (.allocate (descriptor bytes).owner region readWrite) _
    ((allocatedShared bytes).resources, some (ticket bytes)) identifier
    (CallStack.Domain.contract bytes positive bound).wellFormed.1
  · simp only [Ownership.Mutation.run, ownership_allocated bytes positive bound, Except.map]
  · simp only [Ownership.Mutation.target, ne_eq, reduceCtorEq, not_false_eq_true]

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

theorem call_contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    CallResources.Contract (descriptor bytes).frame.call (allocatedShared bytes) := by
  have base := (CallStack.Domain.contract bytes positive bound).pureCall
  have history := allocation_history bytes positive bound
  obtain ⟨codeLoan, codeCells⟩ := base.codeLoan.frame base.wellFormed history rfl
  obtain ⟨stackLoan, stackCells⟩ := base.stackLoan.frame base.wellFormed history rfl
  exact ⟨history.wellFormed base.wellFormed, codeLoan, stackLoan,
    agrees_code _ _ _ _ codeCells base.code,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans base.stack,
    base.returnCanonical, base.stackBound, base.postStackCanonical⟩

theorem allocated_stack_contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    StackFrame.Contract (descriptor bytes).frame (allocatedShared bytes) := by
  have base := CallStack.Domain.contract bytes positive bound
  obtain ⟨allocation, found, owner, epoch, regionEq⟩ := base.authority
  obtain ⟨current, _⟩ := allocation_preserves bytes positive bound _ allocation found
  refine ⟨call_contract bytes positive bound,
    ⟨allocation, Ownership.authorize_success _ _ _ _ current owner epoch, regionEq⟩,
    base.topBound, ?_, base.unborrowed⟩
  intro address slot
  obtain ⟨entry, present, owns, version, fits, writable⟩ := base.ready address slot
  obtain ⟨retained, cells⟩ := allocation_preserves bytes positive bound _ entry present
  refine ⟨entry, retained, owns, version, fits, ?_⟩
  have bounds := base.slot_bounds slot
  have noWrap : address.toNat + 7 < 2^64 := by
    have upper : address.toNat + 8 ≤ 65544 := bounds.2
    omega
  rw [canStoreQWord_cells noWrap (fun query inside =>
    cells query (Ownership.containsQWord_inside entry address query fits inside))]
  exact writable

theorem data_cells (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (address : Word) (inside : region.Contains address) :
    (allocatedShared bytes).resources.space.cells address = some ⟨0, readWrite⟩ :=
  (Ownership.allocate_initialized _ _ _ _ _
    (ownership_allocated bytes positive bound)).1 address inside

theorem data_writable (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    canStoreQWord (toMemory (allocatedShared bytes).resources.space) target = true := by
  have addressable : qwordAddressable target = true := by decide
  simp (disch := decide) only [canStoreQWord, addressable, Bool.true_and, qwordWritable,
    toMemory, data_cells bytes positive bound, readWrite, Bool.and_self]
  rfl

theorem allocated_unborrowed (bytes : List Byte) :
    ∀ identifier loan, (allocatedShared bytes).loans identifier = some loan →
      loan.ticket.identifier ≠ (descriptor bytes).ticket.identifier := by
  intro identifier loan live
  by_cases below : identifier < 4
  · simp only [allocatedShared, CallStack.Domain.shared, Grading.Domain.shared, below,
      ↓reduceIte, Option.some.injEq] at live
    subst loan
    change identifier ≠ 5
    omega
  · simp only [allocatedShared, CallStack.Domain.shared, Grading.Domain.shared, below,
      ↓reduceIte, reduceCtorEq] at live

theorem allocated_contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    OS.CallMemory64.Contract (descriptor bytes) (allocatedShared bytes) := by
  refine ⟨allocated_stack_contract bytes positive bound, ?_,
    allocated_unborrowed bytes, separate bytes⟩
  exact ⟨⟨(descriptor bytes).owner, 0, region⟩,
    by simp only [allocatedShared, Ownership.install, descriptor, ticket, ↓reduceIte],
    rfl, rfl, by change Ownership.containsQWord ⟨11, 0, region⟩ target = true; decide,
    data_writable bytes positive bound⟩

/-- Initialization is an ordinary checked DATA store, with no future callback.
`initialized` proves that the error fallback is unreachable for every admitted
code window and every arbitrary full64 initial target value. -/
def shared (bytes : List Byte) (old : Word := 0) : Borrowing.State :=
  match Borrowing.mutate (allocatedShared bytes)
      (.store64 (descriptor bytes).owner (ticket bytes) target old) with
  | .ok (evolved, _) => evolved
  | .error _ => allocatedShared bytes

theorem initialized (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    Borrowing.mutate (allocatedShared bytes)
      (.store64 (descriptor bytes).owner (ticket bytes) target old) =
      .ok (shared bytes old, none) := by
  obtain ⟨evolved, success⟩ := (allocated_contract bytes positive bound).data_store64_enabled old
  change Borrowing.mutate (allocatedShared bytes)
    (.store64 (descriptor bytes).owner (ticket bytes) target old) = .ok (evolved, none) at success
  unfold shared
  rw [success]

theorem initialization_history (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    Borrowing.History (CallStack.Domain.shared bytes) (shared bytes old) :=
  .next (.mutate (allocated bytes positive bound))
    (.next (.mutate (initialized bytes positive bound old)) .refl)

theorem initializer_effect (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    Borrowing.StoreEffect64 (allocatedShared bytes) (shared bytes old) target old :=
  Borrowing.store64_effect (initialized bytes positive bound old)

theorem contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    OS.CallMemory64.Contract (descriptor bytes) (shared bytes old) :=
  OS.CallMemory64.contract_data_store64 (allocated_contract bytes positive bound)
    (initialized bytes positive bound old)

theorem target_read (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    Borrowing.loadOwnedWord64 (shared bytes old) (descriptor bytes).owner (ticket bytes) target =
        .ok old ∧
      readWord (toMemory (shared bytes old).resources.space) target = .ok old :=
  ⟨Borrowing.store64_owned_readback (initialized bytes positive bound old),
    Borrowing.store64_readWord (initialized bytes positive bound old)⟩

theorem target_allocation (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    (shared bytes old).resources.allocations (ticket bytes).identifier =
      some ⟨(descriptor bytes).owner, 0, region⟩ := by
  rw [(initializer_effect bytes positive bound old).allocations]
  rfl

theorem target_current (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    Ownership.Current (shared bytes old).resources (descriptor bytes).owner (ticket bytes) :=
  Borrowing.loadOwnedWord64_current _ _ _ _ _ (target_read bytes positive bound old).1

theorem frontier (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    (shared bytes old).resources.frontier = 6 :=
  (initializer_effect bytes positive bound old).frontier

/-- The complete qword bound permits exactly one DATA start. This constrains
successful current owner reads, including unaligned boundary-crossing attempts. -/
theorem owned_read_iff (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old address value : Word) :
    Borrowing.loadOwnedWord64 (shared bytes old) (descriptor bytes).owner
        (ticket bytes) address = .ok value ↔ address = target ∧ value = old := by
  constructor
  · intro observed
    obtain ⟨allocation, authorized, fits, _⟩ :=
      Borrowing.loadOwnedWord64_ok _ _ _ _ _ observed
    have found := (Ownership.authorize_ok _ _ _ _ authorized).1
    rw [target_allocation bytes positive bound old] at found
    cases Option.some.inj found
    have bounds := of_decide_eq_true fits
    change 262144 ≤ address.toNat ∧ address.toNat + 8 ≤ 262152 at bounds
    have same : address = target := BitVec.eq_of_toNat_eq (by
      change address.toNat = 262144
      omega)
    subst address
    exact ⟨rfl, (Except.ok.inj (observed.symm.trans
      (target_read bytes positive bound old).1))⟩
  · rintro ⟨same, equal⟩
    rw [same, equal]
    exact (target_read bytes positive bound old).1

/-- Initialization changes only the fresh DATA cells. It preserves the complete
metadata and actual contents of every original live allocation. -/
theorem original_allocation (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) (identifier : Nat) :
    Ownership.PreservesAllocation (CallStack.Domain.shared bytes).resources
      (shared bytes old).resources identifier := by
  have afterAllocate := allocation_preserves bytes positive bound identifier
  have afterStore := Borrowing.store64_preservesAllocation
    (allocated_contract bytes positive bound).wellFormed.1 (initialized bytes positive bound old)
    identifier
  intro allocation live
  have below := ((CallStack.Domain.contract bytes positive bound).wellFormed.1.1 _ _ live).1
  have different : identifier ≠ (ticket bytes).identifier := by
    change identifier < 5 at below
    change identifier ≠ 5
    omega
  exact afterAllocate.trans (afterStore different) allocation live

theorem loans_preserved (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word := 0) :
    (shared bytes old).loans = (Grading.Domain.shared bytes).loans ∧
      (shared bytes old).nextLoan = (Grading.Domain.shared bytes).nextLoan :=
  ⟨(initializer_effect bytes positive bound old).loans,
    (initializer_effect bytes positive bound old).nextLoan⟩

/-- All original live loans remain present with their actual bytes and
permissions, including the full code window and original caller qword. -/
theorem loan_cells_preserved (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) (identifier : Nat) (loan : Borrowing.Loan)
    (live : (Grading.Domain.shared bytes).loans identifier = some loan) :
    (shared bytes old).loans identifier = some loan ∧
      ∀ address, loan.region.Contains address →
        (shared bytes old).resources.space.cells address =
          (Grading.Domain.shared bytes).resources.space.cells address := by
  have retained : (shared bytes old).loans identifier = some loan := by
    rw [(loans_preserved bytes positive bound old).1]
    exact live
  have base := (Comparison64.Domain.contract bytes positive bound).wellFormed
  have history : Borrowing.History (Grading.Domain.shared bytes) (shared bytes old) :=
    .next (.mutate (CallStack.Domain.allocated bytes positive bound))
      (initialization_history bytes positive bound old)
  exact ⟨retained, (history.loan_stable base identifier (base.2 _ _ live).1 loan retained).2⟩

/-- The machine binds the actual DATA pointer and scalar input separately.
All remaining GPRs, all flags, and the old target value are arbitrary. -/
def initial (program : CallStack.Program) (input : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  registers register := match register with
    | .rdi => target
    | .rsi => input
    | .rsp => (descriptor program.bytes).frame.top
    | _ => registers register
  rip := (descriptor program.bytes).frame.call.code + BitVec.ofNat 64 program.entry
  flags := flags
  memory := toMemory (shared program.bytes old).resources.space

/-- Every nonempty bounded code window and selected in-bounds entry has the
complete current resources. No decoding, execution, result or budget is assumed. -/
theorem current (program : CallStack.Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (input : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    OS.CallMemory64.Current (descriptor program.bytes) (shared program.bytes old)
      (initial program input old registers flags) :=
  ⟨contract program.bytes (by omega) bound old, rfl⟩

end EDSL.CallMemory64.Domain
