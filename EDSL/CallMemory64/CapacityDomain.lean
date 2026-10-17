/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.CapacityDomain
import EDSL.CallMemory64.Contract
import EDSL.OS.CallMemory64.History

set_option warningAsError true

namespace EDSL.CallMemory64.CapacityDomain
open X86 OS OS.AddressSpace
open CallStack.CapacityDomain (Supported)

/-- A separate ordinary DATA8 allocation beyond all loader allocations. -/
def target : Word := 262144

def region : Region := qwordRegion target

def ticket (capacity : Nat) (bytes : List Byte) : Ownership.Ticket :=
  ⟨(CallStack.CapacityDomain.shared capacity bytes).resources.frontier, 0⟩

def descriptor (capacity : Nat) (bytes : List Byte) : OS.CallMemory64.Descriptor :=
  ⟨CallStack.CapacityDomain.frame capacity bytes, ticket capacity bytes, target⟩

def allocatedShared (capacity : Nat) (bytes : List Byte) : Borrowing.State :=
  { CallStack.CapacityDomain.shared capacity bytes with resources :=
      (Ownership.install (CallStack.CapacityDomain.shared capacity bytes).resources
        (mapUnchecked (CallStack.CapacityDomain.shared capacity bytes).resources.space
          region readWrite)
        (descriptor capacity bytes).owner region) }

theorem ticket_fresh (capacity : Nat) (bytes : List Byte) :
    ticket capacity bytes = ⟨5, 0⟩ ∧
      (CallStack.CapacityDomain.shared capacity bytes).resources.frontier = 5 ∧
      (allocatedShared capacity bytes).resources.frontier = 6 := ⟨rfl, rfl, rfl⟩

theorem separate (capacity : Nat) (bytes : List Byte) :
    (descriptor capacity bytes).ticket.identifier ≠
      (descriptor capacity bytes).frame.ticket.identifier := by
  change 5 ≠ 4
  decide

theorem target_free (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    allUnmapped (CallStack.CapacityDomain.shared capacity bytes).resources.space region = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside region (by decide) address member
  change 262144 ≤ address.toNat ∧ address.toNat < 262152 at inside
  have privateOutside : ¬(CallStack.CapacityDomain.privateRegion capacity).Contains address := by
    rw [CallStack.CapacityDomain.private_inside_iff capacity supported]
    omega
  change ((mapUnchecked (Grading.Domain.space bytes)
    (CallStack.CapacityDomain.privateRegion capacity) readWrite).cells address).isNone = true
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

theorem ownership_allocated (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Ownership.allocate (CallStack.CapacityDomain.shared capacity bytes).resources
      (descriptor capacity bytes).owner region readWrite =
      .ok ((allocatedShared capacity bytes).resources, ticket capacity bytes) :=
  Ownership.allocate_success _ _ _ _
    (CallStack.CapacityDomain.contract capacity supported bytes positive bound).wellFormed.1
    (by decide) (by decide) (target_free capacity supported bytes bound)

/-- Ticket 5 is issued by the actual Borrowing gate after private ticket 4. -/
theorem allocated (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Borrowing.mutate (CallStack.CapacityDomain.shared capacity bytes)
      (.allocate (descriptor capacity bytes).owner region readWrite) =
      .ok (allocatedShared capacity bytes, some (ticket capacity bytes)) := by
  have allowed : Borrowing.allowed (CallStack.CapacityDomain.shared capacity bytes)
      (.allocate (descriptor capacity bytes).owner region readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (CallStack.CapacityDomain.shared capacity bytes).loans identifier <;> rfl
  simp only [Borrowing.mutate, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Ownership.Mutation.run, ownership_allocated capacity supported bytes positive bound,
    Except.map, Except.mapError]
  rfl

theorem allocation_history (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Borrowing.History (CallStack.CapacityDomain.shared capacity bytes)
      (allocatedShared capacity bytes) :=
  .next (.mutate (allocated capacity supported bytes positive bound)) .refl

theorem allocation_preserves (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (identifier : Nat) :
    Ownership.PreservesAllocation (CallStack.CapacityDomain.shared capacity bytes).resources
      (allocatedShared capacity bytes).resources identifier := by
  apply Ownership.Mutation.run_preserves
    (.allocate (descriptor capacity bytes).owner region readWrite) _
    ((allocatedShared capacity bytes).resources, some (ticket capacity bytes)) identifier
    (CallStack.CapacityDomain.contract capacity supported bytes positive bound).wellFormed.1
  · simp only [Ownership.Mutation.run,
      ownership_allocated capacity supported bytes positive bound, Except.map]
  · simp only [Ownership.Mutation.target, ne_eq, reduceCtorEq, not_false_eq_true]

theorem allocated_stack_contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    StackFrame.Contract (descriptor capacity bytes).frame (allocatedShared capacity bytes) :=
  Borrowing.transportStackContract
    (CallStack.CapacityDomain.contract capacity supported bytes positive bound)
    (allocation_history capacity supported bytes positive bound) rfl
    (allocation_preserves capacity supported bytes positive bound _)

theorem call_contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    CallResources.Contract (descriptor capacity bytes).frame.call (allocatedShared capacity bytes) :=
  (allocated_stack_contract capacity supported bytes positive bound).pureCall

theorem data_cells (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (address : Word) (inside : region.Contains address) :
    (allocatedShared capacity bytes).resources.space.cells address = some ⟨0, readWrite⟩ :=
  (Ownership.allocate_initialized _ _ _ _ _
    (ownership_allocated capacity supported bytes positive bound)).1 address inside

theorem data_writable (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    canStoreQWord (toMemory (allocatedShared capacity bytes).resources.space) target = true := by
  have addressable : qwordAddressable target = true := by decide
  simp (disch := decide) only [canStoreQWord, addressable, Bool.true_and, qwordWritable,
    toMemory, data_cells capacity supported bytes positive bound, readWrite, Bool.and_self]
  rfl

theorem allocated_unborrowed (capacity : Nat) (bytes : List Byte) :
    ∀ identifier loan, (allocatedShared capacity bytes).loans identifier = some loan →
      loan.ticket.identifier ≠ (descriptor capacity bytes).ticket.identifier := by
  intro identifier loan live
  by_cases below : identifier < 4
  · simp only [allocatedShared, CallStack.CapacityDomain.shared, Grading.Domain.shared,
      below, ↓reduceIte, Option.some.injEq] at live
    subst loan
    change identifier ≠ 5
    omega
  · simp only [allocatedShared, CallStack.CapacityDomain.shared, Grading.Domain.shared,
      below, ↓reduceIte, reduceCtorEq] at live

theorem allocated_contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    OS.CallMemory64.Contract (descriptor capacity bytes) (allocatedShared capacity bytes) := by
  refine ⟨allocated_stack_contract capacity supported bytes positive bound, ?_,
    allocated_unborrowed capacity bytes, separate capacity bytes⟩
  exact ⟨⟨(descriptor capacity bytes).owner, 0, region⟩,
    by simp only [allocatedShared, Ownership.install, descriptor, ticket, ↓reduceIte],
    rfl, rfl, by change Ownership.containsQWord ⟨11, 0, region⟩ target = true; decide,
    data_writable capacity supported bytes positive bound⟩

/-- Arbitrary old contents are installed by an ordinary checked owner store.
The error fallback is proved unreachable under the stated capacity/code bounds. -/
def shared (capacity : Nat) (bytes : List Byte) (old : Word := 0) : Borrowing.State :=
  match Borrowing.mutate (allocatedShared capacity bytes)
      (.store64 (descriptor capacity bytes).owner (ticket capacity bytes) target old) with
  | .ok (evolved, _) => evolved
  | .error _ => allocatedShared capacity bytes

theorem initialized (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    Borrowing.mutate (allocatedShared capacity bytes)
      (.store64 (descriptor capacity bytes).owner (ticket capacity bytes) target old) =
      .ok (shared capacity bytes old, none) := by
  obtain ⟨evolved, success⟩ :=
    (allocated_contract capacity supported bytes positive bound).data_store64_enabled old
  change Borrowing.mutate (allocatedShared capacity bytes)
    (.store64 (descriptor capacity bytes).owner (ticket capacity bytes) target old) =
      .ok (evolved, none) at success
  unfold shared
  rw [success]

theorem initialization_history (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    Borrowing.History (CallStack.CapacityDomain.shared capacity bytes) (shared capacity bytes old) :=
  .next (.mutate (allocated capacity supported bytes positive bound))
    (.next (.mutate (initialized capacity supported bytes positive bound old)) .refl)

theorem initializer_effect (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    Borrowing.StoreEffect64 (allocatedShared capacity bytes) (shared capacity bytes old) target old :=
  Borrowing.store64_effect (initialized capacity supported bytes positive bound old)

/-- The actual DATA allocation and initialization preserve every earlier live
allocation, including private ticket 4, with its exact bytes and permissions. -/
theorem original_allocation (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word) (identifier : Nat) :
    Ownership.PreservesAllocation (CallStack.CapacityDomain.shared capacity bytes).resources
      (shared capacity bytes old).resources identifier := by
  have afterAllocate := allocation_preserves capacity supported bytes positive bound identifier
  have afterStore := Borrowing.store64_preservesAllocation
    (allocated_contract capacity supported bytes positive bound).wellFormed.1
    (initialized capacity supported bytes positive bound old) identifier
  intro allocation live
  have below :=
    ((CallStack.CapacityDomain.contract capacity supported bytes positive bound).wellFormed.1.1
      _ _ live).1
  have different : identifier ≠ (ticket capacity bytes).identifier := by
    change identifier < 5 at below
    change identifier ≠ 5
    omega
  exact afterAllocate.trans (afterStore different) allocation live

theorem loans_preserved (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    (shared capacity bytes old).loans = (Grading.Domain.shared bytes).loans ∧
      (shared capacity bytes old).nextLoan = (Grading.Domain.shared bytes).nextLoan :=
  ⟨(initializer_effect capacity supported bytes positive bound old).loans,
    (initializer_effect capacity supported bytes positive bound old).nextLoan⟩

/-- The generic transport runs through both current allocation and DATA store
history, rather than retaining an authority proof for an obsolete snapshot. -/
theorem stack_contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    StackFrame.Contract (descriptor capacity bytes).frame (shared capacity bytes old) :=
  Borrowing.transportStackContract
    (CallStack.CapacityDomain.contract capacity supported bytes positive bound)
    (initialization_history capacity supported bytes positive bound old)
    (loans_preserved capacity supported bytes positive bound old).1
    (original_allocation capacity supported bytes positive bound old _)

theorem contract (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    OS.CallMemory64.Contract (descriptor capacity bytes) (shared capacity bytes old) := by
  have afterStore := OS.CallMemory64.contract_data_store64
    (allocated_contract capacity supported bytes positive bound)
    (initialized capacity supported bytes positive bound old)
  exact ⟨stack_contract capacity supported bytes positive bound old,
    afterStore.word, afterStore.unborrowed, afterStore.separate⟩

theorem target_read (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    Borrowing.loadOwnedWord64 (shared capacity bytes old) (descriptor capacity bytes).owner
        (ticket capacity bytes) target = .ok old ∧
      readWord (toMemory (shared capacity bytes old).resources.space) target = .ok old :=
  ⟨Borrowing.store64_owned_readback (initialized capacity supported bytes positive bound old),
    Borrowing.store64_readWord (initialized capacity supported bytes positive bound old)⟩

theorem target_allocation (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    (shared capacity bytes old).resources.allocations (ticket capacity bytes).identifier =
      some ⟨(descriptor capacity bytes).owner, 0, region⟩ := by
  rw [(initializer_effect capacity supported bytes positive bound old).allocations]
  rfl

theorem target_current (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    Ownership.Current (shared capacity bytes old).resources (descriptor capacity bytes).owner
      (ticket capacity bytes) :=
  Borrowing.loadOwnedWord64_current _ _ _ _ _ (target_read capacity supported bytes positive bound old).1

theorem frontier (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word := 0) :
    (shared capacity bytes old).resources.frontier = 6 :=
  (initializer_effect capacity supported bytes positive bound old).frontier

theorem owned_read_iff (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old address value : Word) :
    Borrowing.loadOwnedWord64 (shared capacity bytes old) (descriptor capacity bytes).owner
        (ticket capacity bytes) address = .ok value ↔ address = target ∧ value = old := by
  constructor
  · intro observed
    obtain ⟨allocation, authorized, fits, _⟩ :=
      Borrowing.loadOwnedWord64_ok _ _ _ _ _ observed
    have found := (Ownership.authorize_ok _ _ _ _ authorized).1
    rw [target_allocation capacity supported bytes positive bound old] at found
    cases Option.some.inj found
    have bounds := of_decide_eq_true fits
    change 262144 ≤ address.toNat ∧ address.toNat + 8 ≤ 262152 at bounds
    have same : address = target := BitVec.eq_of_toNat_eq (by
      change address.toNat = 262144
      omega)
    subst address
    exact ⟨rfl, Except.ok.inj
      (observed.symm.trans (target_read capacity supported bytes positive bound old).1)⟩
  · rintro ⟨same, equal⟩
    rw [same, equal]
    exact (target_read capacity supported bytes positive bound old).1

theorem loan_cells_preserved (capacity : Nat) (supported : Supported capacity)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (old : Word) (identifier : Nat) (loan : Borrowing.Loan)
    (live : (Grading.Domain.shared bytes).loans identifier = some loan) :
    (shared capacity bytes old).loans identifier = some loan ∧
      ∀ address, loan.region.Contains address →
        (shared capacity bytes old).resources.space.cells address =
          (Grading.Domain.shared bytes).resources.space.cells address := by
  have retained : (shared capacity bytes old).loans identifier = some loan := by
    rw [(loans_preserved capacity supported bytes positive bound old).1]
    exact live
  have base := (Comparison64.Domain.contract bytes positive bound).wellFormed
  have history : Borrowing.History (Grading.Domain.shared bytes) (shared capacity bytes old) :=
    .next (.mutate (CallStack.CapacityDomain.allocated capacity supported bytes positive bound))
      (initialization_history capacity supported bytes positive bound old)
  exact ⟨retained, (history.loan_stable base identifier (base.2 _ _ live).1 loan retained).2⟩

/-- Full RAM coupling uses the initialized endpoint. RDX and all other unbound
registers retain their arbitrary seeds, independently of scalar/old contents. -/
def initialCPU (capacity : Nat) (program : CallStack.Program) (input : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  registers register := match register with
    | .rdi => target
    | .rsi => input
    | .rsp => (descriptor capacity program.bytes).frame.top
    | _ => registers register
  rip := (descriptor capacity program.bytes).frame.call.code + BitVec.ofNat 64 program.entry
  flags := flags
  memory := toMemory (shared capacity program.bytes old).resources.space

theorem current (capacity : Nat) (supported : Supported capacity)
    (program : CallStack.Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (input : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    OS.CallMemory64.Current (descriptor capacity program.bytes) (shared capacity program.bytes old)
      (initialCPU capacity program input old registers flags) :=
  ⟨contract capacity supported program.bytes (by omega) bound old, rfl⟩

def resource (capacity : Nat) (program : CallStack.Program) (input : Word) (old : Word := 0) :
    Resources :=
  ⟨shared capacity program.bytes old, descriptor capacity program.bytes, input⟩

/-- Arbitrary bounded programs and entries admit every scalar, old target,
register seed and flags. This proves present admission, not execution; the
ordinary-RAM, canonical-address, AC/CET and interference assumptions of the
existing CallMemory64 contract continue to apply. -/
theorem resource_pre (capacity : Nat) (supported : Supported capacity) (enough : 16 ≤ capacity)
    (program : CallStack.Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (input : Word) (old : Word := 0)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    ResourcePre program (resource capacity program input old)
      (initialCPU capacity program input old registers flags) :=
  ⟨current capacity supported program entry bound input old registers flags, rfl, rfl,
    entry, rfl, rfl, rfl, enough, by change (65544 : Word).toNat % 16 = 8; decide⟩

end EDSL.CallMemory64.CapacityDomain
