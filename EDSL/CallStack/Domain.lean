/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Geometry
import EDSL.Comparison64.Domain

set_option warningAsError true

namespace EDSL.CallStack.Domain
open X86 OS OS.AddressSpace

/-- The entire private allocation ends at the original caller slot. -/
def privateRegion : Region := ⟨65528, 16⟩

/-- The ticket comes from the existing world's fresh allocation frontier;
`allocated` below checks its issuance, including the initial epoch. -/
def ticket (bytes : List Byte) : Ownership.Ticket :=
  ⟨(Grading.Domain.shared bytes).resources.frontier, 0⟩

def frame (bytes : List Byte) : StackFrame.Descriptor :=
  ⟨Comparison64.Domain.call bytes, ticket bytes, 16⟩

/-- This concrete endpoint is justified by the actual checked allocation,
not by assuming an arbitrary resource update preserves loans or memory. -/
def shared (bytes : List Byte) : Borrowing.State :=
  { Grading.Domain.shared bytes with resources :=
      (Ownership.install (Grading.Domain.shared bytes).resources
        (mapUnchecked (Grading.Domain.shared bytes).resources.space privateRegion readWrite)
        (frame bytes).owner privateRegion) }

theorem frame_region (bytes : List Byte) : (frame bytes).region = privateRegion := rfl

theorem private_free (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    allUnmapped (Grading.Domain.space bytes) privateRegion = true := by
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside privateRegion (by decide) address member
  change 65528 ≤ address.toNat ∧ address.toNat < 65544 at inside
  rw [Grading.Domain.cells_far bytes bound address (by omega)]
  have stack : ¬Grading.Domain.stackRegion.Contains address := by
    change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8)
    omega
  have first : ¬Grading.Domain.regionA.Contains address := by
    change ¬(131072 ≤ address.toNat ∧ address.toNat < 131072 + 16)
    omega
  have second : ¬Grading.Domain.regionB.Contains address := by
    change ¬(196608 ≤ address.toNat ∧ address.toNat < 196608 + 8)
    omega
  simp only [Grading.Domain.payload, stack, first, second, ↓reduceIte, Option.isNone_none]

theorem ownership_allocated (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Ownership.allocate (Grading.Domain.shared bytes).resources (frame bytes).owner
      privateRegion readWrite = .ok ((shared bytes).resources, ticket bytes) := by
  exact Ownership.allocate_success _ _ _ _
    (Comparison64.Domain.contract bytes positive bound).wellFormed.1
    (by decide) (by decide) (private_free bytes bound)

/-- The borrowing gate performs the allocation for principal 11, returning
the actual frontier ticket (identifier 4, epoch 0), while retaining all loans. -/
theorem allocated (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.mutate (Grading.Domain.shared bytes)
      (.allocate (frame bytes).owner privateRegion readWrite) =
      .ok (shared bytes, some (ticket bytes)) := by
  have allowed : Borrowing.allowed (Grading.Domain.shared bytes)
      (.allocate (frame bytes).owner privateRegion readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (Grading.Domain.shared bytes).loans identifier <;> rfl
  simp only [Borrowing.mutate, allowed, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Ownership.Mutation.run, ownership_allocated bytes positive bound,
    Except.map, Except.mapError]
  rfl

theorem allocation_history (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Borrowing.History (Grading.Domain.shared bytes) (shared bytes) :=
  .next (.mutate (allocated bytes positive bound)) .refl

/-- Every original live loan, including the immutable arrays, retains its
actual cells and permissions along the checked allocation history. -/
theorem loan_cells_preserved (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (identifier : Nat) (loan : Borrowing.Loan)
    (live : (Grading.Domain.shared bytes).loans identifier = some loan) :
    (shared bytes).loans identifier = some loan ∧
      ∀ address, loan.region.Contains address →
        (shared bytes).resources.space.cells address =
          (Grading.Domain.shared bytes).resources.space.cells address := by
  have valid := (Comparison64.Domain.contract bytes positive bound).wellFormed
  exact ⟨live, ((allocation_history bytes positive bound).loan_stable valid identifier
    (valid.2 identifier loan live).1 loan live).2⟩

/-- The original code and caller word are transported from the existing
domain through real history; symbolic code bytes are never expanded. -/
theorem call_contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    CallResources.Contract (frame bytes).call (shared bytes) := by
  have base := Comparison64.Domain.contract bytes positive bound
  have history := allocation_history bytes positive bound
  obtain ⟨codeLoan, codeCells⟩ := base.codeLoan.frame base.wellFormed history rfl
  obtain ⟨stackLoan, stackCells⟩ := base.stackLoan.frame base.wellFormed history rfl
  exact ⟨history.wellFormed base.wellFormed, codeLoan, stackLoan,
    agrees_code _ _ _ _ codeCells base.code,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans base.stack,
    base.returnCanonical, base.stackBound, base.postStackCanonical⟩

/-- These are the actual initialized allocation cells, obtained from checked
Ownership allocation, including current whole-byte read/write permissions. -/
theorem private_cells (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (address : Word)
    (inside : privateRegion.Contains address) :
    (shared bytes).resources.space.cells address = some ⟨0, readWrite⟩ :=
  (Ownership.allocate_initialized _ _ _ _ _
    (ownership_allocated bytes positive bound)).1 address inside

/-- Every wholly contained qword is writable, including all seven unaligned
starts. The proof checks all eight actual cells, rather than just its base. -/
theorem private_writable (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (address : Word)
    (slot : StackFrame.Slot (frame bytes) address) :
    canStoreQWord (toMemory (shared bytes).resources.space) address = true := by
  change 65528 ≤ address.toNat ∧ address.toNat + 8 ≤ 65544 at slot
  have current (offset : Word) (small : offset.toNat < 8) :
      (toMemory (shared bytes).resources.space).read (address + offset) = some 0 ∧
      (toMemory (shared bytes).resources.space).writable (address + offset) = true ∧
      canonical (address + offset) = true := by
    have total : address.toNat + offset.toNat < 2^64 := by omega
    have natural : (address + offset).toNat = address.toNat + offset.toNat := by
      simp only [BitVec.toNat_add, Nat.mod_eq_of_lt total]
    have inside : privateRegion.Contains (address + offset) := by
      change 65528 ≤ (address + offset).toNat ∧ (address + offset).toNat < 65544
      rw [natural]
      omega
    have cell := private_cells bytes positive bound (address + offset) inside
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [toMemory]; rw [cell]; rfl
    · dsimp only [toMemory]; rw [cell]; rfl
    · simp only [canonical, natural, decide_eq_true_eq]
      exact Or.inl (by omega)
  have read (offset : Word) (small : offset.toNat < 8) := (current offset small).1
  have write (offset : Word) (small : offset.toNat < 8) := (current offset small).2.1
  have canon (offset : Word) (small : offset.toNat < 8) := (current offset small).2.2
  have atZero :
      (toMemory (shared bytes).resources.space).read address = some 0 ∧
      (toMemory (shared bytes).resources.space).writable address = true ∧
      canonical address = true := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using current 0 (by decide)
  simp (disch := decide) only [canStoreQWord, qwordAddressable, qwordWritable,
    read, write, canon, atZero.1, atZero.2.1, atZero.2.2,
    Option.isSome_some, Bool.and_true, decide_eq_true_eq]
  omega

theorem unborrowed (bytes : List Byte) :
    ∀ identifier loan, (shared bytes).loans identifier = some loan →
      loan.ticket.identifier ≠ (frame bytes).ticket.identifier := by
  intro identifier loan live
  by_cases below : identifier < 4
  · simp only [shared, Grading.Domain.shared, below, ↓reduceIte, Option.some.injEq] at live
    subst loan
    change identifier ≠ 4
    omega
  · simp only [shared, Grading.Domain.shared, below, ↓reduceIte, reduceCtorEq] at live

/-- Present allocation owner/epoch authority and all nine whole qword
permissions establish the complete private frame, without execution premises. -/
theorem contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    StackFrame.Contract (frame bytes) (shared bytes) := by
  have current := (Ownership.allocate_wellFormed _ _ _ _ _
    (Comparison64.Domain.contract bytes positive bound).wellFormed.1
    (ownership_allocated bytes positive bound)).2.1
  obtain ⟨allocation, found, owner, epoch⟩ := current
  have actual : allocation = ⟨(frame bytes).owner, 0, privateRegion⟩ := by
    simpa only [shared, ticket, Ownership.install, ↓reduceIte, Option.some.injEq] using found.symm
  have region : allocation.region = (frame bytes).region := by
    rw [actual, frame_region]
  refine ⟨call_contract bytes positive bound,
    ⟨allocation, Ownership.authorize_success _ _ _ _ found owner epoch, region⟩,
    by change 16 ≤ (65544 : Word).toNat; decide, ?_, unborrowed bytes⟩
  intro address slot
  refine ⟨allocation, found, owner, epoch, ?_, private_writable bytes positive bound address slot⟩
  simpa only [Ownership.containsQWord, region, decide_eq_true_eq,
    StackFrame.Slot, Borrowing.Subregion, qwordRegion] using slot

def resource (program : Program) (argument : Word) : Resources :=
  ⟨shared program.bytes, frame program.bytes, argument⟩

/-- The other incoming GPRs (including RAX) and all flags are arbitrary.
The machine is coupled to the complete evolved OS world. -/
def initial (program : Program) (argument : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  registers register := match register with
    | .rdi => argument
    | .rsp => 65544
    | _ => registers register
  rip := 4096 + BitVec.ofNat 64 program.entry
  flags := flags
  memory := toMemory (shared program.bytes).resources.space

/-- Every bounded code window with a selected in-bounds entry admits every
full64 argument and arbitrary other incoming GPRs/flags. Only present resource
facts are required: there is no decoding, CFG, run, result or budget premise. -/
theorem resource_pre (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (argument : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    ResourcePre program (resource program argument) (initial program argument registers flags) :=
  ⟨⟨contract program.bytes (by omega) bound, rfl⟩,
    rfl, rfl, entry, rfl, rfl, by change 16 ≤ 16; decide,
    by change (65544 : Word).toNat % 16 = 8; decide⟩

/-- The existing resource-to-machine implication supplies raw admission;
this theorem makes no claim about execution or universal correctness. -/
theorem raw_pre (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) (argument : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    Pre program (resourceInput (resource program argument))
      (initial program argument registers flags) :=
  (resource_pre program entry bound argument registers flags).machine

/-- A full64 witness crossing the unsigned wrap boundary after two increments.
Its admission is independent of every selected byte and entry offset. -/
theorem nonvacuous (program : Program) (entry : program.entry < program.bytes.length)
    (bound : program.bytes.length ≤ 4096) :
    ∃ resources machine, ResourcePre program resources machine ∧
      Pre program (resourceInput resources) machine ∧
      2^32 ≤ (resourceInput resources).value.toNat ∧
      (resourceInput resources).value.toNat + 2 = 2^64 := by
  exact ⟨resource program 0xfffffffffffffffe, initial program 0xfffffffffffffffe,
    resource_pre program entry bound _, raw_pre program entry bound _,
    by change 2^32 ≤ (0xfffffffffffffffe : Word).toNat; decide,
    by change (0xfffffffffffffffe : Word).toNat + 2 = 2^64; decide⟩

def unsupported : Program := ⟨[0xff], 0⟩

/-- Unsupported code still inhabits the complete current resource domain with
a full64 argument. This is admission, not execution success or a defect. -/
theorem unsupported_admitted :
    ResourcePre unsupported (resource unsupported 0xfffffffffffffffe)
      (initial unsupported 0xfffffffffffffffe) :=
  resource_pre unsupported (by decide) (by decide) _

end EDSL.CallStack.Domain
