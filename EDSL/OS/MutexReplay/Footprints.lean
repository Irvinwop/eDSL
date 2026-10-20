/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Invariant
import EDSL.OS.MutexReplay.Ready
import EDSL.X86.StoreBuffer

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

namespace Footprints

/-- A word contained in a valid allocation cannot wrap, including in the
high canonical half of the address space. -/
theorem word_noWrap (allocation : Ownership.Allocation) (address : Word)
    (valid : allocation.region.valid = true)
    (fits : Ownership.containsWord allocation address = true) :
    address.toNat + 3 < 2^64 := by
  have bounds : allocation.region.base.toNat ≤ address.toNat ∧
      address.toNat + 4 ≤ allocation.region.base.toNat + allocation.region.length :=
    of_decide_eq_true fits
  have limit := (of_decide_eq_true valid).2.1
  omega

/-- The modular footprint used by machine stores lies in the natural-address
allocation. The nonwrapping premise is derived from allocation validity, so
small modular differences across address zero cannot create spurious overlap. -/
theorem word_inside (allocation : Ownership.Allocation) (address query : Word)
    (valid : allocation.region.valid = true)
    (fits : Ownership.containsWord allocation address = true)
    (inside : (query - address).toNat < 4) : allocation.region.Contains query :=
  Ownership.containsWord_inside allocation address query fits
    ((word_contains_iff address query (word_noWrap allocation address valid fits)).mpr inside)

/-- Separation of natural intervals frames every modular byte of a valid
region against a contained four-byte write. -/
theorem dwordDisjoint_of_regions (allocation : Ownership.Allocation) (address : Word)
    (region : Region) (valid : allocation.region.valid = true)
    (fits : Ownership.containsWord allocation address = true)
    (regionValid : region.valid = true) (separate : Ownership.Disjoint allocation.region region) :
    DWordDisjoint address region.base region.length := by
  intro offset bound
  have inside : region.Contains (region.base + BitVec.ofNat 64 offset) :=
    Ownership.addresses_inside region regionValid _
      (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)
  by_cases outside : 4 ≤ ((region.base + BitVec.ofNat 64 offset) - address).toNat
  · exact outside
  · exact False.elim (Ownership.disjoint_outside separate inside
      (word_inside allocation address _ valid fits (by omega)))

/-- Distinct live allocation IDs supply disjoint modular word footprints;
there is no additional separation check in the execution semantics. -/
theorem wordValid_separate {shared : Borrowing.State} {ownerA ownerB : Nat}
    {ticketA ticketB : Ownership.Ticket} {a b : Word}
    (world : Ownership.WellFormed shared.resources)
    (left : Mutex.WordValid shared ownerA ticketA a)
    (right : Mutex.WordValid shared ownerB ticketB b)
    (different : ticketA.identifier ≠ ticketB.identifier) : StoreBuffer.Separate a b := by
  obtain ⟨allocationA, foundA, _, _, fitsA, _⟩ := left
  obtain ⟨allocationB, foundB, _, _, fitsB, _⟩ := right
  have validA := (world.1 _ _ foundA).2.1
  have validB := (world.1 _ _ foundB).2.1
  have separate := world.2 _ _ _ _ foundA foundB different
  intro query
  by_cases outside : 4 ≤ (query - a).toNat
  · exact Or.inl outside
  · right
    by_cases outsideB : 4 ≤ (query - b).toNat
    · exact outsideB
    · exact False.elim (Ownership.disjoint_outside separate
        (word_inside allocationB b query validB fitsB (by omega))
        (word_inside allocationA a query validA fitsA (by omega)))

/-- Pointwise modular separation also frames all four operand offsets, even
without imposing a low-address restriction. -/
theorem dwordDisjoint_of_separate {a b : Word} (separate : StoreBuffer.Separate a b) :
    DWordDisjoint a b 4 := by
  intro offset bound
  have small : offset < 2^64 := by omega
  have within : ((b + BitVec.ofNat 64 offset) - b).toNat < 4 := by
    simpa only [offset_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using bound
  exact (separate (b + BitVec.ofNat 64 offset)).resolve_right (by omega)

/-- Stored read loans inhabit their live allocation. A word in a different
allocation therefore cannot change any byte of the loan's region. -/
theorem wordValid_loan_disjoint {shared : Borrowing.State} {owner loanId : Nat}
    {ticket : Ownership.Ticket} {address : Word} {loan : Borrowing.Loan}
    (valid : Borrowing.WellFormed shared)
    (word : Mutex.WordValid shared owner ticket address)
    (live : shared.loans loanId = some loan)
    (different : ticket.identifier ≠ loan.ticket.identifier) :
    DWordDisjoint address loan.region.base loan.region.length := by
  obtain ⟨allocation, found, _, _, fits, _⟩ := word
  obtain ⟨borrowed, foundBorrowed, _, _, subregion, regionValid, _⟩ := (valid.2 _ _ live).2
  have separate := valid.1.2 _ _ _ _ found foundBorrowed different
  have restricted : Ownership.Disjoint allocation.region loan.region := by
    rcases separate with before | after
    · exact Or.inl (Nat.le_trans before subregion.1)
    · exact Or.inr (Nat.le_trans subregion.2 after)
  exact dwordDisjoint_of_regions allocation address loan.region
    (valid.1.1 _ _ found).2.1 fits regionValid restricted

end Footprints

/-- The existing mutex invariant already establishes the lock/payload byte
separation needed to commute a lock exchange past pending payload writes. -/
theorem Invariant.data_lock_separate {config : Mutex.Config} {state : State}
    (valid : Invariant config state) : StoreBuffer.Separate config.dataAddress config.lockAddress := by
  obtain ⟨record, registered, same⟩ := valid.registered
  have mutex := valid.shared.2 record registered
  rw [← same]
  exact Footprints.wordValid_separate valid.shared.1.1 mutex.data mutex.lock mutex.separate.symm

theorem Invariant.data_lock_disjoint {config : Mutex.Config} {state : State}
    (valid : Invariant config state) : DWordDisjoint config.dataAddress config.lockAddress 4 :=
  Footprints.dwordDisjoint_of_separate valid.data_lock_separate

theorem Invariant.lock_data_disjoint {config : Mutex.Config} {state : State}
    (valid : Invariant config state) : DWordDisjoint config.lockAddress config.dataAddress 4 :=
  Footprints.dwordDisjoint_of_separate (StoreBuffer.separate_symm valid.data_lock_separate)

/-- NoReaders excludes the allocation IDs of both reserved words from every
live read loan. Well-formed ownership converts that exclusion to byte framing. -/
theorem Invariant.loan_disjoint {config : Mutex.Config} {state : State}
    (valid : Invariant config state) {loanId : Nat} {loan : Borrowing.Loan}
    (live : state.shared.shared.loans loanId = some loan) :
    DWordDisjoint config.dataAddress loan.region.base loan.region.length ∧
    DWordDisjoint config.lockAddress loan.region.base loan.region.length := by
  obtain ⟨record, registered, same⟩ := valid.registered
  have mutex := valid.shared.2 record registered
  have excluded := mutex.noReaders loanId loan live
  rw [← same]
  exact ⟨Footprints.wordValid_loan_disjoint valid.shared.1 mutex.data live excluded.2.symm,
    Footprints.wordValid_loan_disjoint valid.shared.1 mutex.lock live excluded.1.symm⟩

/-- Read-only authority for code and the return word excludes writes by both
reserved mutex operands. This grants no native code or stack write authority. -/
structure WorkerFootprints (config : Mutex.Config) (worker : Worker) : Prop where
  dataCode : DWordDisjoint config.dataAddress worker.entry.rip bytes.length
  dataStack : DWordDisjoint config.dataAddress (worker.entry.registers .rsp) 8
  lockCode : DWordDisjoint config.lockAddress worker.entry.rip bytes.length
  lockStack : DWordDisjoint config.lockAddress (worker.entry.registers .rsp) 8

theorem WorkerLoanReady.footprints {config : Mutex.Config} {state : State}
    {identifier : Nat} {worker : Worker}
    (ready : WorkerLoanReady state.shared.shared identifier worker)
    (valid : Invariant config state) : WorkerFootprints config worker := by
  obtain ⟨code, codeLive, _, codeRegion⟩ := ready.1
  obtain ⟨stack, stackLive, _, stackRegion⟩ := ready.2.1
  have codeDisjoint := valid.loan_disjoint codeLive
  have stackDisjoint := valid.loan_disjoint stackLive
  rw [codeRegion] at codeDisjoint
  rw [stackRegion] at stackDisjoint
  exact ⟨codeDisjoint.1, stackDisjoint.1, codeDisjoint.2, stackDisjoint.2⟩

theorem WorkerExecutionReady.footprints {config : Mutex.Config} {state : State}
    {identifier : Nat} {worker : Worker}
    (ready : WorkerExecutionReady state.shared.shared identifier worker)
    (valid : Invariant config state) : WorkerFootprints config worker :=
  ready.loans.footprints valid

theorem Invariant.worker_footprints {config : Mutex.Config} {state : State}
    (valid : Invariant config state) (ready : ExecutionReady state)
    {identifier : Nat} {worker : Worker} (live : state.workers[identifier]? = some worker) :
    WorkerFootprints config worker :=
  (ready identifier worker live).footprints valid

/-- An arbitrary queue of protected payload stores preserves every code byte.
The queue-address premise describes the stores issued by the protected
program; all code/data separation comes from the ownership-derived footprint. -/
theorem WorkerFootprints.buffer_agrees_code {config : Mutex.Config} {worker : Worker}
    (footprints : WorkerFootprints config worker) (memory : Memory) (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress) :
    MemoryAgreesOn (StoreBuffer.view memory buffer) memory worker.entry.rip bytes.length := by
  apply StoreBuffer.view_agrees
  intro store member
  rw [payloads store member]
  exact footprints.dataCode

/-- Instruction fetch is unchanged at every byte in the worker's image;
store-buffer overlays retain execute permissions as well as these bytes. -/
theorem WorkerFootprints.buffer_fetch {config : Mutex.Config} {worker : Worker}
    (footprints : WorkerFootprints config worker) (memory : Memory) (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress)
    (offset : Nat) (bound : offset < bytes.length) :
    fetchByte (StoreBuffer.view memory buffer) (worker.entry.rip + BitVec.ofNat 64 offset) =
      fetchByte memory (worker.entry.rip + BitVec.ofNat 64 offset) := by
  unfold fetchByte
  rw [StoreBuffer.view_executable,
    footprints.buffer_agrees_code memory buffer payloads offset bound]

theorem WorkerFootprints.buffer_code {config : Mutex.Config} {worker : Worker}
    (footprints : WorkerFootprints config worker) (memory : Memory) (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress)
    (code : CodeAt memory worker.entry.rip bytes) :
    CodeAt (StoreBuffer.view memory buffer) worker.entry.rip bytes := by
  apply StoreBuffer.view_code _ _ _ _ code
  intro store member
  rw [payloads store member]
  exact footprints.dataCode

/-- The complete eight-byte return read survives any queue of protected stores. -/
theorem WorkerFootprints.buffer_readWord {config : Mutex.Config} {worker : Worker}
    (footprints : WorkerFootprints config worker) (memory : Memory) (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress) :
    readWord (StoreBuffer.view memory buffer) (worker.entry.registers .rsp) =
      readWord memory (worker.entry.registers .rsp) := by
  apply StoreBuffer.view_readWord_frame
  intro store member
  rw [payloads store member]
  exact footprints.dataStack

/-- Initial execution readiness supplies the actual code, and its stored loans
derive the framing needed to retain that code through payload forwarding. -/
theorem Invariant.buffer_code {config : Mutex.Config} {state : State}
    (valid : Invariant config state) (ready : ExecutionReady state)
    {identifier : Nat} {worker : Worker} (live : state.workers[identifier]? = some worker)
    (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress) :
    CodeAt (StoreBuffer.view (toMemory state.shared.shared.resources.space) buffer)
      worker.entry.rip bytes :=
  (valid.worker_footprints ready live).buffer_code _ buffer payloads (ready identifier worker live).code

theorem Invariant.buffer_stack {config : Mutex.Config} {state : State}
    (valid : Invariant config state) (ready : ExecutionReady state)
    {identifier : Nat} {worker : Worker} (live : state.workers[identifier]? = some worker)
    (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress) :
    readWord (StoreBuffer.view (toMemory state.shared.shared.resources.space) buffer)
      (worker.entry.registers .rsp) = .ok worker.returnAddress :=
  ((valid.worker_footprints ready live).buffer_readWord _ buffer payloads).trans
    (ready identifier worker live).stack

/-- Pending payload writes do not forward a value into the separate lock. -/
theorem Invariant.buffer_lock {config : Mutex.Config} {state : State}
    (valid : Invariant config state) (memory : Memory) (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress) :
    loadDWord (StoreBuffer.view memory buffer) config.lockAddress =
      loadDWord memory config.lockAddress := by
  apply StoreBuffer.view_load_frame
  intro store member
  rw [payloads store member]
  exact valid.data_lock_disjoint

/-- Lock publication commutes with every pending payload store using
allocation-derived separation, for arbitrary memory contents and queue length. -/
theorem Invariant.buffer_lock_commute {config : Mutex.Config} {state : State}
    (valid : Invariant config state) (memory : Memory) (buffer : StoreBuffer.Buffer)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress) (value : BitVec 32) :
    StoreBuffer.view (writeDWordUnchecked memory config.lockAddress value) buffer =
      writeDWordUnchecked (StoreBuffer.view memory buffer) config.lockAddress value := by
  apply StoreBuffer.view_write_commute
  intro store member
  rw [payloads store member]
  exact valid.data_lock_separate

/-- Future TSO admission must separately require the aligned ordinary-RAM
profile for payload accesses. The current invariant admits unaligned payloads
and only establishes this predicate for the lock. -/
def PayloadAddressable (config : Mutex.Config) : Prop :=
  atomicAddressable config.dataAddress = true

/-- The existing invariant supplies payload byte addressability, without an
alignment, cache-line, or page-boundary conclusion. -/
theorem Invariant.data_addressable {config : Mutex.Config} {state : State}
    (valid : Invariant config state) : dwordAddressable config.dataAddress = true := by
  obtain ⟨record, registered, same⟩ := valid.registered
  have mutex := valid.shared.2 record registered
  rw [← same]
  exact (Bool.and_eq_true_iff.mp mutex.data.writable).1

end EDSL.OS.MutexReplay
