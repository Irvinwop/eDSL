/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicLogical64.Contract
import EDSL.ELF.Loader
import EDSL.X86.StackRead64

set_option warningAsError true

namespace EDSL.Grading.AtomicLogical64.Domain
open EDSL EDSL.X86 EDSL.OS EDSL.OS.AddressSpace EDSL.AtomicLogical64

def codeRegion (candidate : List Byte) : Region := ⟨4096, candidate.length⟩
def callerRegion : Region := ⟨32768, 8⟩
def dataRegion : Region := ⟨65536, 16⟩

/-- One data allocation contains the operand and an adjacent frame sentinel. -/
def dataMapped : Ownership.World :=
  Ownership.install (Ownership.empty empty) (mapUnchecked empty dataRegion readWrite) 0 dataRegion

theorem data_allocated : Ownership.allocate (Ownership.empty empty) 0 dataRegion readWrite =
    .ok (dataMapped, ⟨0, 0⟩) :=
  Ownership.allocate_success _ _ _ _ (Ownership.empty_wellFormed _) (by decide)
    (by decide) (by decide)

theorem data_valid : Ownership.WellFormed dataMapped :=
  (Ownership.allocate_wellFormed _ _ _ _ _ (Ownership.empty_wellFormed _) data_allocated).1

def dataStored (old : Word) : Ownership.World :=
  { dataMapped with space := writeQWordCells dataMapped.space 65536 old }

theorem data_stored (old : Word) :
    Ownership.storeWord64 dataMapped 0 ⟨0, 0⟩ 65536 old = .ok (dataStored old) :=
  Ownership.storeWord64_success _ _ _ _ _ ⟨0, 0, dataRegion⟩ rfl (by decide) (by decide)

theorem stored_valid (old : Word) : Ownership.WellFormed (dataStored old) :=
  (Ownership.storeWord64_wellFormed _ _ _ _ _ _ data_valid (data_stored old)).1

def neighborStored (old : Word) : Ownership.World :=
  { dataStored old with space := writeQWordCells (dataStored old).space 65544 0x1122334455667788 }

theorem neighbor_stored (old : Word) : Ownership.storeWord64 (dataStored old) 0 ⟨0, 0⟩
    65544 0x1122334455667788 = .ok (neighborStored old) :=
  Ownership.storeWord64_success _ _ _ _ _ ⟨0, 0, dataRegion⟩ rfl (by decide) rfl

theorem neighbor_valid (old : Word) : Ownership.WellFormed (neighborStored old) :=
  (Ownership.storeWord64_wellFormed _ _ _ _ _ _ (stored_valid old) (neighbor_stored old)).1

def callerMapped (old : Word) : Ownership.World :=
  Ownership.install (neighborStored old)
    (mapUnchecked (neighborStored old).space callerRegion readWrite) 0 callerRegion

theorem caller_allocated (old : Word) :
    Ownership.allocate (neighborStored old) 0 callerRegion readWrite =
      .ok (callerMapped old, ⟨1, 0⟩) :=
  Ownership.allocate_success _ _ _ _ (neighbor_valid old) (by decide) (by decide) rfl

theorem mapped_valid (old : Word) : Ownership.WellFormed (callerMapped old) :=
  (Ownership.allocate_wellFormed _ _ _ _ _ (neighbor_valid old) (caller_allocated old)).1

def prior (old : Word) : Ownership.World :=
  { callerMapped old with space := writeQWordCells (callerMapped old).space 32768 8192 }

theorem caller_stored (old : Word) :
    Ownership.storeWord64 (callerMapped old) 0 ⟨1, 0⟩ 32768 8192 = .ok (prior old) :=
  Ownership.storeWord64_success _ _ _ _ _ ⟨0, 0, callerRegion⟩ rfl (by decide) rfl

theorem prior_valid (old : Word) : Ownership.WellFormed (prior old) :=
  (Ownership.storeWord64_wellFormed _ _ _ _ _ _ (mapped_valid old) (caller_stored old)).1

/-- A raw-byte installation plan, not parsed ELF metadata. The existing segment
installer gives every candidate byte its final RX permissions. No instruction
decoder, return search or future execution participates in this plan. -/
def segment (candidate : List Byte) : ELF.Segment :=
  ⟨0, 4096, candidate.length, candidate.length, 5, 1⟩

def image (candidate : List Byte) : ELF.Image := ⟨4096, [segment candidate]⟩

theorem image_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) : ELF.valid candidate (image candidate) = true := by
  simp [ELF.valid, image, segment, ELF.Segment.valid, ELF.Segment.executable,
    ELF.maxSegmentSize, ELF.pageSize]
  omega

theorem code_region_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) : (codeRegion candidate).valid = true := by
  change decide (0 < candidate.length ∧ 4096 + candidate.length ≤ 2^64 ∧
    (4096 + candidate.length ≤ 2^47 ∨ 2^64 - 2^47 ≤ 4096)) = true
  exact decide_eq_true (by omega)

theorem code_pages (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) :
    (segment candidate).pageRegion = (⟨4096, 4096⟩ : Region) := by
  simp only [segment, ELF.Segment.pageRegion, ELF.Segment.pageStart,
    ELF.Segment.pageEnd, ELF.pageSize, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub]
  change (⟨4096, (4096 + candidate.length + 4095) / 4096 * 4096 - 4096⟩ : Region) = _
  have size : (4096 + candidate.length + 4095) / 4096 * 4096 - 4096 = 4096 := by omega
  rw [size]

theorem segment_permissions (candidate : List Byte) :
    (segment candidate).permissions = readExecute := by
  simp [segment, ELF.Segment.permissions, ELF.Segment.writable, ELF.Segment.executable,
    readExecute]

/-- Freshness is proved by an interval, rather than enumerating a page. -/
theorem image_fresh (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    ELF.fresh (image candidate) (prior old).space = true := by
  simp only [ELF.fresh, image, List.all_cons, List.all_nil, Bool.and_true]
  rw [code_pages candidate positive bound]
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside (⟨4096, 4096⟩ : Region) (by decide) address member
  have dataOut : ¬dataRegion.Contains address := by
    change ¬(65536 ≤ address.toNat ∧ address.toNat < 65536 + 16)
    change 4096 ≤ address.toNat ∧ address.toNat < 4096 + 4096 at inside
    omega
  have callerOut : ¬callerRegion.Contains address := by
    change ¬(32768 ≤ address.toNat ∧ address.toNat < 32768 + 8)
    change 4096 ≤ address.toNat ∧ address.toNat < 4096 + 4096 at inside
    omega
  have targetOut : ¬(qwordRegion 65536).Contains address := by
    change ¬(65536 ≤ address.toNat ∧ address.toNat < 65536 + 8)
    change 4096 ≤ address.toNat ∧ address.toNat < 4096 + 4096 at inside
    omega
  have neighborOut : ¬(qwordRegion 65544).Contains address := by
    change ¬(65544 ≤ address.toNat ∧ address.toNat < 65544 + 8)
    change 4096 ≤ address.toNat ∧ address.toNat < 4096 + 4096 at inside
    omega
  suffices absent : (prior old).space.cells address = none by simp [absent]
  simp only [prior, callerMapped, neighborStored, dataStored, dataMapped, Ownership.install]
  rw [writeQWord_frame _ _ _ _ callerOut, map_frame _ _ _ _ callerOut,
    writeQWord_frame _ _ _ _ neighborOut, writeQWord_frame _ _ _ _ targetOut,
    map_frame _ _ _ _ dataOut]
  rfl

/-- Checked raw installation uses the segment validator and page-freshness
gate. The bound below is the existing byte-window resource limit. -/
def installCandidate (candidate : List Byte) (space : Space) : Except ELF.Error Space := do
  if !ELF.valid candidate (image candidate) then throw .invalidImage
  if !ELF.fresh (image candidate) space then throw .mappingCollision
  return ELF.install candidate (image candidate) space

def loaded (candidate : List Byte) (old : Word) : Ownership.World :=
  { prior old with space := ELF.install candidate (image candidate) (prior old).space }

theorem candidate_installed (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    installCandidate candidate (prior old).space = .ok (loaded candidate old).space := by
  simp [installCandidate, image_valid candidate positive bound,
    image_fresh candidate positive bound old, loaded]

theorem loaded_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    Ownership.WellFormed (loaded candidate old) := by
  apply Ownership.changeSpace_wellFormed _ _ (prior_valid old)
  intro identifier allocation live address inside
  obtain ⟨cell, found⟩ := (prior_valid old).1 identifier allocation live |>.2.2 address inside
  exact ⟨cell, ELF.install_preserves_existing candidate (image candidate) (prior old).space
    (image_valid candidate positive bound) (image_fresh candidate positive bound old) address cell found⟩

theorem code_cell (candidate : List Byte) (old : Word) (address : Word)
    (inside : (codeRegion candidate).Contains address) :
    ∃ byte, (loaded candidate old).space.cells address = some ⟨byte, readExecute⟩ := by
  have index : address.toNat - 4096 < candidate.length := by
    change 4096 ≤ address.toNat ∧ address.toNat < 4096 + candidate.length at inside
    omega
  have present : (candidate[address.toNat - 4096]?).isSome = true := by simpa using index
  obtain ⟨byte, found⟩ := Option.isSome_iff_exists.mp present
  have selected : ELF.segmentAt (image candidate) address.toNat = some (segment candidate) := by
    simp [ELF.segmentAt, image, show (segment candidate).Contains address.toNat from inside]
  refine ⟨byte, ?_⟩
  simpa only [loaded, segment_permissions] using ELF.install_file_byte candidate (image candidate)
    (prior old).space (segment candidate) address byte selected index (by simpa [segment] using found)

theorem loaded_far (candidate : List Byte) (bound : candidate.length ≤ 4096)
    (old : Word) (address : Word) (far : 8192 ≤ address.toNat) :
    (loaded candidate old).space.cells address = (prior old).space.cells address := by
  apply ELF.install_outside
  intro selected member
  have same := List.mem_singleton.mp member
  subst selected
  change ¬(4096 ≤ address.toNat ∧ address.toNat < 4096 + candidate.length)
  omega

def owned (candidate : List Byte) (old : Word) : Ownership.World :=
  Ownership.install (loaded candidate old) (loaded candidate old).space 0 (codeRegion candidate)

theorem code_adopted (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    Ownership.adopt (loaded candidate old) 0 (codeRegion candidate) =
      .ok (owned candidate old, ⟨2, 0⟩) := by
  have mapped : allMapped (loaded candidate old).space (codeRegion candidate) = true := by
    apply Ownership.mapped_of_inside _ _ (code_region_valid candidate positive bound)
    intro address inside
    obtain ⟨byte, found⟩ := code_cell candidate old address inside
    exact ⟨_, found⟩
  have free : Ownership.unclaimed (loaded candidate old) (codeRegion candidate) = true := by
    apply List.all_eq_true.mpr
    intro identifier member
    have below : identifier < 2 := List.mem_range.mp member
    have choices : identifier = 0 ∨ identifier = 1 := by omega
    rcases choices with rfl | rfl
    · change decide (4096 + candidate.length ≤ 65536 ∨ 65536 + 16 ≤ 4096) = true
      exact decide_eq_true (by omega)
    · change decide (4096 + candidate.length ≤ 32768 ∨ 32768 + 8 ≤ 4096) = true
      exact decide_eq_true (by omega)
  exact Ownership.adopt_success _ _ _ (loaded_valid candidate positive bound old)
    (code_region_valid candidate positive bound) mapped free

theorem owned_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    Ownership.WellFormed (owned candidate old) :=
  (Ownership.adopt_wellFormed _ _ _ _ (loaded_valid candidate positive bound old)
    (code_adopted candidate positive bound old)).1

def raw (candidate : List Byte) (old : Word) : Shared :=
  Atomics64.empty (Atomics.empty (Borrowing.empty (owned candidate old)))

theorem raw_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) : Atomics64.WellFormed (raw candidate old) :=
  Atomics64.empty_wellFormed _ (Atomics.empty_wellFormed _
    (Borrowing.empty_wellFormed _ (owned_valid candidate positive bound old)))

def enrolled (candidate : List Byte) (old : Word) : Shared :=
  Atomics64.installCell (raw candidate old) ⟨0, ⟨0, 0⟩, 65536⟩

theorem target_enrolled (candidate : List Byte) (bound : candidate.length ≤ 4096) (old : Word) :
    Atomics64.enroll (raw candidate old) 0 ⟨0, 0⟩ 65536 = .ok (enrolled candidate old, ⟨0⟩) := by
  have outside (address : Word) (far : 8192 ≤ address.toNat) :
      ELF.segmentAt (image candidate) address.toNat = none := by
    have absent : ¬(segment candidate).Contains address.toNat := by
      change ¬(4096 ≤ address.toNat ∧ address.toNat < 4096 + candidate.length)
      omega
    simp [ELF.segmentAt, image, absent]
  have c0 := outside 65536 (by decide)
  have c1 := outside 65537 (by decide)
  have c2 := outside 65538 (by decide)
  have c3 := outside 65539 (by decide)
  have c4 := outside 65540 (by decide)
  have c5 := outside 65541 (by decide)
  have c6 := outside 65542 (by decide)
  have c7 := outside 65543 (by decide)
  change ELF.segmentAt (image candidate) 65536 = none at c0
  change ELF.segmentAt (image candidate) 65537 = none at c1
  change ELF.segmentAt (image candidate) 65538 = none at c2
  change ELF.segmentAt (image candidate) 65539 = none at c3
  change ELF.segmentAt (image candidate) 65540 = none at c4
  change ELF.segmentAt (image candidate) 65541 = none at c5
  change ELF.segmentAt (image candidate) 65542 = none at c6
  change ELF.segmentAt (image candidate) 65543 = none at c7
  simp [Atomics64.enroll, Atomics64.validateCell, raw, owned, loaded, ELF.install,
    c0, c1, c2, c3, c4, c5, c6, c7, enrolled, Atomics64.reserved,
    Atomics64.empty, Atomics.empty, Borrowing.empty, Borrowing.allowed,
    Ownership.authorize, Ownership.install, prior, callerMapped, neighborStored,
    dataStored, dataMapped, Ownership.empty, Ownership.containsQWord, dataRegion,
    atomicAddressable64, canStoreQWord, qwordAddressable, qwordWritable, dataOnly64,
    toMemory, writeQWordCells, qwordRegion, mapUnchecked, callerRegion, Region.Contains,
    readWrite, canonical, Atomics.reserved, Except.mapError]

theorem enrolled_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) : Atomics64.WellFormed (enrolled candidate old) :=
  (Atomics64.enroll_wellFormed _ _ _ _ _ (raw_valid candidate positive bound old)
    (target_enrolled candidate bound old)).1

def issued (candidate : List Byte) (old : Word) : Shared :=
  Atomics64.installHandle (enrolled candidate old) ⟨11, ⟨0⟩⟩

theorem handle_issued (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    Atomics64.issue (enrolled candidate old) 0 ⟨0⟩ 11 = .ok (issued candidate old, ⟨0⟩) :=
  Atomics64.issue_success _ _ _ _ _ (enrolled_valid candidate positive bound old) rfl rfl

theorem issued_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) : Atomics64.WellFormed (issued candidate old) :=
  (Atomics64.issue_wellFormed _ _ _ _ _ (enrolled_valid candidate positive bound old)
    (handle_issued candidate positive bound old)).1

def withCode (candidate : List Byte) (old : Word) : Shared :=
  { issued candidate old with legacy := { (issued candidate old).legacy with shared :=
    (Borrowing.installLoan (issued candidate old).legacy.shared
      ⟨⟨2, 0⟩, 0, 11, codeRegion candidate⟩) } }

theorem code_borrowed (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    Atomics64.readBorrow (issued candidate old) 0 ⟨2, 0⟩ 11 (codeRegion candidate) =
      .ok (withCode candidate old, 0) := by
  have readable : Borrowing.allReadable (issued candidate old).legacy.shared.resources.space
      (codeRegion candidate) = true := by
    apply List.all_eq_true.mpr
    intro address member
    obtain ⟨byte, found⟩ := code_cell candidate old address
      (Ownership.addresses_inside _ (code_region_valid candidate positive bound) address member)
    change (match (loaded candidate old).space.cells address with
      | none => false | some cell => cell.permissions.readable) = true
    rw [found]
    rfl
  have borrowed := Borrowing.readBorrow_success (issued candidate old).legacy.shared 0 ⟨2, 0⟩
    11 (codeRegion candidate) ⟨0, 0, codeRegion candidate⟩
    (issued_valid candidate positive bound old).legacy.shared rfl
    (code_region_valid candidate positive bound) ⟨Nat.le_refl _, Nat.le_refl _⟩ readable
  have free : Atomics64.reserved (issued candidate old) 2 = false := rfl
  have legacyFree : Atomics.reserved (issued candidate old).legacy 2 = false := rfl
  simp only [Atomics64.readBorrow, free, Bool.false_eq_true, ↓reduceIte,
    Atomics.readBorrow, legacyFree, borrowed, Except.mapError, ok_bind]
  rfl

theorem code_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) : Atomics64.WellFormed (withCode candidate old) :=
  Atomics64.readBorrow_wellFormed _ _ _ _ _ _ (issued_valid candidate positive bound old)
    (code_borrowed candidate positive bound old)

def shared (candidate : List Byte) (old : Word) : Shared :=
  { withCode candidate old with legacy := { (withCode candidate old).legacy with shared :=
    (Borrowing.installLoan (withCode candidate old).legacy.shared
      ⟨⟨1, 0⟩, 0, 11, callerRegion⟩) } }

theorem caller_borrowed (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) :
    Atomics64.readBorrow (withCode candidate old) 0 ⟨1, 0⟩ 11 callerRegion =
      .ok (shared candidate old, 1) := by
  have readable : Borrowing.allReadable (withCode candidate old).legacy.shared.resources.space
      callerRegion = true := by
    apply List.all_eq_true.mpr
    intro address member
    have inside := Ownership.addresses_inside callerRegion (by decide) address member
    have far : 8192 ≤ address.toNat := by
      change 32768 ≤ address.toNat ∧ address.toNat < 32768 + 8 at inside
      omega
    change (match (loaded candidate old).space.cells address with
      | none => false | some cell => cell.permissions.readable) = true
    rw [loaded_far candidate bound old address far]
    dsimp only [prior, callerMapped, Ownership.install, writeQWordCells]
    rw [ite_eq_left (show (qwordRegion 32768).Contains address from inside)]
    simp only [mapUnchecked, ite_eq_left inside, Option.map_some]
    rfl
  have borrowed := Borrowing.readBorrow_success (withCode candidate old).legacy.shared 0 ⟨1, 0⟩
    11 callerRegion ⟨0, 0, callerRegion⟩ (code_valid candidate positive bound old).legacy.shared
    rfl (by decide) ⟨Nat.le_refl _, Nat.le_refl _⟩ readable
  have free : Atomics64.reserved (withCode candidate old) 1 = false := rfl
  have legacyFree : Atomics.reserved (withCode candidate old).legacy 1 = false := rfl
  simp only [Atomics64.readBorrow, free, Bool.false_eq_true, ↓reduceIte,
    Atomics.readBorrow, legacyFree, borrowed, Except.mapError, ok_bind]
  rfl

theorem shared_valid (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old : Word) : Atomics64.WellFormed (shared candidate old) :=
  Atomics64.readBorrow_wellFormed _ _ _ _ _ _ (code_valid candidate positive bound old)
    (caller_borrowed candidate positive bound old)

def input : Input := ⟨11, ⟨0⟩, 0, 1, 8192⟩

def initial (candidate : List Byte) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) : X86.State where
  registers register := match register with
    | .rdi => 65536
    | .rsi => mask
    | .rsp => 32768
    | _ => registers register
  rip := 4096
  flags := flags
  memory := toMemory (shared candidate old).legacy.shared.resources.space

/-- Installation preserves every caller/target cell, including permissions. -/
theorem memory_agrees_far (candidate : List Byte) (bound : candidate.length ≤ 4096)
    (old : Word) (base : Word) (length : Nat) (far : 8192 ≤ base.toNat)
    (span : base.toNat + length ≤ 2^64) :
    MemoryAgreesOn (toMemory (loaded candidate old).space) (toMemory (prior old).space)
      base length := by
  intro offset inside
  have small : offset < 2^64 := by omega
  have total : base.toNat + offset < 2^64 := by omega
  have natural : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt total]
  exact (toMemory_agrees_at _ _ _
    (loaded_far candidate bound old _ (by rw [natural]; omega))).1

theorem caller_read (candidate : List Byte) (bound : candidate.length ≤ 4096)
    (old mask : Word) (registers : Register → Word) (flags : Word) :
    readWord (initial candidate old mask registers flags).memory 32768 = .ok 8192 := by
  have stored := Ownership.storeWord64_sound _ _ _ _ _ _ (caller_stored old)
  have read : readWord (toMemory (prior old).space) 32768 = .ok 8192 :=
    readWord_of_loadQWord _ _ _ stored.2.2.2.2.1
  exact (readWord_congr _ _ _
    (memory_agrees_far candidate bound old 32768 8 (by decide) (by decide))).trans read

theorem resources (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) :
    Resources candidate input (shared candidate old) (initial candidate old mask registers flags) := by
  have authority := Atomics64.authorize_success (shared candidate old) 11 ⟨0⟩
    ⟨11, ⟨0⟩⟩ ⟨0, ⟨0, 0⟩, 65536⟩ (shared_valid candidate positive bound old) rfl rfl rfl
  exact ⟨shared_valid candidate positive bound old, ⟨_, _, authority, rfl⟩, rfl,
    ⟨⟨⟨2, 0⟩, 0, 11, codeRegion candidate⟩, rfl, rfl, rfl⟩,
    ⟨⟨⟨1, 0⟩, 0, 11, callerRegion⟩, rfl, rfl, rfl⟩,
    caller_read candidate bound old mask registers flags, by decide,
    by change 32768 + 8 < (2 : Nat)^64; decide,
    by change canonical (32768 + 8) = true; decide⟩

/-- All selected bytes, including the final byte of an arbitrary symbolic
span, are actually fetchable. There is no opcode or execution premise. -/
theorem loaded_code (candidate : List Byte) (bound : candidate.length ≤ 4096) (old : Word) :
    CodeAt (toMemory (loaded candidate old).space) 4096 candidate := by
  refine ⟨by change 4096 + candidate.length ≤ 2^64; omega, ?_⟩
  intro offset byte present
  have inside : offset < candidate.length := by
    have someAt : candidate[offset]?.isSome = true := by simp [present]
    simpa using someAt
  have small : offset < 2^64 := by omega
  have total : 4096 + offset < 2^64 := by omega
  have natural : ((4096 : Word) + BitVec.ofNat 64 offset).toNat = 4096 + offset := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt total]
  have selected : ELF.segmentAt (image candidate) (4096 + offset) = some (segment candidate) := by
    have contained : (segment candidate).Contains (4096 + offset) := by
      change 4096 ≤ 4096 + offset ∧ 4096 + offset < 4096 + candidate.length
      omega
    simp [ELF.segmentAt, image, contained]
  have cell : (loaded candidate old).space.cells (4096 + BitVec.ofNat 64 offset) =
      some ⟨byte, readExecute⟩ := by
    rw [← segment_permissions candidate]
    apply ELF.install_file_byte candidate (image candidate) (prior old).space (segment candidate)
    · rw [natural]; exact selected
    · simp only [segment, natural, Nat.add_sub_cancel_left]; exact inside
    · simpa only [segment, natural, Nat.add_sub_cancel_left, Nat.zero_add] using present
  have canonicalAt : canonical ((4096 : Word) + BitVec.ofNat 64 offset) = true := by
    simp only [canonical, natural, decide_eq_true_eq]
    exact Or.inl (by omega)
  change fetchByte (toMemory (loaded candidate old).space) (4096 + BitVec.ofNat 64 offset) = .ok byte
  have current : (toMemory (loaded candidate old).space).read
      (4096 + BitVec.ofNat 64 offset) = some byte := by
    dsimp only [toMemory]; rw [cell]; rfl
  have executable : (toMemory (loaded candidate old).space).executable
      (4096 + BitVec.ofNat 64 offset) = true := by
    dsimp only [toMemory]; rw [cell]; rfl
  rw [fetchByte, canonicalAt, executable]
  change (match (toMemory (loaded candidate old).space).read (4096 + BitVec.ofNat 64 offset) with
    | some value => Except.ok value
    | none => Except.error (Error.inaccessibleInstruction _)) = .ok byte
  rw [current]

/-- Public admission for every nonempty bounded byte list and every symbolic
old/mask pair. All authority and initialized bytes come from checked setup. -/
theorem resource_pre (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) :
    Pre candidate input (shared candidate old) (initial candidate old mask registers flags) :=
  ⟨resources candidate positive bound old mask registers flags, loaded_code candidate bound old⟩

theorem old_read (candidate : List Byte) (bound : candidate.length ≤ 4096) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) :
    loadQWord (initial candidate old mask registers flags).memory
      ((initial candidate old mask registers flags).registers .rdi) = .ok old := by
  change loadQWord (toMemory (loaded candidate old).space) 65536 = .ok old
  rw [loadQWord_congr _ (toMemory (prior old).space) _
    (memory_agrees_far candidate bound old 65536 8 (by decide) (by decide))]
  change Except.ok (joinQWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8) (old.extractLsb' 32 8)
    (old.extractLsb' 40 8) (old.extractLsb' 48 8) (old.extractLsb' 56 8)) = .ok old
  rw [qword_join_extracts]

theorem arbitrary_current (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) :
    Resources candidate input (shared candidate old) (initial candidate old mask registers flags) ∧
      Pre candidate input (shared candidate old) (initial candidate old mask registers flags) ∧
      loadQWord (initial candidate old mask registers flags).memory
        ((initial candidate old mask registers flags).registers .rdi) = .ok old ∧
      (initial candidate old mask registers flags).registers .rsi = mask :=
  ⟨resources candidate positive bound old mask registers flags,
    resource_pre candidate positive bound old mask registers flags,
    old_read candidate bound old mask registers flags, rfl⟩

/-- Usefulness is a separate input fact and never restricts Pre. -/
def Useful (old mask : Word) : Prop :=
  ∃ index : Fin 64, ¬Logical64.HasBit old index ∧ Logical64.HasBit mask index

theorem highbit_useful : Useful 0 0x8000000000000000 :=
  ⟨⟨63, by decide⟩, by change ¬Nat.testBit 0 63; decide,
    by change Nat.testBit 0x8000000000000000 63; decide⟩

theorem useful_current (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) :
    ∃ old mask shared initial,
      Pre candidate input shared initial ∧
      loadQWord initial.memory (initial.registers .rdi) = .ok old ∧
      initial.registers .rsi = mask ∧ Useful old mask :=
  ⟨0, 0x8000000000000000, shared candidate 0, initial candidate 0 0x8000000000000000,
    resource_pre candidate positive bound _ _, old_read candidate bound _ _, rfl, highbit_useful⟩

end EDSL.Grading.AtomicLogical64.Domain
