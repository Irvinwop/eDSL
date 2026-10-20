/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Domain
import EDSL.OS.AtomicSetThreads64.Lifecycle

set_option warningAsError true

namespace EDSL.OS.AtomicSetThreads64.Domain
open X86 AddressSpace

/-- Failures of the actual resource setup retain their checked source. -/
inductive SetupFault where
  | ownership (fault : Ownership.Fault)
  | image (fault : ELF.Error)
  | atomic (fault : Atomics64.Fault)

/-- Allocate and initialize data and caller storage, validate/install the RX
image, adopt its exact extent, and enroll the full64 operand. No worker handle
or loan is installed during setup. Availability is checked by `spawn` later. -/
def setup (bytes : List Byte) (old : Word) : Except SetupFault State := do
  let (data, dataTicket) ← (Ownership.allocate (Ownership.empty AddressSpace.empty)
    0 EDSL.Grading.AtomicLogical64.Domain.dataRegion readWrite).mapError SetupFault.ownership
  let data ← (Ownership.storeWord64 data 0 dataTicket 65536 old).mapError SetupFault.ownership
  let data ← (Ownership.storeWord64 data 0 dataTicket 65544 0x1122334455667788).mapError SetupFault.ownership
  let (caller, stackTicket) ← (Ownership.allocate data 0 EDSL.Grading.AtomicLogical64.Domain.callerRegion readWrite).mapError SetupFault.ownership
  let caller ← (Ownership.storeWord64 caller 0 stackTicket 32768 8192).mapError SetupFault.ownership
  let space ← (EDSL.Grading.AtomicLogical64.Domain.installCandidate bytes caller.space).mapError SetupFault.image
  let (code, _) ← (Ownership.adopt { caller with space := space } 0
    (EDSL.Grading.AtomicLogical64.Domain.codeRegion bytes)).mapError SetupFault.ownership
  let raw := Atomics64.empty (Atomics.empty (Borrowing.empty code))
  let (registered, _) ← (Atomics64.enroll raw 0 dataTicket 65536).mapError SetupFault.atomic
  return empty registered

/-- The loader's enrolled state, before its separate actor-11 issuance/loans. -/
def prepared (bytes : List Byte) (old : Word) : State :=
  empty (EDSL.Grading.AtomicLogical64.Domain.enrolled bytes old)

theorem setup_ok (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) :
    setup bytes old = .ok (prepared bytes old) := by
  simp only [setup, EDSL.Grading.AtomicLogical64.Domain.data_allocated, Except.mapError, ok_bind,
    EDSL.Grading.AtomicLogical64.Domain.data_stored, EDSL.Grading.AtomicLogical64.Domain.neighbor_stored, EDSL.Grading.AtomicLogical64.Domain.caller_allocated,
    EDSL.Grading.AtomicLogical64.Domain.caller_stored,
    EDSL.Grading.AtomicLogical64.Domain.candidate_installed bytes positive bound old]
  have adopted : Ownership.adopt
      { EDSL.Grading.AtomicLogical64.Domain.prior old with
        space := (EDSL.Grading.AtomicLogical64.Domain.loaded bytes old).space }
      0 (EDSL.Grading.AtomicLogical64.Domain.codeRegion bytes) =
      .ok (EDSL.Grading.AtomicLogical64.Domain.owned bytes old, ⟨2, 0⟩) :=
    EDSL.Grading.AtomicLogical64.Domain.code_adopted bytes positive bound old
  rw [adopted]
  simp only [ok_bind]
  change (do
    let registered ← (Atomics64.enroll
      (EDSL.Grading.AtomicLogical64.Domain.raw bytes old) 0 ⟨0, 0⟩ 65536).mapError SetupFault.atomic
    pure (empty registered.1) : Except SetupFault State) = .ok (prepared bytes old)
  rw [EDSL.Grading.AtomicLogical64.Domain.target_enrolled bytes bound old]
  rfl

theorem prepared_valid (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) : WellFormed (prepared bytes old) :=
  empty_wellFormed (EDSL.Grading.AtomicLogical64.Domain.enrolled_valid bytes positive bound old)

theorem prepared_unissued (bytes : List Byte) (old : Word) :
    (prepared bytes old).shared.nextHandle = 0 ∧
    (∀ handle, (prepared bytes old).shared.handles handle = none) ∧
    (prepared bytes old).shared.legacy.shared.nextLoan = 0 ∧
    (∀ loan, (prepared bytes old).shared.legacy.shared.loans loan = none) ∧
    (∀ identifier, (prepared bytes old).workers identifier = none) := by
  exact ⟨rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl⟩

def entry (mask : Word) (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) : Context where
  registers register := match register with
    | .rdi => 65536
    | .rsi => mask
    | .rsp => 32768
    | _ => registers register
  rip := 4096
  flags := flags

def start (bytes : List Byte) (mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) : Start :=
  ⟨entry mask registers flags, bytes, ⟨0⟩, ⟨2, 0⟩, ⟨1, 0⟩⟩

theorem prepared_code (bytes : List Byte) (bound : bytes.length ≤ 4096) (old : Word) :
    CodeAt (toMemory (prepared bytes old).shared.legacy.shared.resources.space) 4096 bytes :=
  EDSL.Grading.AtomicLogical64.Domain.loaded_code bytes bound old

theorem prepared_cell (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) :
    Atomics64.authorizeCell (prepared bytes old).shared 0 ⟨0⟩ =
      .ok ⟨0, ⟨0, 0⟩, 65536⟩ :=
  Atomics64.authorizeCell_success _ _ _ _
    (EDSL.Grading.AtomicLogical64.Domain.enrolled_valid bytes positive bound old) rfl rfl

theorem prepared_code_ready (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) :
    BorrowReady (prepared bytes old).shared ⟨2, 0⟩ (EDSL.Grading.AtomicLogical64.Domain.codeRegion bytes) := by
  refine ⟨⟨0, 0, EDSL.Grading.AtomicLogical64.Domain.codeRegion bytes⟩, rfl,
    EDSL.Grading.AtomicLogical64.Domain.code_region_valid bytes positive bound, ⟨Nat.le_refl _, Nat.le_refl _⟩,
    ?_, rfl, rfl⟩
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨byte, found⟩ := EDSL.Grading.AtomicLogical64.Domain.code_cell bytes old address
    (Ownership.addresses_inside _ (EDSL.Grading.AtomicLogical64.Domain.code_region_valid bytes positive bound) address member)
  change (match (EDSL.Grading.AtomicLogical64.Domain.loaded bytes old).space.cells address with
    | none => false | some cell => cell.permissions.readable) = true
  rw [found]
  rfl

theorem prepared_stack_ready (bytes : List Byte) (bound : bytes.length ≤ 4096) (old : Word) :
    BorrowReady (prepared bytes old).shared ⟨1, 0⟩ EDSL.Grading.AtomicLogical64.Domain.callerRegion := by
  refine ⟨⟨0, 0, EDSL.Grading.AtomicLogical64.Domain.callerRegion⟩, rfl, by decide,
    ⟨Nat.le_refl _, Nat.le_refl _⟩, ?_, rfl, rfl⟩
  apply List.all_eq_true.mpr
  intro address member
  have inside := Ownership.addresses_inside EDSL.Grading.AtomicLogical64.Domain.callerRegion (by decide) address member
  have far : 8192 ≤ address.toNat := by
    change 32768 ≤ address.toNat ∧ address.toNat < 32768 + 8 at inside
    omega
  change (match (EDSL.Grading.AtomicLogical64.Domain.loaded bytes old).space.cells address with
    | none => false | some cell => cell.permissions.readable) = true
  rw [EDSL.Grading.AtomicLogical64.Domain.loaded_far bytes bound old address far]
  dsimp only [EDSL.Grading.AtomicLogical64.Domain.prior, EDSL.Grading.AtomicLogical64.Domain.callerMapped, Ownership.install, writeQWordCells]
  rw [ite_eq_left (show (qwordRegion 32768).Contains address from inside)]
  simp only [mapUnchecked, ite_eq_left inside, Option.map_some]
  rfl

theorem prepared_caller (bytes : List Byte) (bound : bytes.length ≤ 4096) (old : Word) :
    readWord (toMemory (prepared bytes old).shared.legacy.shared.resources.space) 32768 =
      .ok 8192 :=
  EDSL.Grading.AtomicLogical64.Domain.caller_read bytes bound old 0 (fun _ => 0) 0

theorem prepared_old (bytes : List Byte) (bound : bytes.length ≤ 4096) (old : Word) :
    loadQWord (toMemory (prepared bytes old).shared.legacy.shared.resources.space) 65536 =
      .ok old :=
  EDSL.Grading.AtomicLogical64.Domain.old_read bytes bound old 0

/-- A layout is only a supported-syntax certificate. All remaining admission
facts concern the current checked setup, without a desired mathematical task. -/
theorem prepared_ready (bytes : List Byte) (layout : Layout bytes)
    (bound : bytes.length ≤ 4096) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) : SpawnReady (prepared bytes old) (start bytes mask registers flags) := by
  have positive : 0 < bytes.length := by
    rw [layout.exactBytes, bodyBytes_length]
    omega
  exact ⟨layout, prepared_code bytes bound old, _, prepared_cell bytes positive bound old,
    rfl, prepared_code_ready bytes positive bound old, prepared_stack_ready bytes bound old,
    8192, prepared_caller bytes bound old, by decide,
    by change 32768 + 8 < (2 : Nat)^64; decide,
    by change canonical (32768 + 8) = true; decide⟩

/-- The actual spawn installs the entire requested body at the fresh thread
identity. This extracts a checked worker; it does not prescribe its validity. -/
theorem spawned_body (operations : List Sequential.LogicalOp) (old mask : Word)
    (registers : Register → Word) (flags : Word) (result : State × Nat)
    (success : spawn (prepared (bodyBytes operations) old) 0
      (start (bodyBytes operations) mask registers flags) true = .ok result) :
    result.2 = 0 ∧ ∃ worker, result.1.workers 0 = some worker ∧
      worker.operations = operations ∧ worker.bytes = bodyBytes operations ∧
      worker.context = entry mask registers flags ∧ worker.cursor = 0 ∧
      worker.events = [] ∧ worker.phase = .running ∧ worker.rank = operations.length + 1 := by
  obtain ⟨actual, cell, target, code, stack, data, _, _, checked, _, _, _, _, _, _, _, _, _, _, same⟩ :=
    spawn_ok _ _ _ _ _ success
  change checkLayout (bodyBytes operations) = some actual at checked
  rw [checkLayout_bodyBytes] at checked
  cases Option.some.inj checked
  rw [same]
  refine ⟨rfl, ⟨0, (start (bodyBytes operations) mask registers flags).entry,
    (bodyBytes operations), operations, ⟨0⟩, target, data.2, code.2, stack.2,
    (start (bodyBytes operations) mask registers flags).entry, 0, [], .running⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [install, prepared, empty, start]
  · simp [Worker.rank]

/-- Every finite supported body fitting the explicit loader capacity has an
actual resource setup and checked spawn for arbitrary full64 old/mask and
arbitrary caller registers/flags. The installed worker's validity is derived
from that spawn, never assigned as a fixture or assumed in admission. -/
theorem arbitrary_body (operations : List Sequential.LogicalOp)
    (bound : (bodyBytes operations).length ≤ 4096) (old mask : Word)
    (registers : Register → Word := fun _ => 0x123456789abcdef0)
    (flags : Word := 0x202) :
    ∃ result,
      setup (bodyBytes operations) old = .ok (prepared (bodyBytes operations) old) ∧
      SpawnReady (prepared (bodyBytes operations) old)
        (start (bodyBytes operations) mask registers flags) ∧
      spawn (prepared (bodyBytes operations) old) 0
        (start (bodyBytes operations) mask registers flags) true = .ok result ∧
      WellFormed result.1 ∧
      result.1.shared.legacy.shared.resources =
        (prepared (bodyBytes operations) old).shared.legacy.shared.resources ∧
      loadQWord (toMemory result.1.shared.legacy.shared.resources.space) 65536 = .ok old := by
  have positive : 0 < (bodyBytes operations).length := by simp
  have valid := prepared_valid (bodyBytes operations) positive bound old
  have ready := prepared_ready (bodyBytes operations) ⟨operations, rfl⟩ bound old mask registers flags
  obtain ⟨result, spawned, resultValid⟩ := spawn_enabled _ _ true valid ready rfl
  have resources := spawn_resources _ _ _ _ _ spawned
  refine ⟨result, setup_ok _ positive bound old, ready, spawned, resultValid, resources, ?_⟩
  rw [resources]
  exact prepared_old _ bound old

/-- An explicit mixed supported body exercises all three strict logical
encodings. The initial word and mask both use the high half of the qword. -/
def mixedOperations : List Sequential.LogicalOp := [.band, .bor, .bxor]

theorem mixed_bytes : bodyBytes mixedOperations =
    [0xf0, 0x48, 0x21, 0x37, 0xf0, 0x48, 0x09, 0x37,
      0xf0, 0x48, 0x31, 0x37, 0xc3] := rfl

/-- Concrete nonvacuity of the checked mixed-body setup and creation. This
witness states current RAM and actual installed syntax, without identifying a
compound call with one atomic abstract operation. -/
theorem mixed_body : ∃ result worker,
    setup (bodyBytes mixedOperations) 0x8000000000000001 =
      .ok (prepared (bodyBytes mixedOperations) 0x8000000000000001) ∧
    spawn (prepared (bodyBytes mixedOperations) 0x8000000000000001) 0
      (start (bodyBytes mixedOperations) 0x8000000000000000) true = .ok result ∧
    WellFormed result.1 ∧ result.2 = 0 ∧ result.1.workers 0 = some worker ∧
    WorkerValid result.1.shared 0 worker ∧ worker.operations = [.band, .bor, .bxor] ∧
    worker.phase = .running ∧ worker.rank = 4 ∧
    loadQWord (toMemory result.1.shared.legacy.shared.resources.space) 65536 =
      .ok 0x8000000000000001 := by
  obtain ⟨result, installed, _, spawned, valid, _, read⟩ :=
    arbitrary_body mixedOperations (by decide) 0x8000000000000001 0x8000000000000000
  obtain ⟨identifier, worker, live, operations, _, _, _, _, running, rank⟩ :=
    spawned_body _ _ _ _ _ _ spawned
  exact ⟨result, worker, installed, spawned, valid, identifier, live,
    (valid.2 0 worker live).2, operations, running, rank, read⟩

/-- Observable data from a checked mixed-body execution and collection. -/
structure MixedObservation where
  labels : List (Option Atomics64.Event)
  current : Option Word
  caller : Word
  stackPointer : Word
  workerGone : Bool
  handleGone : Bool
  codeLoanGone : Bool
  stackLoanGone : Bool

/-- Concrete selections use the actual current-memory machine/OS dispatcher,
including its no-change OR event, the real RET, and checked collection. -/
def executeMixed (state : State) : Except Fault MixedObservation := do
  let (created, identifier) ← spawn state 0 (start (bodyBytes mixedOperations) 0x8000000000000000)
  let (one, andEvent) ← dispatch created identifier false
  let (two, orEvent) ← dispatch one identifier true
  let (three, xorEvent) ← dispatch two identifier false
  let (done, retEvent) ← dispatch three identifier true
  let (joined, context) ← join done 0 identifier
  return ⟨[andEvent, orEvent, xorEvent, retEvent],
    (loadQWord (toMemory joined.shared.legacy.shared.resources.space) 65536).toOption,
    context.rip, context.registers .rsp, (joined.workers identifier).isNone,
    (joined.shared.handles ⟨0⟩).isNone, (joined.shared.legacy.shared.loans 0).isNone,
    (joined.shared.legacy.shared.loans 1).isNone⟩

/-- Literal full64 event/value and return oracles for the actual checked
setup→spawn→AND→OR→XOR→RET→join path. Collection removes the handle/two loans;
the cell remains registered and its current word is read after collection. -/
theorem mixed_execution : (do
    let state ← (setup (bodyBytes mixedOperations) 0x8000000000000001).mapError Sum.inl
    (executeMixed state).mapError Sum.inr : Except (Sum SetupFault Fault) MixedObservation) =
    .ok ⟨[
      some ⟨1, ⟨0⟩, ⟨0⟩, ⟨.band, 0x8000000000000000,
        ⟨65536, 0x8000000000000001, 0x8000000000000000⟩⟩⟩,
      some ⟨1, ⟨0⟩, ⟨0⟩, ⟨.bor, 0x8000000000000000,
        ⟨65536, 0x8000000000000000, 0x8000000000000000⟩⟩⟩,
      some ⟨1, ⟨0⟩, ⟨0⟩, ⟨.bxor, 0x8000000000000000,
        ⟨65536, 0x8000000000000000, 0⟩⟩⟩,
      none], some 0, 8192, 32776, true, true, true, true⟩ := by
  rw [setup_ok _ (by decide) (by decide)]
  rfl

end EDSL.OS.AtomicSetThreads64.Domain
