/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Cohort
import EDSL.OS.MutexReplay.Preservation

namespace EDSL.Examples.MutexWorkers
open X86 OS OS.AddressSpace OS.MutexReplay

/-- Independently assembled from fixtures/mutex-worker.S, including its RET.
This fixture does not take its bytes from the replay model's expected code. -/
def fixture : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x87, 0x07, 0x83, 0xf8, 0, 0x75, 0xf4,
   0x8b, 0x06, 0x8d, 0x40, 1, 0x89, 0x06, 0x8d, 0x40, 1, 0x89, 0x06,
   0xb8, 0, 0, 0, 0, 0x87, 0x07, 0xb8, 0, 0, 0, 0, 0xc3]

/-- Loader code, a read-only caller return stack, lock, payload, and adjacent
sentinel. All payload bits are supplied by the caller, including wraparound. -/
def seed (old : BitVec 32) : Space where
  cells address :=
    if 4194304 ≤ address.toNat ∧ address.toNat < 4194341 then
      (fixture[address.toNat - 4194304]?).map fun byte => ⟨byte, readExecute⟩
    else match address.toNat with
      | 32769 => some ⟨0x20, readOnly⟩
      | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readOnly⟩
      | 65536 | 65537 | 65538 | 65539 => some ⟨0, readWrite⟩
      | 131072 => some ⟨old.extractLsb' 0 8, readWrite⟩
      | 131073 => some ⟨old.extractLsb' 8 8, readWrite⟩
      | 131074 => some ⟨old.extractLsb' 16 8, readWrite⟩
      | 131075 => some ⟨old.extractLsb' 24 8, readWrite⟩
      | 131076 => some ⟨0xd8, readWrite⟩ | 131077 => some ⟨0xc7, readWrite⟩
      | 131078 => some ⟨0xb6, readWrite⟩ | 131079 => some ⟨0xa5, readWrite⟩
      | _ => none

def entry : Context where
  registers register := if register = .rdi then 65536 else if register = .rsi then 131072
    else if register = .rsp then 32768 else 0xfeedface89abcdef
  rip := 4194304
  flags := 0x8d7

def configuration (predicate : BitVec 32 → Bool) : Mutex.Config :=
  ⟨0, ⟨0, 0⟩, 65536, ⟨1, 0⟩, 131072, predicate⟩

def unrestricted : BitVec 32 → Bool := fun _ => true
def even : BitVec 32 → Bool := fun value => !value.getLsbD 0

def withTicket (state : Mutex.State) (operation : Ownership.Mutation) :
    Except MutexReplay.Fault (Mutex.State × Ownership.Ticket) := do
  let (after, result) ← (Mutex.mutate state operation).mapError MutexReplay.Fault.protocol
  let some ticket := result | throw .invalidContext
  pure (after, ticket)

/-- Every allocation and registration goes through the checked OS API.
The fixed lock/data ticket identities are validated again by registration. -/
def setupIn (space : Space) (predicate : BitVec 32 → Bool) :
    Except MutexReplay.Fault (MutexReplay.State × Start) := do
  let initial := Mutex.empty (Borrowing.empty (Ownership.empty space))
  let (lock, _) ← withTicket initial (.adopt 0 ⟨65536, 4⟩)
  let (data, _) ← withTicket lock (.adopt 0 ⟨131072, 8⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4194304, 37⟩)
  let (stack, stackTicket) ← withTicket code (.adopt 0 ⟨32768, 8⟩)
  let registered ← (Mutex.register stack (configuration predicate)).mapError MutexReplay.Fault.protocol
  pure (MutexReplay.empty registered, ⟨entry, codeTicket, stackTicket⟩)

theorem withTicket_ok (state : Mutex.State) (operation : Ownership.Mutation)
    (result : Mutex.State × Ownership.Ticket) (success : withTicket state operation = .ok result) :
    Mutex.mutate state operation = .ok (result.1, some result.2) := by
  cases changed : Mutex.mutate state operation with
  | error fault => simp [withTicket, changed, Except.mapError] at success
  | ok output =>
    rcases output with ⟨after, ticket⟩
    cases ticket with
    | none => simp [withTicket, changed, Except.mapError] at success
    | some issued =>
      simp [withTicket, changed, Except.mapError] at success
      cases success
      rfl

/-- Invert real setup success and establish well-formedness from the empty
ownership world, four checked mutations, and checked registration. -/
theorem setupIn_valid (space : Space) (predicate : BitVec 32 → Bool)
    (result : MutexReplay.State × Start) (success : setupIn space predicate = .ok result) :
    Invariant (configuration predicate) result.1 ∧ result.1.workers = [] := by
  have initialValid : Mutex.WellFormed (Mutex.empty (Borrowing.empty (Ownership.empty space))) :=
    Mutex.empty_wellFormed _ (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed space))
  cases lock : withTicket (Mutex.empty (Borrowing.empty (Ownership.empty space))) (.adopt 0 ⟨65536, 4⟩) with
  | error fault =>
    simp only [BitVec.ofNat_eq_ofNat] at lock
    simp [setupIn, lock] at success
  | ok locked =>
    cases data : withTicket locked.1 (.adopt 0 ⟨131072, 8⟩) with
    | error fault =>
      simp only [BitVec.ofNat_eq_ofNat] at lock data
      simp [setupIn, lock, data] at success
    | ok payload =>
      cases code : withTicket payload.1 (.adopt 0 ⟨4194304, 37⟩) with
      | error fault =>
        simp only [BitVec.ofNat_eq_ofNat] at lock data code
        simp [setupIn, lock, data, code] at success
      | ok executable =>
        cases stack : withTicket executable.1 (.adopt 0 ⟨32768, 8⟩) with
        | error fault =>
          simp only [BitVec.ofNat_eq_ofNat] at lock data code stack
          simp [setupIn, lock, data, code, stack] at success
        | ok caller =>
          cases registered : Mutex.register caller.1 (configuration predicate) with
          | error fault =>
            simp only [BitVec.ofNat_eq_ofNat] at lock data code stack
            simp [setupIn, lock, data, code, stack, registered, Except.mapError] at success
          | ok shared =>
            simp only [BitVec.ofNat_eq_ofNat] at lock data code stack
            simp [setupIn, lock, data, code, stack, registered, Except.mapError] at success
            subst result
            have lockValid := Mutex.mutate_wellFormed _ _ _ initialValid (withTicket_ok _ _ _ lock)
            have dataValid := Mutex.mutate_wellFormed _ _ _ lockValid (withTicket_ok _ _ _ data)
            have codeValid := Mutex.mutate_wellFormed _ _ _ dataValid (withTicket_ok _ _ _ code)
            have stackValid := Mutex.mutate_wellFormed _ _ _ codeValid (withTicket_ok _ _ _ stack)
            have sharedValid := Mutex.register_wellFormed _ _ _ stackValid registered
            obtain ⟨_, _, _, _, _, _, _, _, same⟩ := Mutex.register_ok _ _ _ stackValid.1 registered
            have present : shared.mutex = some ⟨configuration predicate, none⟩ := by rw [same]
            refine ⟨empty_invariant _ _ sharedValid ⟨_, present, rfl⟩ ?_, rfl⟩
            intro record live
            rw [present] at live
            cases live
            rfl

def spawnMany (state : MutexReplay.State) (start : Start) : Nat → Except MutexReplay.Fault MutexReplay.State
  | 0 => .ok state
  | count + 1 => do
    let after ← spawn state start
    spawnMany after start count

theorem spawnMany_valid (state : MutexReplay.State) (start : Start) (count : Nat)
    (after : MutexReplay.State) (config : Mutex.Config) (valid : Invariant config state)
    (entryPhase : ∀ worker ∈ state.workers, worker.phase = .entry)
    (success : spawnMany state start count = .ok after) :
    Invariant config after ∧ (∀ worker ∈ after.workers, worker.phase = .entry) ∧
      after.workers.length = state.workers.length + count := by
  induction count generalizing state with
  | zero => simp [spawnMany] at success; cases success; exact ⟨valid, entryPhase, by omega⟩
  | succ count induction =>
    cases spawned : spawn state start with
    | error fault => simp [spawnMany, spawned] at success
    | ok next =>
      have tail : spawnMany next start count = .ok after := by simpa [spawnMany, spawned] using success
      obtain ⟨invariant, phases, length⟩ := induction next
        (spawn_invariant _ _ _ _ valid spawned) (spawn_entry _ _ _ spawned) tail
      have added := spawn_length _ _ _ spawned
      exact ⟨invariant, phases, by omega⟩

def cohort (predicate : BitVec 32 → Bool) (old : BitVec 32) (count : Nat) :
    Except MutexReplay.Fault MutexReplay.State := do
  let (state, start) ← setupIn (seed old) predicate
  spawnMany state start count

/-- Every successful setup/spawn sequence produces an entry cohort satisfying
the generic invariant; no invariant of its result is assumed. -/
theorem cohort_valid (predicate : BitVec 32 → Bool) (old : BitVec 32) (count : Nat)
    (state : MutexReplay.State) (success : cohort predicate old count = .ok state) :
    Invariant (configuration predicate) state ∧
      (∀ worker ∈ state.workers, worker.phase = .entry) ∧ state.workers.length = count := by
  cases prepared : setupIn (seed old) predicate with
  | error fault => simp [cohort, prepared] at success
  | ok pair =>
    have next : spawnMany pair.1 pair.2 count = .ok state := by simpa [cohort, prepared] using success
    obtain ⟨valid, empty⟩ := setupIn_valid _ _ _ prepared
    have entryPhase : ∀ worker ∈ pair.1.workers, worker.phase = .entry := by simp [empty]
    obtain ⟨invariant, phases, length⟩ := spawnMany_valid _ _ _ _ _ valid entryPhase next
    exact ⟨invariant, phases, by simpa [empty] using length⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Normal forms used to share checked setup and spawn computations. They
carry no validity assumptions; the success lemmas below validate them. -/
def prepared (old : BitVec 32) (predicate : BitVec 32 → Bool) : MutexReplay.State :=
  let space := seed old
  let lock := Ownership.install (Ownership.empty space) space 0 ⟨65536, 4⟩
  let data := Ownership.install lock space 0 ⟨131072, 8⟩
  let code := Ownership.install data space 0 ⟨4194304, 37⟩
  let stack := Ownership.install code space 0 ⟨32768, 8⟩
  MutexReplay.empty ⟨Borrowing.empty stack, 0, some ⟨configuration predicate, none⟩⟩

def start : Start := ⟨entry, ⟨2, 0⟩, ⟨3, 0⟩⟩

private def appendWorker (state : MutexReplay.State) : MutexReplay.State :=
  let identifier := state.workers.length
  let codeId := state.shared.shared.nextLoan
  let code := Borrowing.installLoan state.shared.shared
    ⟨start.codeTicket, 0, principal identifier, codeRegion entry⟩
  let stack := Borrowing.installLoan code
    ⟨start.stackTicket, 0, principal identifier, Threads.stackRegion entry⟩
  ⟨{ state.shared with shared := stack }, state.workers ++
    [⟨entry, 8192, codeId, codeId + 1, entry, .entry, none⟩]⟩

/-- A shared normal form for entry cohorts. Use a checked `cohort` success
equality to establish admission, rather than assuming this form is valid. -/
def entrants (old : BitVec 32) (predicate : BitVec 32 → Bool) : Nat → MutexReplay.State
  | 0 => prepared old predicate
  | count + 1 => appendWorker (entrants old predicate count)

theorem setup_unrestricted (old : BitVec 32) :
    setupIn (seed old) unrestricted = .ok (prepared old unrestricted, start) := by
  rfl

private theorem first_spawn (old : BitVec 32) :
    spawn (prepared old unrestricted) start = .ok (appendWorker (prepared old unrestricted)) := by
  rfl

private theorem second_spawn (old : BitVec 32) :
    spawn (appendWorker (prepared old unrestricted)) start =
      .ok (appendWorker (appendWorker (prepared old unrestricted))) := by
  rfl

/-- A nonempty witness whose actual checked admission is proved below. -/
def admitted (old : BitVec 32) : MutexReplay.State :=
  entrants old unrestricted 2

theorem admitted_success (old : BitVec 32) : cohort unrestricted old 2 = .ok (admitted old) := by
  simp [cohort, setup_unrestricted, spawnMany, first_spawn, second_spawn, admitted, entrants]

/-- Checked adoption, registration, code/stack admission, and both spawns
succeed for every 32-bit word, without an input parity restriction. -/
theorem all_words_admitted (old : BitVec 32) : (cohort unrestricted old 2).toOption.isSome = true := by
  rw [admitted_success]
  rfl

theorem admitted_valid (old : BitVec 32) :
    Invariant (configuration unrestricted) (admitted old) ∧
      (∀ worker ∈ (admitted old).workers, worker.phase = .entry) ∧ (admitted old).workers.length = 2 :=
  cohort_valid _ _ _ _ (admitted_success old)

theorem admitted_observed (old : BitVec 32) :
    loadDWord (toMemory (admitted old).shared.shared.resources.space) 131072 = .ok old := by
  change Except.ok (joinDWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8)) = Except.ok old
  rw [join_extracts]

theorem unrestricted_closed : ClosedUnderTwo (configuration unrestricted) := by
  intro value _
  rfl

/-- The admitted symbolic cohort instantiates the independent total theorem
for any supplied successful completing schedule, including modular overflow. -/
theorem admitted_total (old : BitVec 32) (selections : List Nat)
    (result : MutexReplay.State × List (Nat × AtomicEvent))
    (success : schedule (admitted old) selections = .ok result) (finished : Finished result.1) :
    loadDWord (toMemory result.1.shared.shared.resources.space) 131072 = .ok (old + 4) := by
  obtain ⟨valid, entryPhase, length⟩ := admitted_valid old
  have total := completed_total _ _ _ _ old valid unrestricted_closed entryPhase (admitted_observed old) success finished
  simpa only [configuration, length, BitVec.ofNat_eq_ofNat] using total

/-- Worker zero has performed its first store before worker one executes an
entire busy retry. Both subsequently complete through their actual RET. -/
def contended : List Nat := List.replicate 7 0 ++ List.replicate 4 1 ++
  List.replicate 6 0 ++ List.replicate 13 1

def serial (count : Nat) : List Nat :=
  (List.range count).flatMap fun identifier => List.replicate 13 identifier

end EDSL.Examples.MutexWorkers
