/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.MutexWorkers
import EDSL.Examples.MutexLoans
import EDSL.MutexWorkerCertificate
import EDSL.OS.MutexReplay.Cost
import EDSL.Audit

namespace EDSL.Tests.MutexInvariant
open X86 OS OS.AddressSpace OS.MutexReplay Examples.MutexWorkers

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private def checked {α : Type} (attempt : Except MutexReplay.Fault α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {α : Type} (attempt : Except MutexReplay.Fault α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

/-- Completion evidence inspects phases alone. Register values, guards,
lock/payload cells, and the postcondition checker are absent from this gate. -/
private def finishedPhases (state : MutexReplay.State) : Bool :=
  state.workers.all fun worker => decide (worker.phase = .completed)

private theorem finished_of_phases (state : MutexReplay.State) (phases : finishedPhases state = true) :
    Finished state := by
  intro identifier worker live
  exact of_decide_eq_true (List.all_eq_true.mp phases worker (List.mem_of_getElem? live))

-- Each entry normal form is tied to successful adoption/registration and
-- actual spawns. These lemmas validate the gates, rather than assuming WF.
def evenInitial : MutexReplay.State := entrants 0xfffffffe even 2

theorem even_admission : cohort even 0xfffffffe 2 = .ok evenInitial := by
  have setup : setupIn (seed 0xfffffffe) even = .ok (prepared 0xfffffffe even, start) := by rfl
  have first : spawn (prepared 0xfffffffe even) start = .ok (entrants 0xfffffffe even 1) := by rfl
  have second : spawn (entrants 0xfffffffe even 1) start = .ok evenInitial := by rfl
  simp only [BitVec.ofNat_eq_ofNat] at setup first second
  simp [cohort, setup, spawnMany, first, second]

theorem even_closed : ClosedUnderTwo (configuration even) := by
  intro value prior
  change (!value.getLsbD 0) = true at prior
  change (!(value + 2).getLsbD 0) = true
  rw [BitVec.getLsbD_add (by decide) value 2]
  simpa using prior

def evenRun : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule evenInitial contended) (by rfl)

theorem even_schedule : schedule evenInitial contended = .ok evenRun := checked_ok _ _

theorem even_finished : Finished evenRun.1 := finished_of_phases _ (by rfl)

theorem even_valid : Invariant (configuration even) evenInitial := (cohort_valid _ _ _ _ even_admission).1

-- The expected +4 is the public two-request contract. The proof obtains it
-- from preservation/accounting, never from the concrete result observation.
theorem even_total_from_generic :
    loadDWord (toMemory evenRun.1.shared.shared.resources.space) 131072 = .ok 2 := by
  obtain ⟨valid, entryPhase, length⟩ := cohort_valid _ _ _ _ even_admission
  have observed : loadDWord (toMemory evenInitial.shared.shared.resources.space) 131072 = .ok 0xfffffffe := by rfl
  have total := completed_total _ _ _ _ _ valid even_closed entryPhase observed even_schedule even_finished
  simp only [configuration, length] at total
  exact total.trans (congrArg Except.ok (show (0xfffffffe : BitVec 32) + BitVec.ofNat 32 (2 * 2) = 2 by decide))

-- Independent machine observations catch wrong store width, lost updates,
-- omitted 1->1 exchanges, nonzero returns, and failure to execute RET.
def observations (result : MutexReplay.State × List (Nat × AtomicEvent)) :
    Option (BitVec 32) × Option (BitVec 32) × Option (BitVec 32) ×
      List (Word × Word × Word) × List (Nat × AtomicEvent) :=
  ((loadDWord (toMemory result.1.shared.shared.resources.space) 131072).toOption,
   (loadDWord (toMemory result.1.shared.shared.resources.space) 131076).toOption,
   (loadDWord (toMemory result.1.shared.shared.resources.space) 65536).toOption,
   result.1.workers.map (fun worker =>
     (worker.context.registers .rax, worker.context.registers .rsp, worker.context.rip)), result.2)

def observedEven (state : MutexReplay.State) : Option Bool :=
  (loadDWord (toMemory state.shared.shared.resources.space) 131072).toOption.map even

example : observations evenRun = (some 2, some 0xa5b6c7d8, some 0,
    [(0, 32776, 8192), (0, 32776, 8192)],
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩), (0, ⟨65536, 1, 0⟩),
     (1, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 0⟩)]) := by rfl

def openPrefix : List Nat := List.replicate 7 0 ++ List.replicate 4 1

def opened : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule evenInitial openPrefix) (by rfl)

theorem opened_schedule : schedule evenInitial openPrefix = .ok opened := checked_ok _ _

-- The generic invariant remains valid while the even payload predicate is
-- false: the holder has the first store's credit and private saved value.
example : Invariant (configuration even) opened.1 :=
  schedule_invariant _ _ _ _ even_valid even_closed opened_schedule

example : loadDWord (toMemory opened.1.shared.shared.resources.space) 131072 = .ok 0xffffffff ∧
    observedEven opened.1 = some false ∧ credits opened.1 = 1 ∧
    opened.1.workers.map (fun worker => worker.phase) = [.incrementingSecond, .entry] ∧
    opened.2 = [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩)] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def releaseHolder (state : MutexReplay.State) : Except Mutex.Fault (Mutex.State × AtomicEvent) := do
  let record ← Mutex.registered state.shared
  let some lease := record.holder | throw .missingGuard
  Mutex.release state.shared lease.actor lease

example : releaseHolder opened.1 = .error .invalidInvariant := by rfl

def restored : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule opened.1 [0, 0]) (by rfl)

theorem restored_schedule : schedule opened.1 [0, 0] = .ok restored := checked_ok _ _

example : Invariant (configuration even) restored.1 :=
  schedule_invariant _ _ _ _
    (schedule_invariant _ _ _ _ even_valid even_closed opened_schedule) even_closed restored_schedule

example : loadDWord (toMemory restored.1.shared.shared.resources.space) 131072 = .ok 0 ∧
    observedEven restored.1 = some true ∧ credits restored.1 = 2 ∧ (releaseHolder restored.1).toOption.isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- A restored payload and released lock do not finish a worker. Immediately
-- before RET, both contexts still point at its actual executable byte.
def beforeRet : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule evenInitial (List.replicate 12 0 ++ List.replicate 12 1)) (by rfl)

example : beforeRet.1.workers.map (fun worker => worker.phase) = [.returning, .returning] ∧
    finishedPhases beforeRet.1 = false ∧ collect beforeRet.1 = .error .notCompleted := by
  exact ⟨rfl, rfl, rfl⟩

def afterRet : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule beforeRet.1 [1, 0]) (by rfl)

example : Finished afterRet.1 := finished_of_phases _ (by rfl)

example : afterRet.1.workers.map (fun worker => (worker.context.registers .rsp, worker.context.rip)) =
    [(32776, 8192), (32776, 8192)] := by rfl

-- The permissive invariant admits every word, not just the even example.
-- Force one busy retry between the load and first store, then a second retry
-- between the two stores, before allowing either critical section to finish.
def loadContended : List Nat := List.replicate 5 0 ++ List.replicate 4 1 ++
  List.replicate 2 0 ++ List.replicate 4 1 ++ List.replicate 6 0 ++ List.replicate 13 1

def oddRun : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule (admitted 0xffffffff) loadContended) (by rfl)

theorem odd_schedule : schedule (admitted 0xffffffff) loadContended = .ok oddRun := checked_ok _ _

theorem odd_finished : Finished oddRun.1 := finished_of_phases _ (by rfl)

example : loadDWord (toMemory oddRun.1.shared.shared.resources.space) 131072 = .ok 3 :=
  admitted_total _ _ _ odd_schedule odd_finished

example : (observations oddRun).1 = some 3 ∧ oddRun.2 =
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩), (1, ⟨65536, 1, 1⟩),
     (0, ⟨65536, 1, 0⟩), (1, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 0⟩)] := by exact ⟨rfl, rfl⟩

-- One and three workers exercise the initial + 2*count contract with
-- distinct nonempty sizes, zero busy retries, wraparound, and an odd input.
def oneInitial : MutexReplay.State := entrants 0xffffffff unrestricted 1
def threeInitial : MutexReplay.State := entrants 1 unrestricted 3

theorem one_admission : cohort unrestricted 0xffffffff 1 = .ok oneInitial := by
  have first : spawn (prepared 0xffffffff unrestricted) start = .ok oneInitial := by rfl
  simp only [BitVec.ofNat_eq_ofNat] at first
  simp [cohort, setup_unrestricted, spawnMany, first]

theorem three_admission : cohort unrestricted 1 3 = .ok threeInitial := by
  have first : spawn (prepared 1 unrestricted) start = .ok (entrants 1 unrestricted 1) := by rfl
  have second : spawn (entrants 1 unrestricted 1) start = .ok (entrants 1 unrestricted 2) := by rfl
  have third : spawn (entrants 1 unrestricted 2) start = .ok threeInitial := by rfl
  simp only [BitVec.ofNat_eq_ofNat] at first second third
  simp [cohort, setup_unrestricted, spawnMany, first, second, third]

def oneRun : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule oneInitial (serial 1)) (by rfl)

def threeRun : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule threeInitial (serial 3)) (by rfl)

theorem one_schedule : schedule oneInitial (serial 1) = .ok oneRun := checked_ok _ _
theorem three_schedule : schedule threeInitial (serial 3) = .ok threeRun := checked_ok _ _
theorem one_finished : Finished oneRun.1 := finished_of_phases _ (by rfl)
theorem three_finished : Finished threeRun.1 := finished_of_phases _ (by rfl)

example : loadDWord (toMemory oneRun.1.shared.shared.resources.space) 131072 = .ok 1 := by
  obtain ⟨valid, phases, length⟩ := cohort_valid _ _ _ _ one_admission
  have observed : loadDWord (toMemory oneInitial.shared.shared.resources.space) 131072 = .ok 0xffffffff := by rfl
  have total := completed_total _ _ _ _ _ valid unrestricted_closed phases observed one_schedule one_finished
  simp only [configuration, length] at total
  exact total.trans (congrArg Except.ok (show (0xffffffff : BitVec 32) + BitVec.ofNat 32 (2 * 1) = 1 by decide))

example : loadDWord (toMemory threeRun.1.shared.shared.resources.space) 131072 = .ok 7 := by
  obtain ⟨valid, phases, length⟩ := cohort_valid _ _ _ _ three_admission
  have observed : loadDWord (toMemory threeInitial.shared.shared.resources.space) 131072 = .ok 1 := by rfl
  have total := completed_total _ _ _ _ _ valid unrestricted_closed phases observed three_schedule three_finished
  simp only [configuration, length] at total
  exact total.trans (congrArg Except.ok (show (1 : BitVec 32) + BitVec.ofNat 32 (2 * 3) = 7 by decide))

example : (observations oneRun).1 = some 1 ∧ (observations threeRun).1 = some 7 ∧
    busyCount oneRun.2 = 0 ∧ busyCount threeRun.2 = 0 := by exact ⟨rfl, rfl, rfl, rfl⟩

-- Actual completion supplies the cost theorem's Boolean completion fact
-- through the preserved invariant, rather than through an endpoint checker.
example : contended.length = 13 * evenInitial.workers.length + 4 * busyCount evenRun.2 := by
  have phases := (cohort_valid _ _ _ _ even_admission).2.1
  have finalValid := schedule_invariant _ _ _ _ even_valid even_closed even_schedule
  exact completed_cost _ _ _ even_valid.controlled phases even_schedule (finalValid.completed even_finished)

example : busyCount evenRun.2 = 1 := by rfl

example : loadContended.length = 13 * (admitted 0xffffffff).workers.length + 4 * busyCount oddRun.2 := by
  obtain ⟨valid, phases, _⟩ := admitted_valid 0xffffffff
  have finalValid := schedule_invariant _ _ _ _ valid unrestricted_closed odd_schedule
  exact completed_cost _ _ _ valid.controlled phases odd_schedule (finalValid.completed odd_finished)

example : busyCount oddRun.2 = 2 := by rfl

example : (serial 3).length = 13 * threeInitial.workers.length + 4 * busyCount threeRun.2 := by
  obtain ⟨valid, phases, _⟩ := cohort_valid _ _ _ _ three_admission
  have finalValid := schedule_invariant _ _ _ _ valid unrestricted_closed three_schedule
  exact completed_cost _ _ _ valid.controlled phases three_schedule (finalValid.completed three_finished)

-- This instantiates the artifact's generic specification on actual checked
-- admission for every word, including its positive collection contract.
example (old : BitVec 32) :
    MutexWorkerCertificate.CompletedSpecification (admitted old) (configuration unrestricted) old := by
  obtain ⟨valid, phases, _⟩ := admitted_valid old
  exact (MutexWorkerCertificate.universal_sound bytes (by decide) _ _ _ valid
    (admitted_loanReady old) unrestricted_closed phases (admitted_observed old)).2

-- A known contended execution satisfies readiness through checked creation;
-- collection success is derived, rather than supplied as another fixture gate.
example : ∃ collected, collect evenRun.1 = .ok collected ∧
    CollectedOutcome evenInitial (configuration even) 0xfffffffe collected ∧
    ∀ loanId, collected.1.shared.loans loanId =
      if loanId ∈ cohortLoanIds evenInitial.workers then none else evenInitial.shared.shared.loans loanId := by
  obtain ⟨_, phases, _⟩ := cohort_valid _ _ _ _ even_admission
  exact completed_collection_exists _ _ _ _ _ even_valid
    (cohort_loanReady _ _ _ _ even_admission) even_closed phases (by rfl) even_schedule even_finished

end EDSL.Tests.MutexInvariant

#audit_edsl
