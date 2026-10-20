/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.MutexWorkers
import EDSL.OS.MutexReplay.Progress
import EDSL.OS.MutexReplay.Coverage

namespace EDSL.Examples.MutexWorkers
open X86 OS OS.AddressSpace OS.MutexReplay

/-- Readiness is obtained from the successful checked spawns. In particular,
the executable bytes and saved return word are never assumed of the result. -/
theorem spawnMany_executionReady (state : MutexReplay.State) (start : Start) (count : Nat)
    (after : MutexReplay.State) (config : Mutex.Config) (valid : Invariant config state)
    (ready : ExecutionReady state) (success : spawnMany state start count = .ok after) :
    ExecutionReady after := by
  induction count generalizing state with
  | zero => simp [spawnMany] at success; cases success; exact ready
  | succ count induction =>
    cases spawned : spawn state start with
    | error fault => simp [spawnMany, spawned] at success
    | ok next =>
      have tail : spawnMany next start count = .ok after := by
        simpa [spawnMany, spawned] using success
      exact induction next (spawn_invariant _ _ _ _ valid spawned)
        (spawn_executionReady _ _ _ valid.shared ready spawned) tail

theorem cohort_executionReady (predicate : BitVec 32 → Bool) (old : BitVec 32) (count : Nat)
    (state : MutexReplay.State) (success : cohort predicate old count = .ok state) :
    ExecutionReady state := by
  cases prepared : setupIn (seed old) predicate with
  | error fault => simp [cohort, prepared] at success
  | ok pair =>
    have next : spawnMany pair.1 pair.2 count = .ok state := by
      simpa [cohort, prepared] using success
    obtain ⟨valid, empty⟩ := setupIn_valid _ _ _ prepared
    have ready : ExecutionReady pair.1 := by
      intro identifier worker live
      rw [empty] at live
      cases live
    exact spawnMany_executionReady _ _ _ _ _ valid ready next

theorem admitted_executionReady (old : BitVec 32) : ExecutionReady (admitted old) :=
  cohort_executionReady _ _ _ _ (admitted_success old)

/-- Every 32-bit input has an actual completing schedule of twenty-six user
instructions, no busy acquisition, and the independent two-request result.
Successful future replay is a conclusion of forward enabledness. -/
theorem admitted_completion (old : BitVec 32) :
    ∃ selections result, schedule (admitted old) selections = .ok result ∧
      Finished result.1 ∧ busyCount result.2 = 0 ∧ selections.length = 26 ∧
      loadDWord (toMemory result.1.shared.shared.resources.space) 131072 = .ok (old + 4) := by
  obtain ⟨valid, entry, length⟩ := admitted_valid old
  obtain ⟨selections, result, success, finished, noBusy, steps⟩ :=
    entry_cohort_completion _ _ valid (admitted_executionReady old) unrestricted_closed entry
  exact ⟨selections, result, success, finished, noBusy, by simpa only [length] using steps,
    admitted_total old selections result success finished⟩

/-- A successful finite prefix may leave the lock held or a retry in flight.
Forward preservation still constructs a completing suffix, without a future
success premise or a fairness assumption. The bound counts user instructions. -/
theorem admitted_prefix_completion (old : BitVec 32) (prior : List Nat)
    (middle : MutexReplay.State × List (Nat × AtomicEvent))
    (success : schedule (admitted old) prior = .ok middle) :
    ∃ selections result, schedule middle.1 selections = .ok result ∧
      Finished result.1 ∧ busyCount result.2 = 0 ∧
      selections.length = potentialSum middle.1 ∧ selections.length ≤ 30 := by
  have valid := (admitted_valid old).1
  have preserved := schedule_invariant _ _ _ _ valid unrestricted_closed success
  have ready := schedule_executionReady _ _ _ _ valid (admitted_executionReady old)
    unrestricted_closed success
  obtain ⟨selections, result, scheduled, finished, noBusy, steps, bound⟩ :=
    cohort_completion _ _ preserved ready unrestricted_closed
  have length : middle.1.workers.length = 2 :=
    (schedule_trace _ _ _ success).length.trans (admitted_valid old).2.2
  exact ⟨selections, result, scheduled, finished, noBusy, steps, by simpa only [length] using bound⟩

/-- The symbolic completion theorem applies to the scheduler which executes
only architectural instructions, with no replay phase or resource gates. -/
theorem admitted_machine_completion (old : BitVec 32) :
    ∃ selections result, MachineThreads.schedule (erase (admitted old)) selections = .ok result ∧
      MachineThreads.Finished result.1 ∧ busyCount result.2 = 0 ∧ selections.length = 26 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := by
  obtain ⟨valid, entry, length⟩ := admitted_valid old
  obtain ⟨selections, result, success, finished, noBusy, steps⟩ :=
    machine_entry_completion _ _ valid (admitted_executionReady old) unrestricted_closed entry
  have total := machine_completed_total _ _ _ _ old valid (admitted_executionReady old)
    unrestricted_closed entry (admitted_observed old) success finished
  exact ⟨selections, result, success, finished, noBusy, by simpa only [length] using steps,
    by simpa only [configuration, length, BitVec.ofNat_eq_ofNat] using total⟩

theorem admitted_machine_total (old : BitVec 32) (selections : List Nat)
    (result : MachineThreads.State × List (Nat × AtomicEvent))
    (success : MachineThreads.schedule (erase (admitted old)) selections = .ok result)
    (finished : MachineThreads.Finished result.1) :
    loadDWord result.1.memory 131072 = .ok (old + 4) := by
  obtain ⟨valid, entry, length⟩ := admitted_valid old
  have total := machine_completed_total _ _ _ _ old valid (admitted_executionReady old)
    unrestricted_closed entry (admitted_observed old) success finished
  simpa only [configuration, length, BitVec.ofNat_eq_ofNat] using total

/-- Any successful architectural prefix has a completing architectural suffix,
including a paused holder or failed acquisition. The total concerns the
original requests, rather than a new contract imposed on the intermediate word. -/
theorem admitted_machine_prefix_completion (old : BitVec 32) (prior : List Nat)
    (middle : MachineThreads.State × List (Nat × AtomicEvent))
    (success : MachineThreads.schedule (erase (admitted old)) prior = .ok middle) :
    ∃ selections result, MachineThreads.schedule middle.1 selections = .ok result ∧
      MachineThreads.Finished result.1 ∧ busyCount result.2 = 0 ∧ selections.length ≤ 30 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := by
  obtain ⟨replayed, scheduled, same⟩ := schedule_lifts _ _ _ _ (admitted_valid old).1
    (admitted_executionReady old) unrestricted_closed success
  obtain ⟨selections, result, completed, finished, noBusy, _, bound⟩ :=
    admitted_prefix_completion old prior replayed scheduled
  have whole := schedule_append_ok _ _ _ _ _ scheduled completed
  have total := admitted_total old (prior ++ selections)
    (result.1, replayed.2 ++ result.2) whole finished
  refine ⟨selections, (erase result.1, result.2), ?_, (erase_finished _).mpr finished,
    noBusy, bound, total⟩
  rw [same]
  exact schedule_erases _ _ _ completed

end EDSL.Examples.MutexWorkers
