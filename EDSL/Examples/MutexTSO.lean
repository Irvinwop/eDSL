/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.MutexExecution
import EDSL.OS.MutexTSO.Progress

namespace EDSL.Examples.MutexWorkers
open X86 OS OS.AddressSpace

/-- Checked admission supplies every executable byte and saved return word.
The additional TSO profile also checks aligned payload access and absence of
execute permission on all lock and payload bytes, for every payload word. -/
theorem admitted_tso_profile (old : BitVec 32) :
    MutexTSO.Profile (configuration unrestricted) (MutexTSO.logicalMemory (admitted old)) := by
  exact ⟨rfl, rfl, rfl⟩

/-- The buffered model starts from the same checked two-worker cohort; no
future replay, publication, return, or endpoint result is assumed. -/
theorem admitted_tso_admission (old : BitVec 32) :
    MutexTSO.Admission (configuration unrestricted) (admitted old) old :=
  ⟨(admitted_valid old).1, admitted_executionReady old, admitted_tso_profile old,
    unrestricted_closed, (admitted_valid old).2.1, admitted_observed old⟩

abbrev tsoInitial (old : BitVec 32) : TSO.State := TSO.initial (MutexReplay.erase (admitted old))

theorem admitted_tso_related (old : BitVec 32) :
    MutexTSO.Rel (configuration unrestricted) (tsoInitial old) (admitted old) :=
  MutexTSO.Rel.initial (admitted_valid old).1 (admitted_executionReady old) (admitted_tso_profile old)

/-- Every actual finite buffered execution retains its complete checked OS
witness. The replay schedule consists exactly of its retired observations. -/
theorem admitted_tso_prefix (old : BitVec 32) (actions : List TSO.Action)
    (result : TSO.State × List TSO.Observation)
    (success : TSO.schedule (tsoInitial old) actions = .ok result) :
    ∃ finalState,
      MutexReplay.schedule (admitted old) (MutexTSO.retiredSelections result.2) =
        .ok (finalState, TSO.atomicEvents result.2) ∧
      MutexTSO.Rel (configuration unrestricted) result.1 finalState :=
  MutexTSO.schedule_lifts (admitted_tso_related old) unrestricted_closed success

/-- Actual returns alone establish publication and the independent +2 request
per worker, with modular overflow. This concerns physical RAM, not an overlay. -/
theorem admitted_tso_total (old : BitVec 32) (actions : List TSO.Action)
    (result : TSO.State × List TSO.Observation)
    (success : TSO.schedule (tsoInitial old) actions = .ok result)
    (returned : TSO.Returned result.1) : loadDWord result.1.memory 131072 = .ok (old + 4) := by
  have total := (MutexTSO.completed_observations (admitted_tso_admission old) success returned).total
  simpa only [configuration, (admitted_valid old).2.2, BitVec.ofNat_eq_ofNat] using total

/-- The retired-instruction lower bound applies to every physically completing
execution of these bytes, including busy retries, stalls and delayed drains. -/
theorem admitted_tso_minimum (old : BitVec 32) (actions : List TSO.Action)
    (result : TSO.State × List TSO.Observation)
    (success : TSO.schedule (tsoInitial old) actions = .ok result)
    (returned : TSO.Returned result.1) : 26 ≤ TSO.retiredCount result.2 := by
  simpa only [(admitted_valid old).2.2] using
    MutexTSO.completed_minimum (admitted_tso_admission old) success returned

/-- Every symbolic entry cohort has an actual completing buffered run.
Publication is constructed; the theorem assumes no future successful run. -/
theorem admitted_tso_completion (old : BitVec 32) :
    ∃ actions result, TSO.schedule (tsoInitial old) actions = .ok result ∧
      TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
      MutexTSO.blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 = 26 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := by
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired, outcome⟩ :=
    MutexTSO.entry_completion (admitted_tso_admission old)
  refine ⟨actions, result, scheduled, finished, noBusy, noBlocked, ?_, ?_⟩
  · simpa only [(admitted_valid old).2.2] using retired
  · simpa only [configuration, (admitted_valid old).2.2, BitVec.ofNat_eq_ofNat] using outcome.total

/-- Every actual successful prefix has a completing suffix satisfying the
original requests. A paused busy acquisition and delayed stores need no new
admission or fairness assumption. The bound counts retired instructions. -/
theorem admitted_tso_prefix_completion (old : BitVec 32) (prior : List TSO.Action)
    (middle : TSO.State × List TSO.Observation)
    (success : TSO.schedule (tsoInitial old) prior = .ok middle) :
    ∃ actions result, TSO.schedule middle.1 actions = .ok result ∧
      TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
      MutexTSO.blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 ≤ 30 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := by
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, bound, outcome⟩ :=
    MutexTSO.prefix_completion (admitted_tso_admission old) success
  refine ⟨actions, result, scheduled, finished, noBusy, noBlocked, ?_, ?_⟩
  · simpa only [(admitted_valid old).2.2] using bound
  · simpa only [configuration, (admitted_valid old).2.2, BitVec.ofNat_eq_ofNat] using outcome.total

/-- A constructed entry execution attains thirty model actions: twenty-six
retired instructions and four FIFO drains, with no busy exchange or stall. -/
theorem admitted_tso_action_completion (old : BitVec 32) :
    ∃ actions result, TSO.schedule (tsoInitial old) actions = .ok result ∧
      TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
      MutexTSO.blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 = 26 ∧
      MutexTSO.drainCount result.2 = 4 ∧ actions.length = 30 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := by
  obtain ⟨actions, result, scheduled, finished, noBusy, noBlocked, retired, drained, count, outcome⟩ :=
    MutexTSO.entry_action_completion (admitted_tso_admission old)
  refine ⟨actions, result, scheduled, finished, noBusy, noBlocked, ?_, ?_, ?_, ?_⟩
  · simpa only [(admitted_valid old).2.2] using retired
  · simpa only [(admitted_valid old).2.2] using drained
  · simpa only [(admitted_valid old).2.2] using count
  · simpa only [configuration, (admitted_valid old).2.2, BitVec.ofNat_eq_ofNat] using outcome.total

end EDSL.Examples.MutexWorkers
