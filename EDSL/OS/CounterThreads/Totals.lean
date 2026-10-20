/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Trace

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

theorem countEvents_partition (frontier : Nat) (events : List (Nat × AtomicEvent)) :
    events.countP (fun event => decide (event.1 < frontier + 1)) =
      events.countP (fun event => decide (event.1 < frontier)) + countEvents frontier events := by
  induction events with
  | nil => simp [countEvents]
  | cons event events induction =>
    by_cases smaller : event.1 < frontier
    · have within : event.1 < frontier + 1 := by omega
      have different : event.1 ≠ frontier := by omega
      simp [countEvents, smaller, within, different] at induction ⊢
      omega
    · by_cases equal : event.1 = frontier
      · have within : event.1 < frontier + 1 := by omega
        simp [countEvents, equal] at induction ⊢
        omega
      · have outside : ¬event.1 < frontier + 1 := by omega
        simpa [countEvents, smaller, equal, outside] using induction

theorem countEvents_range (frontier : Nat) (events : List (Nat × AtomicEvent)) :
    ((List.range frontier).map (fun identifier => countEvents identifier events)).sum =
      events.countP (fun event => decide (event.1 < frontier)) := by
  induction frontier with
  | zero => simp
  | succ frontier induction =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [induction]
    exact (countEvents_partition frontier events).symm

theorem countEvents_total (frontier : Nat) (events : List (Nat × AtomicEvent))
    (within : ∀ event ∈ events, event.1 < frontier) :
    ((List.range frontier).map (fun identifier => countEvents identifier events)).sum = events.length := by
  rw [countEvents_range]
  exact List.countP_eq_length.mpr (by intro event member; simpa using within event member)

theorem missing_event_count (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result)
    (query : Nat) (missing : state.workers query = none) : countEvents query result.2 = 0 := by
  apply List.countP_eq_zero.mpr
  intro event member
  simp only [decide_eq_true_eq]
  intro equal
  obtain ⟨worker, live⟩ := schedule_event_live _ _ _ valid success event member
  obtain ⟨previous, original, _⟩ := schedule_origin _ _ _ valid success event.1 worker live
  rw [equal, missing] at original
  cases original

def requested (state : State) : Nat :=
  ((List.range state.nextThread).map fun identifier =>
    match state.workers identifier with
    | none => 0
    | some worker => (worker.entry.registers .rcx).toNat).sum

/-- Every finite registry size and every 64-bit iteration input are admitted.
Once all initially started workers complete, the event total is exactly the
sum of their independently published iteration requests. -/
theorem completed_total_events (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (started : ∀ identifier worker, state.workers identifier = some worker → worker.phase = .entry)
    (success : schedule state selections = .ok result)
    (completed : ∀ identifier worker, result.1.workers identifier = some worker → worker.phase = .completed) :
    result.2.length = requested state := by
  rw [← countEvents_total state.nextThread result.2 (schedule_event_bound _ _ _ valid success)]
  unfold requested
  apply congrArg List.sum
  apply List.map_congr_left
  intro identifier _
  cases found : state.workers identifier with
  | none => exact missing_event_count _ _ _ valid success identifier found
  | some worker =>
    obtain ⟨current, currentAt, _⟩ := schedule_remaining state selections identifier worker result valid found success
    exact completed_event_count _ _ _ _ _ _ valid found (started _ _ found) success currentAt (completed _ _ currentAt)

/-- All successful schedules that complete the published workload have the
same modular counter result. Termination of arbitrary scheduler choices is
not assumed, and no operation outside the supplied schedule is implicit. -/
theorem completed_counter (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (address : Word) (initial : BitVec 32) (valid : WellFormed state) (allAt : AllAt state address)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok initial)
    (started : ∀ identifier worker, state.workers identifier = some worker → worker.phase = .entry)
    (success : schedule state selections = .ok result)
    (completed : ∀ identifier worker, result.1.workers identifier = some worker → worker.phase = .completed) :
    loadDWord (toMemory result.1.shared.shared.resources.space) address = .ok (initial + BitVec.ofNat 32 (requested state)) := by
  have total := completed_total_events _ _ _ valid started success completed
  simpa only [total] using schedule_counter _ _ _ address initial valid allAt observed success

end EDSL.OS.CounterThreads
