/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Scheduling

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

def countEvents (identifier : Nat) (events : List (Nat × AtomicEvent)) : Nat :=
  events.countP fun event => decide (event.1 = identifier)

theorem dispatch_performed (state : State) (identifier query : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.performed = worker.performed + (if identifier = query ∧ result.2.isSome then 1 else 0) := by
  obtain ⟨selected, advanced, selectedAt, advancedOk, same⟩ := dispatch_ok _ _ _ success
  have selectedValid := (valid.2 _ _ selectedAt).2
  have effect := advance_effect state identifier selected advanced valid.1 selectedValid advancedOk
  rw [same]
  by_cases own : query = identifier
  · subst query
    have equal := Option.some.inj (selectedAt.symm.trans live)
    subst selected
    exact ⟨advanced.worker, by simp [replace], by simpa using effect.performed selectedValid.privateContext⟩
  · exact ⟨worker, by simpa [replace, own] using live, by simp [Ne.symm own]⟩

theorem schedule_performed (state : State) (selections : List Nat) (query : Nat) (worker : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    ∃ current, result.1.workers query = some current ∧ current.performed = worker.performed + countEvents query result.2 := by
  induction selections generalizing state worker result with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨worker, live, by simp [countEvents]⟩
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, middleAt, progress⟩ := dispatch_performed _ _ _ _ _ valid live selected
    obtain ⟨current, currentAt, counted⟩ := induction first.1 middle tail
      (dispatch_wellFormed _ _ _ valid selected) middleAt scheduled
    rw [same]
    refine ⟨current, currentAt, ?_⟩
    cases event : first.2 with
    | none => simp [event] at progress; simpa [recordEvent, countEvents, event, progress] using counted
    | some event =>
      by_cases own : identifier = query
      · simp [own, event] at progress
        simp [recordEvent, countEvents, own]
        simp only [countEvents] at counted
        omega
      · simp [own, event] at progress
        simpa [recordEvent, countEvents, event, own, progress] using counted

theorem schedule_entry (state : State) (selections : List Nat) (query : Nat) (worker current : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result)
    (after : result.1.workers query = some current) : current.entry = worker.entry := by
  obtain ⟨original, found, entry⟩ := ((schedule_history _ _ _ success).advances valid).2 query (valid.2 _ _ live).1 current after
  have equal := Option.some.inj (found.symm.trans live)
  subst original
  exact entry.symm

/-- Once a newly started worker completes, its actual emitted increment count
is exactly its published 64-bit iteration input. Peers may preempt between steps. -/
theorem completed_event_count (state : State) (selections : List Nat) (query : Nat) (worker current : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (initial : worker.phase = .entry)
    (success : schedule state selections = .ok result) (after : result.1.workers query = some current)
    (completed : current.phase = .completed) : countEvents query result.2 = (worker.entry.registers .rcx).toNat := by
  obtain ⟨actual, found, counted⟩ := schedule_performed _ _ _ _ _ valid live success
  have equal := Option.some.inj (found.symm.trans after)
  subst actual
  have entry := schedule_entry _ _ _ _ _ _ valid live success after
  have beforePrivate := (valid.2 _ _ live).2.privateContext
  have afterPrivate := ((schedule_wellFormed _ _ _ valid success).2 _ _ after).2.privateContext
  simp only [PrivateValid, initial] at beforePrivate
  simp only [PrivateValid, completed] at afterPrivate
  simpa [Worker.performed, initial, completed, beforePrivate.2.2.2.2, afterPrivate.2.2.2.2.1, entry] using counted.symm

/-- Exact per-worker user-instruction cost in every successful completing
supplied schedule, including the zero guard, final MOV and RET. Peer selections
and runtime/kernel work are outside this count. -/
theorem completed_selection_count (state : State) (selections : List Nat) (query : Nat) (worker current : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (initial : worker.phase = .entry)
    (success : schedule state selections = .ok result) (after : result.1.workers query = some current)
    (completed : current.phase = .completed) :
    selections.count query = 3 * (worker.entry.registers .rcx).toNat + 3 := by
  obtain ⟨actual, found, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  have equal := Option.some.inj (found.symm.trans after)
  subst actual
  have zero := current.remaining_zero.mpr completed
  have before := entry_cost worker (valid.2 _ _ live).2.privateContext initial
  omega

end EDSL.OS.CounterThreads
