/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.History
import EDSL.OS.CounterThreads.Progress

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

def recordEvent (identifier : Nat) (event : Option AtomicEvent) (tail : List (Nat × AtomicEvent)) : List (Nat × AtomicEvent) :=
  match event with | none => tail | some event => (identifier, event) :: tail

def schedule (state : State) : List Nat → Except Fault (State × List (Nat × AtomicEvent))
  | [] => .ok (state, [])
  | identifier :: rest => do
    let first ← dispatch state identifier
    let tail ← schedule first.1 rest
    return (tail.1, recordEvent identifier first.2 tail.2)

theorem schedule_cons_ok (state : State) (identifier : Nat) (rest : List Nat)
    (result : State × List (Nat × AtomicEvent)) (success : schedule state (identifier :: rest) = .ok result) :
    ∃ first tail, dispatch state identifier = .ok first ∧ schedule first.1 rest = .ok tail ∧
      result = (tail.1, recordEvent identifier first.2 tail.2) := by
  cases head : dispatch state identifier with
  | error fault => simp [schedule, head] at success
  | ok first =>
    cases next : schedule first.1 rest with
    | error fault => simp [schedule, head, next] at success
    | ok tail =>
      simp [schedule, head, next] at success
      exact ⟨first, tail, rfl, next, success.symm⟩

theorem schedule_history (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : History state result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .refl
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .next (.dispatch selected) (induction first.1 tail scheduled)

theorem schedule_wellFormed (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result) : WellFormed result.1 :=
  (schedule_history _ _ _ success).wellFormed valid

theorem schedule_remaining (state : State) (selections : List Nat) (query : Nat) (worker : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result) :
    ∃ current, result.1.workers query = some current ∧ current.remaining + selections.count query = worker.remaining := by
  induction selections generalizing state worker result with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨worker, live, by simp⟩
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    obtain ⟨middle, middleAt, progress⟩ := dispatch_remaining _ _ _ _ _ valid live selected
    obtain ⟨current, currentAt, remaining⟩ := induction first.1 middle tail
      (dispatch_wellFormed _ _ _ valid selected) middleAt scheduled
    rw [same]
    refine ⟨current, currentAt, ?_⟩
    by_cases own : identifier = query
    · simp [own] at progress ⊢; omega
    · simp [own, eq_comm] at progress ⊢; omega

theorem Worker.remaining_zero (worker : Worker) : worker.remaining = 0 ↔ worker.phase = .completed := by
  cases phase : worker.phase <;> simp [Worker.remaining, phase] <;> omega

theorem schedule_completes (state : State) (selections : List Nat) (query : Nat) (worker : Worker)
    (result : State × List (Nat × AtomicEvent)) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : schedule state selections = .ok result)
    (selected : selections.count query = worker.remaining) :
    ∃ current, result.1.workers query = some current ∧ current.phase = .completed := by
  obtain ⟨current, currentAt, remaining⟩ := schedule_remaining _ _ _ _ _ valid live success
  have zero : current.remaining = 0 := by omega
  exact ⟨current, currentAt, current.remaining_zero.mp zero⟩

theorem schedule_own_enabled (steps : Nat) (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker) (remaining : worker.remaining = steps) :
    ∃ result, schedule state (List.replicate steps identifier) = .ok result := by
  induction steps generalizing state worker with
  | zero => exact ⟨(state, []), rfl⟩
  | succ steps induction =>
    have unfinished : worker.phase ≠ .completed := by
      intro completed
      have zero := worker.remaining_zero.mpr completed
      omega
    obtain ⟨first, selected⟩ := dispatch_enabled state identifier worker valid live unfinished
    obtain ⟨middle, middleAt, progress⟩ := dispatch_remaining state identifier identifier worker first valid live selected
    have nextRank : middle.remaining = steps := by simp at progress; omega
    obtain ⟨tail, scheduled⟩ := induction first.1 middle (dispatch_wellFormed _ _ _ valid selected) middleAt nextRank
    exact ⟨(tail.1, recordEvent identifier first.2 tail.2), by simp [List.replicate_succ, schedule, selected, scheduled]⟩

theorem run_and_join (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker) :
    ∃ final events joined,
      schedule state (List.replicate worker.remaining identifier) = .ok (final, events) ∧
      join final 0 identifier = .ok joined ∧ joined.2 = 0 ∧ WellFormed joined.1 := by
  obtain ⟨result, scheduled⟩ := schedule_own_enabled worker.remaining state identifier worker valid live rfl
  obtain ⟨current, currentAt, completed⟩ := schedule_completes state (List.replicate worker.remaining identifier)
    identifier worker result valid live scheduled (by simp)
  have finalValid := schedule_wellFormed _ _ _ valid scheduled
  obtain ⟨joined, collected⟩ := join_enabled result.1 identifier current finalValid currentAt completed
  exact ⟨result.1, result.2, joined, scheduled, collected, join_zero _ _ _ _ finalValid collected,
    join_wellFormed _ _ _ _ finalValid collected⟩

theorem entry_cost (worker : Worker) (valid : PrivateValid worker) (phase : worker.phase = .entry) :
    worker.remaining = 3 * (worker.entry.registers .rcx).toNat + 3 := by
  simp only [PrivateValid, phase] at valid
  simp [Worker.remaining, phase, valid.2.2.2.2]

end EDSL.OS.CounterThreads
