/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Collection

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

theorem schedule_append_success (state : State) (first second : List Nat)
    (middle result : State × List (Nat × AtomicEvent)) (started : schedule state first = .ok middle)
    (finished : schedule middle.1 second = .ok result) :
    schedule state (first ++ second) = .ok (result.1, middle.2 ++ result.2) := by
  induction first generalizing state middle with
  | nil => simp [schedule] at started; cases started; simpa using finished
  | cons identifier rest induction =>
    obtain ⟨head, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ started
    rw [same] at finished ⊢
    have next := induction head.1 tail scheduled finished
    simp only [List.cons_append, schedule, selected, ok_bind, next, pure_ok]
    cases head.2 <;> rfl

/-- A constructive finite schedule: finish each supplied live worker using its
proved remaining-instruction variant. This witnesses progress without imposing
fairness on all scheduler choices. Completed repeated IDs contribute no steps. -/
def finishWorkers (state : State) : List Nat → Except Fault (State × List (Nat × AtomicEvent))
  | [] => .ok (state, [])
  | identifier :: rest => do
    let some worker := state.workers identifier | throw .missingThread
    let first ← schedule state (List.replicate worker.remaining identifier)
    let tail ← finishWorkers first.1 rest
    return (tail.1, first.2 ++ tail.2)

theorem finishWorkers_cons_ok (state : State) (identifier : Nat) (rest : List Nat)
    (result : State × List (Nat × AtomicEvent)) (success : finishWorkers state (identifier :: rest) = .ok result) :
    ∃ worker first tail, state.workers identifier = some worker ∧
      schedule state (List.replicate worker.remaining identifier) = .ok first ∧
      finishWorkers first.1 rest = .ok tail ∧ result = (tail.1, first.2 ++ tail.2) := by
  cases found : state.workers identifier with
  | none => simp [finishWorkers, found] at success
  | some worker =>
    cases selected : schedule state (List.replicate worker.remaining identifier) with
    | error fault => simp [finishWorkers, found, selected] at success
    | ok first =>
      cases finished : finishWorkers first.1 rest with
      | error fault => simp [finishWorkers, found, selected, finished] at success
      | ok tail =>
        simp [finishWorkers, found, selected, finished] at success
        exact ⟨worker, first, tail, rfl, selected, finished, success.symm⟩

theorem finishWorkers_schedule (state : State) (identifiers : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : finishWorkers state identifiers = .ok result) : ∃ selections, schedule state selections = .ok result := by
  induction identifiers generalizing state result with
  | nil => simp [finishWorkers] at success; cases success; exact ⟨[], rfl⟩
  | cons identifier rest induction =>
    obtain ⟨worker, first, tail, _, selected, finished, same⟩ := finishWorkers_cons_ok _ _ _ _ success
    obtain ⟨selections, scheduled⟩ := induction first.1 tail finished
    rw [same]
    exact ⟨List.replicate worker.remaining identifier ++ selections,
      schedule_append_success state _ selections first tail selected scheduled⟩

theorem finishWorkers_enabled (state : State) (identifiers : List Nat) (valid : WellFormed state)
    (live : ∀ identifier ∈ identifiers, ∃ worker, state.workers identifier = some worker) :
    ∃ result, finishWorkers state identifiers = .ok result := by
  induction identifiers generalizing state with
  | nil => exact ⟨(state, []), rfl⟩
  | cons identifier rest induction =>
    obtain ⟨worker, found⟩ := live identifier (by simp)
    obtain ⟨first, selected⟩ := schedule_own_enabled worker.remaining state identifier worker valid found rfl
    have nextValid := schedule_wellFormed _ _ _ valid selected
    have nextLive : ∀ query ∈ rest, ∃ current, first.1.workers query = some current := by
      intro query member
      obtain ⟨previous, previousAt⟩ := live query (by simp [member])
      obtain ⟨current, currentAt, _⟩ := schedule_remaining _ _ _ _ _ valid previousAt selected
      exact ⟨current, currentAt⟩
    obtain ⟨tail, finished⟩ := induction first.1 nextValid nextLive
    exact ⟨(tail.1, first.2 ++ tail.2), by simp [finishWorkers, found, selected, finished]⟩

theorem finishWorkers_completed (state : State) (identifiers : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : finishWorkers state identifiers = .ok result) :
    ∀ identifier ∈ identifiers, ∃ worker, result.1.workers identifier = some worker ∧ worker.phase = .completed := by
  induction identifiers generalizing state result with
  | nil => simp
  | cons identifier rest induction =>
    obtain ⟨worker, first, tail, found, selected, finished, same⟩ := finishWorkers_cons_ok _ _ _ _ success
    have nextValid := schedule_wellFormed _ _ _ valid selected
    have completedRest := induction first.1 tail nextValid finished
    obtain ⟨selections, scheduled⟩ := finishWorkers_schedule _ _ _ finished
    obtain ⟨middle, middleAt, phase⟩ := schedule_completes state (List.replicate worker.remaining identifier)
      identifier worker first valid found selected (by simp)
    obtain ⟨current, currentAt, remaining⟩ := schedule_remaining first.1 selections identifier middle tail nextValid middleAt scheduled
    have beforeZero := middle.remaining_zero.mpr phase
    have afterZero : current.remaining = 0 := by omega
    rw [same]
    intro query member
    simp only [List.mem_cons] at member
    rcases member with own | other
    · subst query; exact ⟨current, currentAt, current.remaining_zero.mp afterZero⟩
    · exact completedRest query other

theorem finish_all (state : State) (valid : WellFormed state) :
    ∃ result selections, finishWorkers state (liveIds state) = .ok result ∧ schedule state selections = .ok result ∧
      WellFormed result.1 ∧ (∀ identifier worker, result.1.workers identifier = some worker → worker.phase = .completed) := by
  have live : ∀ identifier ∈ liveIds state, ∃ worker, state.workers identifier = some worker :=
    fun identifier member => (liveIds_member state valid identifier).mp member
  obtain ⟨result, finished⟩ := finishWorkers_enabled state (liveIds state) valid live
  obtain ⟨selections, scheduled⟩ := finishWorkers_schedule _ _ _ finished
  refine ⟨result, selections, finished, scheduled, schedule_wellFormed _ _ _ valid scheduled, ?_⟩
  intro identifier worker found
  obtain ⟨previous, previousAt, _⟩ := schedule_origin _ _ _ valid scheduled identifier worker found
  have member := (liveIds_member state valid identifier).mpr ⟨previous, previousAt⟩
  obtain ⟨current, currentAt, completed⟩ := finishWorkers_completed _ _ _ valid finished identifier member
  have equal := Option.some.inj (currentAt.symm.trans found)
  subst current
  exact completed

/-- A constructive completion/collection path for every well-formed
published workload. The final word is an independent arithmetic specification;
every worker is collected and its output is zero. Physical runtime/kernel
conformance remains external; the finite path provides no arbitrary-scheduler
progress or unrecorded-interference guarantee. -/
theorem finish_collect_counter (state : State) (address : Word) (initial : BitVec 32)
    (valid : WellFormed state) (allAt : AllAt state address)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok initial)
    (started : ∀ identifier worker, state.workers identifier = some worker → worker.phase = .entry) :
    ∃ finished events selections joined,
      finishWorkers state (liveIds state) = .ok (finished, events) ∧
      schedule state selections = .ok (finished, events) ∧
      collect finished 0 (liveIds finished) = .ok joined ∧ WellFormed joined.1 ∧
      joined.2 = List.replicate (liveIds finished).length 0 ∧ (∀ identifier, joined.1.workers identifier = none) ∧
      loadDWord (toMemory joined.1.shared.shared.resources.space) address = .ok (initial + BitVec.ofNat 32 (requested state)) := by
  obtain ⟨result, selections, finished, scheduled, finalValid, completed⟩ := finish_all state valid
  have counter := completed_counter state selections result address initial valid allAt observed started scheduled completed
  obtain ⟨joined, collected, joinedValid, zeros, removed, resources⟩ := collect_all result.1 finalValid completed
  exact ⟨result.1, result.2, selections, joined, finished, scheduled, collected, joinedValid, zeros, removed,
    by rw [resources]; exact counter⟩

end EDSL.OS.CounterThreads
