/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Model

namespace EDSL.OS.TSO
open X86

theorem schedule_cons_ok (state : State) (action : Action) (rest : List Action)
    (result : State × List Observation) (success : schedule state (action :: rest) = .ok result) :
    ∃ head tail, step state action = .ok head ∧ schedule head.1 rest = .ok tail ∧
      result = (tail.1, head.2 :: tail.2) := by
  cases first : step state action with
  | error fault => simp [schedule, first] at success
  | ok head =>
    cases following : schedule head.1 rest with
    | error fault => simp [schedule, first, following] at success
    | ok tail =>
      simp [schedule, first, following] at success
      exact ⟨head, tail, rfl, following, success.symm⟩

inductive Trace : State → List Action → List Observation → State → Prop where
  | nil {state} : Trace state [] [] state
  | cons {before middle after action observation actions observations}
      (transition : step before action = .ok (middle, observation))
      (tail : Trace middle actions observations after) :
      Trace before (action :: actions) (observation :: observations) after

theorem schedule_trace (state : State) (actions : List Action) (result : State × List Observation)
    (success : schedule state actions = .ok result) : Trace state actions result.2 result.1 := by
  induction actions generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .nil
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .cons first (ih _ _ following)

theorem Trace.schedule {before after : State} {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) : schedule before actions = .ok (after, observations) := by
  induction trace with
  | nil => rfl
  | cons transition _ ih => simp [TSO.schedule, transition, ih]

theorem Trace.length {before after : State} {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) : observations.length = actions.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons]; omega

theorem schedule_append (state : State) (first second : List Action)
    (middle result : State × List Observation)
    (scheduledFirst : schedule state first = .ok middle) (suffix : schedule middle.1 second = .ok result) :
    schedule state (first ++ second) = .ok (result.1, middle.2 ++ result.2) := by
  induction first generalizing state middle with
  | nil => simp [schedule] at scheduledFirst; cases scheduledFirst; exact suffix
  | cons action rest ih =>
    obtain ⟨head, tail, step, scheduled, same⟩ := schedule_cons_ok _ _ _ _ scheduledFirst
    rw [same] at suffix ⊢
    have following := ih _ _ scheduled suffix
    simp [schedule, step, following]

/-- Successful drain exposes exactly the FIFO head and preserves every
architectural context and return flag. It may run after actual RET. -/
theorem drain_ok (state : State) (identifier : Nat) (result : State × Observation)
    (success : drain state identifier = .ok result) :
    ∃ worker head tail memory, state.workers[identifier]? = some worker ∧
      worker.buffer = head :: tail ∧
      storeDWord state.memory head.address head.value = .ok memory ∧
      result = (install state identifier memory worker.context worker.returned tail,
        .drained identifier head) := by
  cases live : state.workers[identifier]? with
  | none => simp [drain, live] at success
  | some worker =>
    cases buffer : worker.buffer with
    | nil => simp [drain, live, buffer] at success
    | cons head tail =>
      cases committed : storeDWord state.memory head.address head.value with
      | error fault => simp [drain, live, buffer, committed, Except.mapError] at success
      | ok memory =>
        simp [drain, live, buffer, committed, Except.mapError] at success
        exact ⟨worker, head, tail, memory, rfl, buffer, committed, success.symm⟩

theorem drain_memory (state : State) (identifier : Nat) (result : State × Observation)
    (success : drain state identifier = .ok result) :
    ∃ worker head tail, state.workers[identifier]? = some worker ∧ worker.buffer = head :: tail ∧
      canStoreDWord state.memory head.address = true ∧
      result.1.memory = writeDWordUnchecked state.memory head.address head.value ∧
      result.2 = .drained identifier head := by
  obtain ⟨worker, head, tail, memory, live, buffer, committed, same⟩ := drain_ok _ _ _ success
  by_cases allowed : canStoreDWord state.memory head.address = true
  · have memoryEq : memory = writeDWordUnchecked state.memory head.address head.value := by
      simpa [storeDWord, allowed] using committed.symm
    exact ⟨worker, head, tail, live, buffer, allowed, by rw [same, memoryEq]; rfl, by rw [same]⟩
  · simp [storeDWord, allowed] at committed

/-- Publication leaves the issuing thread's data view unchanged: it transfers
one pending write to shared RAM without performing a new user instruction. -/
theorem drain_view (state : State) (identifier : Nat) (result : State × Observation)
    (success : drain state identifier = .ok result) :
    ∃ before after, state.workers[identifier]? = some before ∧
      result.1.workers[identifier]? = some after ∧ after.context = before.context ∧
      after.returned = before.returned ∧
      StoreBuffer.view result.1.memory after.buffer = StoreBuffer.view state.memory before.buffer := by
  obtain ⟨worker, head, tail, memory, live, buffer, committed, same⟩ := drain_ok _ _ _ success
  have bound := (List.getElem_of_getElem? live).1
  have memoryEq : memory = writeDWordUnchecked state.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact Except.ok.inj committed.symm
    · cases committed
  refine ⟨worker, ⟨worker.context, worker.returned, tail⟩, live, ?_, rfl, rfl, ?_⟩
  · rw [same]
    exact List.getElem?_set_self bound
  · rw [same, buffer, memoryEq]
    rfl

end EDSL.OS.TSO
