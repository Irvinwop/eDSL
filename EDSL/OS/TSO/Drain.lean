/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Trace

namespace EDSL.OS.TSO
open X86

/-- Sufficient current permission facts for publishing every pending write.
These describe existing queues and memory, not future drain success. -/
def PendingWritable (state : State) : Prop :=
  ∀ (identifier : Nat) (worker : Worker), state.workers[identifier]? = some worker →
    ∀ store ∈ worker.buffer, canStoreDWord state.memory store.address = true

theorem initial_pendingWritable (state : MachineThreads.State) : PendingWritable (initial state) := by
  intro identifier worker live store member
  simp only [initial, List.getElem?_map] at live
  cases found : state.workers[identifier]? with
  | none => simp [found] at live
  | some original =>
    simp only [found, Option.map_some, Option.some.injEq] at live
    subst worker
    cases member

theorem drain_enabled (state : State) (identifier : Nat) (worker : Worker)
    (ready : PendingWritable state) (live : state.workers[identifier]? = some worker)
    (pending : worker.buffer ≠ []) : ∃ result, drain state identifier = .ok result := by
  cases buffer : worker.buffer with
  | nil => exact False.elim (pending buffer)
  | cons head tail =>
    have allowed := ready identifier worker live head (by rw [buffer]; simp)
    exact ⟨(install state identifier (writeDWordUnchecked state.memory head.address head.value)
      worker.context worker.returned tail, .drained identifier head),
      by simp [drain, live, buffer, storeDWord, allowed, Except.mapError]⟩

theorem drain_pendingWritable (state : State) (identifier : Nat) (result : State × Observation)
    (ready : PendingWritable state) (success : drain state identifier = .ok result) :
    PendingWritable result.1 := by
  obtain ⟨selected, head, tail, memory, live, buffer, committed, same⟩ := drain_ok _ _ _ success
  have memoryEq : memory = writeDWordUnchecked state.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact Except.ok.inj committed.symm
    · cases committed
  have bound := (List.getElem_of_getElem? live).1
  rw [same]
  intro query worker found store member
  by_cases own : identifier = query
  · subst query
    simp only [install, List.getElem?_set_self bound, Option.some.injEq] at found
    subst worker
    have prior : store ∈ selected.buffer := by rw [buffer]; exact List.mem_cons_of_mem head member
    exact memoryEq ▸ StoreBuffer.write_canStore _ _ _ _ (ready identifier selected live store prior)
  · have prior : state.workers[query]? = some worker := by
      simpa only [install, List.getElem?_set_ne own] using found
    exact memoryEq ▸ StoreBuffer.write_canStore _ _ _ _ (ready query worker prior store member)

/-- A finite queue can always publish in exactly its current length of drain
steps. Contexts and actual returns are retained, and the issuing thread's view
is unchanged. This is an available path, not a fairness assumption. -/
theorem publish_worker (count : Nat) (state : State) (identifier : Nat) (worker : Worker)
    (ready : PendingWritable state) (live : state.workers[identifier]? = some worker)
    (length : worker.buffer.length = count) :
    ∃ result current, schedule state (List.replicate count (.drain identifier)) = .ok result ∧
      result.1.workers[identifier]? = some current ∧ current.buffer = [] ∧
      current.context = worker.context ∧ current.returned = worker.returned ∧
      StoreBuffer.view result.1.memory current.buffer = StoreBuffer.view state.memory worker.buffer ∧
      retiredCount result.2 = 0 ∧ atomicEvents result.2 = [] := by
  induction count generalizing state worker with
  | zero =>
    have empty : worker.buffer = [] := List.length_eq_zero_iff.mp length
    exact ⟨(state, []), worker, rfl, live, empty, rfl, rfl, rfl, rfl, rfl⟩
  | succ count ih =>
    have pending : worker.buffer ≠ [] := by intro empty; simp [empty] at length
    obtain ⟨first, selected⟩ := drain_enabled state identifier worker ready live pending
    obtain ⟨original, head, tail, memory, found, buffer, committed, same⟩ := drain_ok _ _ _ selected
    have equal := Option.some.inj (found.symm.trans live)
    subst original
    let middle : Worker := ⟨worker.context, worker.returned, tail⟩
    have atMiddle : first.1.workers[identifier]? = some middle := by
      rw [same]
      exact List.getElem?_set_self (List.getElem_of_getElem? live).1
    have tailLength : middle.buffer.length = count := by
      change tail.length = count
      simp only [buffer, List.length_cons] at length
      omega
    obtain ⟨result, current, scheduled, currentAt, empty, context, returned, view, noRetire, noAtomic⟩ :=
      ih first.1 middle (drain_pendingWritable _ _ _ ready selected) atMiddle tailLength
    obtain ⟨before, after, beforeAt, afterAt, _, _, sameView⟩ := drain_view _ _ _ selected
    have beforeEq := Option.some.inj (beforeAt.symm.trans live)
    have afterEq := Option.some.inj (afterAt.symm.trans atMiddle)
    subst before
    subst after
    refine ⟨(result.1, first.2 :: result.2), current, ?_, currentAt, empty,
      context, returned, view.trans sameView, ?_, ?_⟩
    · simp [List.replicate_succ, schedule, step, selected, scheduled]
    · rw [same]
      simpa only [retiredCount, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using noRetire
    · rw [same]
      simpa only [atomicEvents, List.filterMap_cons, List.filterMap] using noAtomic

end EDSL.OS.TSO
