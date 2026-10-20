/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Totals

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

def collect (state : State) (parent : Nat) : List Nat → Except Fault (State × List Word)
  | [] => .ok (state, [])
  | identifier :: rest => do
    let first ← join state parent identifier
    let tail ← collect first.1 parent rest
    return (tail.1, first.2 :: tail.2)

theorem collect_cons_ok (state : State) (parent identifier : Nat) (rest : List Nat) (result : State × List Word)
    (success : collect state parent (identifier :: rest) = .ok result) :
    ∃ first tail, join state parent identifier = .ok first ∧ collect first.1 parent rest = .ok tail ∧
      result = (tail.1, first.2 :: tail.2) := by
  cases head : join state parent identifier with
  | error fault => simp [collect, head] at success
  | ok first =>
    cases next : collect first.1 parent rest with
    | error fault => simp [collect, head, next] at success
    | ok tail =>
      simp [collect, head, next] at success
      exact ⟨first, tail, rfl, next, success.symm⟩

theorem collect_history (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (success : collect state parent identifiers = .ok result) : History state result.1 := by
  induction identifiers generalizing state result with
  | nil => simp [collect] at success; cases success; exact .refl
  | cons identifier rest induction =>
    obtain ⟨first, tail, joined, collected, same⟩ := collect_cons_ok _ _ _ _ _ success
    rw [same]
    exact .next (.join joined) (induction first.1 tail collected)

theorem collect_wellFormed (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (valid : WellFormed state) (success : collect state parent identifiers = .ok result) : WellFormed result.1 :=
  (collect_history _ _ _ _ success).wellFormed valid

theorem collect_resources (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (success : collect state parent identifiers = .ok result) : result.1.shared.shared.resources = state.shared.shared.resources := by
  induction identifiers generalizing state result with
  | nil => simp [collect] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, joined, collected, same⟩ := collect_cons_ok _ _ _ _ _ success
    rw [same]
    exact (induction first.1 tail collected).trans (join_resources _ _ _ _ joined)

theorem collect_values (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (valid : WellFormed state) (success : collect state parent identifiers = .ok result) :
    result.2 = List.replicate identifiers.length 0 := by
  induction identifiers generalizing state result with
  | nil => simp [collect] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, joined, collected, same⟩ := collect_cons_ok _ _ _ _ _ success
    have zero := join_zero _ _ _ _ valid joined
    have values := induction first.1 tail (join_wellFormed _ _ _ _ valid joined) collected
    rw [same]
    simp [zero, values, List.replicate_succ]

theorem collect_removes (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (valid : WellFormed state) (success : collect state parent identifiers = .ok result) :
    ∀ identifier ∈ identifiers, result.1.workers identifier = none := by
  induction identifiers generalizing state result with
  | nil => simp
  | cons identifier rest induction =>
    obtain ⟨first, tail, joined, collected, same⟩ := collect_cons_ok _ _ _ _ _ success
    have tailValid := join_wellFormed _ _ _ _ valid joined
    have removed := induction first.1 tail tailValid collected
    have firstRemoved := joined_for_history (identifier := identifier) parent valid joined (collect_history _ _ _ _ collected)
    rw [same]
    intro query member
    simp only [List.mem_cons] at member
    rcases member with own | other
    · subst query; exact firstRemoved.2
    · exact removed query other

theorem collect_frame (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (success : collect state parent identifiers = .ok result) :
    ∀ query, query ∉ identifiers → result.1.workers query = state.workers query := by
  induction identifiers generalizing state result with
  | nil => simp [collect] at success; cases success; simp
  | cons identifier rest induction =>
    obtain ⟨first, tail, joined, collected, same⟩ := collect_cons_ok _ _ _ _ _ success
    obtain ⟨_, _, _, _, _, _, _, _, _, _, firstEq⟩ := join_ok _ _ _ _ joined
    rw [same]
    intro query absent
    have different : query ≠ identifier := by intro equal; exact absent (by simp [equal])
    have outside : query ∉ rest := by intro member; exact absent (by simp [member])
    rw [induction first.1 tail collected query outside, firstEq]
    simp [replace, different]

theorem collect_revokes (state : State) (parent : Nat) (identifiers : List Nat) (result : State × List Word)
    (valid : WellFormed state) (success : collect state parent identifiers = .ok result) :
    ∀ identifier ∈ identifiers, ∃ worker, state.workers identifier = some worker ∧
      Atomics.Revoked result.1.shared worker.handle ∧ Borrowing.Revoked result.1.shared.shared worker.codeLoan ∧
      Borrowing.Revoked result.1.shared.shared worker.stackLoan := by
  induction identifiers generalizing state result with
  | nil => simp
  | cons identifier rest induction =>
    obtain ⟨first, tail, joined, collected, same⟩ := collect_cons_ok _ _ _ _ _ success
    have tailValid := join_wellFormed _ _ _ _ valid joined
    have restRevoked := induction first.1 tail tailValid collected
    have firstRevoked := joined_resources_for_history (identifier := identifier) parent valid joined (collect_history _ _ _ _ collected)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, firstEq⟩ := join_ok _ _ _ _ joined
    rw [same]
    intro query member
    simp only [List.mem_cons] at member
    rcases member with own | other
    · subst query; exact firstRevoked
    · obtain ⟨worker, live, handle, code, stack⟩ := restRevoked query other
      by_cases removed : query = identifier
      · subst query; rw [firstEq] at live; simp [replace] at live
      · exact ⟨worker, by rw [firstEq] at live; simpa [replace, removed] using live, handle, code, stack⟩

theorem collect_enabled (state : State) (identifiers : List Nat) (valid : WellFormed state)
    (distinct : identifiers.Nodup)
    (completed : ∀ identifier ∈ identifiers, ∃ worker, state.workers identifier = some worker ∧ worker.phase = .completed) :
    ∃ result, collect state 0 identifiers = .ok result := by
  induction identifiers generalizing state with
  | nil => exact ⟨(state, []), rfl⟩
  | cons identifier rest induction =>
    obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨worker, live, phase⟩ := completed identifier (by simp)
    obtain ⟨first, joined⟩ := join_enabled state identifier worker valid live phase
    have nextValid := join_wellFormed _ _ _ _ valid joined
    have nextCompleted : ∀ query ∈ rest, ∃ current, first.1.workers query = some current ∧ current.phase = .completed := by
      intro query member
      obtain ⟨current, found, complete⟩ := completed query (by simp [member])
      obtain ⟨_, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ joined
      have different : query ≠ identifier := by intro equal; subst query; exact absent member
      exact ⟨current, by rw [same]; simpa [replace, different] using found, complete⟩
    obtain ⟨tail, collected⟩ := induction first.1 nextValid tailDistinct nextCompleted
    exact ⟨(tail.1, first.2 :: tail.2), by simp [collect, joined, collected]⟩

def liveIds (state : State) : List Nat :=
  (List.range state.nextThread).filter fun identifier => (state.workers identifier).isSome

theorem liveIds_distinct (state : State) : (liveIds state).Nodup :=
  List.Pairwise.filter _ List.nodup_range

theorem liveIds_member (state : State) (valid : WellFormed state) (identifier : Nat) :
    identifier ∈ liveIds state ↔ ∃ worker, state.workers identifier = some worker := by
  constructor
  · intro member
    have present := (List.mem_filter.mp member).2
    cases found : state.workers identifier with
    | none => simp [found] at present
    | some worker => exact ⟨worker, rfl⟩
  · rintro ⟨worker, found⟩
    have below := (valid.2 _ _ found).1
    simp [liveIds, below, found]

theorem collect_all (state : State) (valid : WellFormed state)
    (completed : ∀ identifier worker, state.workers identifier = some worker → worker.phase = .completed) :
    ∃ result, collect state 0 (liveIds state) = .ok result ∧ WellFormed result.1 ∧
      result.2 = List.replicate (liveIds state).length 0 ∧ (∀ identifier, result.1.workers identifier = none) ∧
      result.1.shared.shared.resources = state.shared.shared.resources := by
  have ready : ∀ identifier ∈ liveIds state, ∃ worker, state.workers identifier = some worker ∧ worker.phase = .completed := by
    intro identifier member
    obtain ⟨worker, found⟩ := (liveIds_member state valid identifier).mp member
    exact ⟨worker, found, completed _ _ found⟩
  obtain ⟨result, collected⟩ := collect_enabled state (liveIds state) valid (liveIds_distinct state) ready
  refine ⟨result, collected, collect_wellFormed _ _ _ _ valid collected,
    collect_values _ _ _ _ valid collected, ?_, collect_resources _ _ _ _ collected⟩
  intro identifier
  by_cases member : identifier ∈ liveIds state
  · exact collect_removes _ _ _ _ valid collected identifier member
  · rw [collect_frame _ _ _ _ collected identifier member]
    cases found : state.workers identifier with
    | none => rfl
    | some worker => exact False.elim (member ((liveIds_member state valid identifier).mpr ⟨worker, found⟩))

theorem schedule_liveIds (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result) : liveIds result.1 = liveIds state := by
  unfold liveIds
  rw [schedule_nextThread _ _ _ success]
  apply List.filter_congr
  intro identifier _
  cases before : state.workers identifier with
  | none =>
    cases after : result.1.workers identifier with
    | none => rfl
    | some worker =>
      obtain ⟨previous, live, _⟩ := schedule_origin _ _ _ valid success identifier worker after
      rw [before] at live
      cases live
  | some worker =>
    obtain ⟨current, currentAt, _⟩ := schedule_remaining _ _ _ _ _ valid before success
    simp [currentAt]

end EDSL.OS.CounterThreads
