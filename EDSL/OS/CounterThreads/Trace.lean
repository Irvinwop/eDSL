/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Accounting
import EDSL.OS.CounterThreads.Effects

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

def AllAt (state : State) (address : Word) : Prop :=
  ∀ identifier worker, state.workers identifier = some worker → worker.entry.registers .rdi = address

theorem dispatch_allAt (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (address : Word) (valid : WellFormed state) (allAt : AllAt state address)
    (success : dispatch state identifier = .ok result) : AllAt result.1 address := by
  obtain ⟨selected, advanced, found, selectedOk, same⟩ := dispatch_ok _ _ _ success
  have effect := advance_effect _ _ _ _ valid.1 (valid.2 _ _ found).2 selectedOk
  rw [same]
  intro query worker live
  by_cases own : query = identifier
  · subst query
    simp [replace] at live
    cases live
    have entry : advanced.worker.entry = selected.entry := by cases effect <;> rfl
    rw [entry]
    exact allAt identifier selected found
  · exact allAt query worker (by simpa [replace, own] using live)

/-- An independent counter contract on shared memory: all actually emitted
locked increments contribute once, modulo 2^32, across any successful supplied
dispatch schedule. Other instruction selections do not change OS cells. -/
theorem schedule_counter (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (address : Word) (initial : BitVec 32) (valid : WellFormed state) (allAt : AllAt state address)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok initial)
    (success : schedule state selections = .ok result) :
    loadDWord (toMemory result.1.shared.shared.resources.space) address = .ok (initial + BitVec.ofNat 32 result.2.length) := by
  induction selections generalizing state result initial with
  | nil => simp [schedule] at success; cases success; simpa using observed
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    have tailValid := dispatch_wellFormed _ _ _ valid selected
    have tailAt := dispatch_allAt _ _ _ address valid allAt selected
    obtain ⟨worker, advanced, found, advancedOk, firstEq⟩ := dispatch_ok _ _ _ selected
    have effect := advance_effect _ _ _ _ valid.1 (valid.2 _ _ found).2 advancedOk
    have memory := effect.memory (valid.2 _ _ found).2
    have operand := allAt identifier worker found
    subst first
    cases emission : advanced.event with
    | none =>
      simp only [emission] at memory
      have read : loadDWord (toMemory advanced.shared.shared.resources.space) address = .ok initial := by
        rw [memory]
        exact observed
      have final := induction _ tail initial tailValid tailAt read scheduled
      rw [same]
      simpa [recordEvent, emission] using final
    | some event =>
      simp only [emission] at memory
      have atCell : event.address = address := memory.1.trans operand
      have beforeRead : loadDWord (toMemory state.shared.shared.resources.space) address = .ok event.before := by
        simpa [atCell] using memory.2.2.1
      have oldEq : event.before = initial := Except.ok.inj (beforeRead.symm.trans observed)
      have read : loadDWord (toMemory advanced.shared.shared.resources.space) address = .ok (initial + 1) := by
        simpa only [atCell, memory.2.1, oldEq] using memory.2.2.2
      have final := induction _ tail (initial + 1) tailValid tailAt read scheduled
      have swap := BitVec.add_comm (1 : BitVec 32) (BitVec.ofNat 32 tail.2.length)
      simp only [BitVec.ofNat_eq_ofNat] at swap
      rw [same]
      simpa [recordEvent, emission, BitVec.ofNat_add, BitVec.add_assoc,
        swap] using final

theorem schedule_nextThread (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : result.1.nextThread = state.nextThread := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact (induction _ _ scheduled).trans (dispatch_frame _ _ _ selected).1

theorem schedule_origin (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result)
    (query : Nat) (worker : Worker) (live : result.1.workers query = some worker) :
    ∃ previous, state.workers query = some previous ∧ previous.entry = worker.entry := by
  have afterValid := schedule_wellFormed _ _ _ valid success
  have below := (afterValid.2 _ _ live).1
  rw [schedule_nextThread _ _ _ success] at below
  exact ((schedule_history _ _ _ success).advances valid).2 query below worker live

theorem schedule_event_live (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result) :
    ∀ event ∈ result.2, ∃ worker, result.1.workers event.1 = some worker := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; simp
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    have tailValid := dispatch_wellFormed _ _ _ valid selected
    have tailLive := induction first.1 tail tailValid scheduled
    obtain ⟨worker, advanced, found, advancedOk, firstEq⟩ := dispatch_ok _ _ _ selected
    have firstLive : first.1.workers identifier = some advanced.worker := by rw [firstEq]; simp [replace]
    obtain ⟨current, currentAt, _⟩ := schedule_remaining first.1 rest identifier advanced.worker tail tailValid firstLive scheduled
    rw [same]
    intro event member
    cases emitted : first.2 with
    | none => exact tailLive event (by simpa [recordEvent, emitted] using member)
    | some actual =>
      simp [recordEvent, emitted] at member
      rcases member with own | old
      · subst event; exact ⟨current, currentAt⟩
      · exact tailLive event old

theorem schedule_event_bound (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (valid : WellFormed state) (success : schedule state selections = .ok result) :
    ∀ event ∈ result.2, event.1 < state.nextThread := by
  intro event member
  obtain ⟨worker, live⟩ := schedule_event_live _ _ _ valid success event member
  have below := ((schedule_wellFormed _ _ _ valid success).2 _ _ live).1
  rwa [schedule_nextThread _ _ _ success] at below

end EDSL.OS.CounterThreads
