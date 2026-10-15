/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Scheduling

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

def AllAt (state : State) (address : Word) : Prop :=
  ∀ identifier worker, state.workers identifier = some worker → worker.entry.registers .rdi = address

theorem dispatch_allAt (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (address : Word) (valid : WellFormed state) (allAt : AllAt state address)
    (success : dispatch state identifier = .ok result) : AllAt result.1 address := by
  obtain ⟨selected, live, effect⟩ := dispatch_effect _ _ _ valid success
  cases effect <;> intro query worker found
  all_goals
    by_cases own : query = identifier
    · subst query
      simp [replace] at found
      cases found
      exact allAt identifier selected live
    · exact allAt query worker (by simpa [replace, own] using found)

/-- An independent value-flow contract on actual actor-labeled machine events. -/
inductive ValueChain (address : Word) : BitVec 32 → List (Nat × AtomicEvent) → BitVec 32 → Prop where
  | nil {value} : ValueChain address value [] value
  | cons {old event events final} (atCell : event.2.address = address) (observed : event.2.before = old)
      (tail : ValueChain address event.2.after events final) : ValueChain address old (event :: events) final

/-- Arbitrary successful instruction schedules for a shared cell preserve the
old/new chain. MOV and RET selections contribute no events or shared writes.
The input value is an independently supplied observation of initial memory. -/
theorem schedule_chain (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (address : Word) (old : BitVec 32) (valid : WellFormed state) (allAt : AllAt state address)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok old)
    (success : schedule state selections = .ok result) :
    ∃ final, loadDWord (toMemory result.1.shared.shared.resources.space) address = .ok final ∧
      ValueChain address old result.2 final := by
  induction selections generalizing state result old with
  | nil =>
    simp [schedule] at success
    cases success
    exact ⟨old, observed, .nil⟩
  | cons identifier rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    have tailValue := fun nextOld read => induction first.1 tail nextOld
      (dispatch_wellFormed _ _ _ valid selected)
      (dispatch_allAt _ _ _ address valid allAt selected) read scheduled
    obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ valid selected
    cases effect with
    | preparing _ | returning _ =>
      obtain ⟨final, read, chain⟩ := tailValue old observed
      rw [same]
      exact ⟨final, read, chain⟩
    | @exchanging context shared phase exchangedOk =>
      obtain ⟨handle, authorized, transition⟩ := Atomics.exchange_sound _ _ _ _ _ exchangedOk
      obtain ⟨other, checked, atOperand⟩ := ((valid.2 _ _ live).2).authorized
      have equal := Except.ok.inj (authorized.symm.trans checked)
      subst other
      have atCell := atOperand.trans (allAt identifier worker live)
      have beforeRead := transition.2.2.1
      rw [atCell] at beforeRead
      have beforeValue := Except.ok.inj (beforeRead.symm.trans observed)
      obtain ⟨final, read, chain⟩ := tailValue ((worker.entry.registers .rsi).setWidth 32)
        (by simpa only [atCell] using transition.readback)
      rw [same]
      exact ⟨final, read, .cons (allAt identifier worker live) beforeValue chain⟩

/-- A multiset equality, counting duplicates: initial cell plus all inserted
words equals final cell plus all returned words in the actual RMW trace. -/
theorem ValueChain.conservation {address : Word} {old final : BitVec 32} {events : List (Nat × AtomicEvent)}
    (chain : ValueChain address old events final) :
    List.Perm (old :: events.map (fun event => event.2.after))
      (final :: events.map (fun event => event.2.before)) := by
  induction chain with
  | nil => exact .refl _
  | @cons old event events final _ observed _ induction =>
    simp only [List.map_cons]
    rw [observed]
    exact (List.Perm.cons old induction).trans (.swap _ _ _)

theorem schedule_conservation (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (address : Word) (old : BitVec 32) (valid : WellFormed state) (allAt : AllAt state address)
    (observed : loadDWord (toMemory state.shared.shared.resources.space) address = .ok old)
    (success : schedule state selections = .ok result) :
    ∃ final, loadDWord (toMemory result.1.shared.shared.resources.space) address = .ok final ∧
      List.Perm (old :: result.2.map (fun event => event.2.after))
        (final :: result.2.map (fun event => event.2.before)) := by
  obtain ⟨final, read, chain⟩ := schedule_chain _ _ _ _ _ valid allAt observed success
  exact ⟨final, read, chain.conservation⟩

end EDSL.OS.AtomicThreads
