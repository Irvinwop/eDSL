/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Scheduling
import EDSL.OS.Atomics64.Trace

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Actual selected instructions, with every AF choice and optional event.
There is no constructor for supplying an event independently of dispatch. -/
inductive InstructionTrace : State → List Observation → State → Prop where
  | refl {state} : InstructionTrace state [] state
  | next {before first rest after selection}
      (success : dispatch before selection.1 selection.2 = .ok first)
      (tail : InstructionTrace first.1 rest after) :
      InstructionTrace before ((selection, first.2) :: rest) after

theorem schedule_instructions (state : State) (selections : List Selection)
    (result : State × List Observation) (success : schedule state selections = .ok result) :
    InstructionTrace state result.2 result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .refl
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .next selected (induction first.1 tail scheduled)

/-- Every observed event binds the selected actor, stored handle and cell,
actual instruction mask and OR operation. Requests use the lower API's
principal/handle/mask record rather than a parallel unlabeled mask list. -/
theorem InstructionTrace.event_bound {state after : State} {observations : List Observation}
    (trace : InstructionTrace state observations after) (valid : WellFormed state)
    (selection : Selection) (event : Atomics64.Event) (member : (selection, some event) ∈ observations) :
    ∃ before next worker, WellFormed before ∧ before.workers selection.1 = some worker ∧
      dispatch before selection.1 selection.2 = .ok (next, some event) ∧
      Atomics64.logicalDiscard before.shared (principal selection.1) worker.handle
        (worker.entry.registers .rsi) = .ok (next.shared, event) ∧
      event.request = (⟨principal selection.1, worker.handle, worker.entry.registers .rsi⟩ : Atomics64.Request) ∧
      event.cell = worker.cell ∧ event.logical.op = .bor := by
  induction trace with
  | refl => simp at member
  | @next before first rest after chosen selected tail induction =>
    rcases List.mem_cons.mp member with head | member
    · have same := Prod.mk.inj head
      have chosenEq : chosen = selection := same.1.symm
      subst chosen
      have hasEvent : dispatch before selection.1 selection.2 = .ok (first.1, some event) :=
        selected.trans (congrArg Except.ok (Prod.ext rfl same.2.symm))
      obtain ⟨worker, live, operation⟩ := dispatch_atomic_operation _ _ _ _ _ valid hasEvent
      obtain ⟨actual, _, actualAt, _, actor, handle, cell, op, mask, _⟩ :=
        dispatch_atomic_spec _ _ _ _ _ valid hasEvent
      have sameWorker := Option.some.inj (actualAt.symm.trans live)
      subst actual
      exact ⟨before, first.1, worker, valid, live, hasEvent, operation,
        by simp only [Atomics64.Event.request, Atomics64.Request.mk.injEq]; exact ⟨actor, handle, mask⟩,
        cell, op⟩
    · exact induction (dispatch_wellFormed _ _ _ _ valid selected) member

/-- Restriction for modification-order projection. Lifecycle/admin actions
remain in the rich managed History and are not silently erased here. -/
def AllOn (state : State) (cell : Atomics64.CellId64) : Prop :=
  ∀ identifier worker, state.workers identifier = some worker → worker.cell = cell

theorem dispatch_allOn (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (cell : Atomics64.CellId64)
    (valid : WellFormed state) (allOn : AllOn state cell)
    (success : dispatch state identifier af = .ok result) : AllOn result.1 cell := by
  obtain ⟨selected, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect <;> intro query worker found
  all_goals
    by_cases own : query = identifier
    · subst query
      simp [replace] at found
      cases found
      exact allOn identifier selected live
    · exact allOn query worker (by simpa [replace, own] using found)

/-- A dispatch-only schedule on one persistent cell projects to the checked
full64 OR trace. Actual RET is stutter on CURRENT shared RAM; there are no
spawn-time snapshots, administrative operations or mixed-width dispatches. -/
theorem schedule_orTrace (state : State) (selections : List Selection)
    (result : State × List Observation) (identifier : Atomics64.CellId64) (cell : Atomics64.Cell)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell)
    (allOn : AllOn state identifier) (success : schedule state selections = .ok result) :
    Atomics64.OrTrace identifier cell state.shared (events result.2) result.1.shared := by
  induction selections generalizing state result with
  | nil =>
    simp [schedule] at success
    cases success
    exact .refl live
  | cons selection rest induction =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    have keeps := dispatch_keeps _ _ _ _ valid selected
    have nextLive : first.1.shared.cells identifier = some cell := by rw [keeps.2.1]; exact live
    have tailTrace := induction first.1 tail (dispatch_wellFormed _ _ _ _ valid selected)
      nextLive (dispatch_allOn _ _ _ _ _ valid allOn selected) scheduled
    rw [same]
    cases output : first.2 with
    | none =>
      have noEvent : dispatch state selection.1 selection.2 = .ok (first.1, none) :=
        selected.trans (congrArg Except.ok (Prod.ext rfl output))
      have current := dispatch_return_ram _ _ _ _ valid noEvent
      simpa only [events, List.filterMap_cons, output, current] using tailTrace
    | some event =>
      have hasEvent : dispatch state selection.1 selection.2 = .ok (first.1, some event) :=
        selected.trans (congrArg Except.ok (Prod.ext rfl output))
      obtain ⟨worker, workerAt, operation⟩ := dispatch_atomic_operation _ _ _ _ _ valid hasEvent
      obtain ⟨actual, _, actualAt, _, _, _, identity, _⟩ := dispatch_atomic_spec _ _ _ _ _ valid hasEvent
      have sameWorker := Option.some.inj (actualAt.symm.trans workerAt)
      subst actual
      have selectedCell : event.cell = identifier := identity.trans (allOn _ _ workerAt)
      simpa only [events, List.filterMap_cons, output] using
        Atomics64.OrTrace.next operation selectedCell tailTrace

/-- The current-before chain is derived from actual dispatch events, with no
restrictions that masks be disjoint, distinct, nonzero or value-changing. -/
theorem schedule_chain (state : State) (selections : List Selection) (result : State × List Observation)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (initial : Word)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell) (allOn : AllOn state identifier)
    (observed : loadQWord (toMemory state.shared.legacy.shared.resources.space) cell.address = .ok initial)
    (success : schedule state selections = .ok result) :
    ∃ final, loadQWord (toMemory result.1.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      Atomics64.OrChain initial (events result.2) final :=
  (schedule_orTrace _ _ _ _ _ valid live allOn success).chain initial observed

/-- Independent natural-number bit-union contract for arbitrary legal finite
interleavings, using the masks retained in their actual full64 events. -/
theorem schedule_membership (state : State) (selections : List Selection) (result : State × List Observation)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (initial : Word)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell) (allOn : AllOn state identifier)
    (observed : loadQWord (toMemory state.shared.legacy.shared.resources.space) cell.address = .ok initial)
    (success : schedule state selections = .ok result) :
    ∃ final, loadQWord (toMemory result.1.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      ∀ index, Logical64.HasBit final index ↔ Logical64.HasBit initial index ∨
        ∃ event ∈ events result.2, Logical64.HasBit event.logical.mask index :=
  (schedule_orTrace _ _ _ _ _ valid live allOn success).membership initial observed

/-- A successful trace and its independent contract are constructed from
present resources and finite selection counts, without a future-run premise. -/
theorem schedule_enabled_membership (state : State) (selections : List Selection)
    (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (initial : Word)
    (valid : WellFormed state) (live : state.shared.cells identifier = some cell)
    (allOn : AllOn state identifier) (legal : Admissible state selections)
    (observed : loadQWord (toMemory state.shared.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ after observations final,
      schedule state selections = .ok (after, observations) ∧ WellFormed after ∧
      InstructionTrace state observations after ∧
      loadQWord (toMemory after.shared.legacy.shared.resources.space) cell.address = .ok final ∧
      ∀ index, Logical64.HasBit final index ↔ Logical64.HasBit initial index ∨
        ∃ event ∈ events observations, Logical64.HasBit event.logical.mask index := by
  obtain ⟨result, success⟩ := schedule_enabled _ _ valid legal
  obtain ⟨final, read, bits⟩ := schedule_membership _ _ _ _ _ _ valid live allOn observed success
  exact ⟨result.1, result.2, final, success, schedule_wellFormed _ _ _ valid success,
    schedule_instructions _ _ _ success, read, bits⟩

end EDSL.OS.AtomicThreads64
