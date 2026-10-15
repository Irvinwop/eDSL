/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Ready
import EDSL.OS.MutexReplay.Preservation
import EDSL.X86.CodeCheckComplete

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem empty_executionReady (shared : Mutex.State) : ExecutionReady (empty shared) := by
  intro identifier worker live
  simp [empty] at live

theorem executionReady_loanReady (state : State) (ready : ExecutionReady state) : LoanReady state :=
  fun identifier worker live => (ready identifier worker live).loans

/-- The retained records protect both executable bytes and the saved return
word through the actual borrowing history, including their permissions. -/
theorem WorkerExecutionReady.frame {before after : Borrowing.State} {identifier : Nat} {worker : Worker}
    (ready : WorkerExecutionReady before identifier worker) (valid : Borrowing.WellFormed before)
    (history : Borrowing.History before after)
    (codeKept : after.loans worker.codeLoan = before.loans worker.codeLoan)
    (stackKept : after.loans worker.stackLoan = before.loans worker.stackLoan) :
    WorkerExecutionReady after identifier worker := by
  obtain ⟨codeAfter, codeCells⟩ := ready.loans.1.frame valid history codeKept
  obtain ⟨stackAfter, stackCells⟩ := ready.loans.2.1.frame valid history stackKept
  refine ⟨⟨codeAfter, stackAfter, ready.loans.2.2⟩, ?_, ?_, ready.canonical⟩
  · exact agrees_code _ _ _ _ codeCells ready.code
  · exact (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans ready.stack

/-- Updating execution context, phase, and guard preserves the immutable code,
return address, and loan identifiers used by readiness. -/
theorem WorkerExecutionReady.evolved {shared : Borrowing.State} {identifier : Nat} {worker : Worker}
    (ready : WorkerExecutionReady shared identifier worker) (result : Result) :
    WorkerExecutionReady shared identifier (evolved worker result) := by
  exact ⟨ready.loans, ready.code, ready.stack, ready.canonical⟩

/-- Checked spawn establishes the new worker's code and return facts and
retains every prior worker's authority without changing the resource cells. -/
theorem spawn_executionReady (state : State) (start : Start) (after : State)
    (valid : Mutex.WellFormed state.shared) (ready : ExecutionReady state)
    (success : spawn state start = .ok after) : ExecutionReady after := by
  have loans := spawn_loanReady state start after valid (executionReady_loanReady state ready) success
  obtain ⟨_, _, target, code, stack, _, _, _, _, _, executable, returned, canonical,
    _, _, same⟩ := spawn_ok _ _ _ success
  have space : stack.1.shared.resources.space = state.shared.shared.resources.space := by
    simpa only [same] using spawn_space _ _ _ success
  rw [same] at loans ⊢
  intro identifier worker live
  by_cases old : identifier < state.workers.length
  · have before : state.workers[identifier]? = some worker := by
      simpa only [List.getElem?_append_left old] using live
    have original := ready identifier worker before
    refine ⟨loans identifier worker live, ?_, ?_, original.canonical⟩
    · simpa only [space] using original.code
    · simpa only [space] using original.stack
  · have tail := List.getElem?_append_right (Nat.le_of_not_gt old) (l₂ := [
        ⟨start.entry, target, code.2, stack.2, start.entry, .entry, none⟩])
    simp only [tail] at live
    cases index : identifier - state.workers.length with
    | zero =>
      simp [index] at live
      subst worker
      refine ⟨loans identifier _ ?_, ?_, ?_, canonical⟩
      · simp only [tail, index, List.getElem?_cons_zero]
      · simpa only [space] using checkCode_sound _ _ _ executable
      · simpa only [space] using returned
    | succ index => simp [index] at live

/-- A successful dispatch supplies the real protocol history and preserves
the exact loan map, so readiness holds for the selected worker and all peers.
Only initial mutex well-formedness is needed. -/
theorem dispatch_executionReady (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (valid : Mutex.WellFormed state.shared) (ready : ExecutionReady state)
    (success : dispatch state identifier = .ok result) : ExecutionReady result.1 := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  obtain ⟨_, operation, _, performed, _⟩ := advance_ok _ _ _ _ advanced
  have history := (perform_history _ _ _ _ _ performed).borrowing valid
  have loans := (perform_loans _ _ _ _ _ performed).1
  have bound := (List.getElem_of_getElem? live).1
  rw [same]
  intro query current found
  by_cases selected : identifier = query
  · subst query
    rw [List.getElem?_set_self bound] at found
    cases found
    exact ((ready identifier worker live).frame valid.1 history
      (congrFun loans worker.codeLoan) (congrFun loans worker.stackLoan)).evolved output
  · have before : state.workers[query]? = some current := by
      simpa only [List.getElem?_set_ne selected] using found
    exact (ready query current before).frame valid.1 history
      (congrFun loans current.codeLoan) (congrFun loans current.stackLoan)

/-- Readiness composes over the actual successful dispatches. The protocol
invariant and its closure premise supply well-formedness at each prefix. -/
theorem schedule_executionReady (state : State) (config : Mutex.Config) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (valid : Invariant config state)
    (ready : ExecutionReady state) (closed : ClosedUnderTwo config)
    (success : schedule state selections = .ok result) : ExecutionReady result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact ready
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact induction first.1 tail (dispatch_invariant _ _ _ _ valid closed head)
      (dispatch_executionReady _ _ _ valid.shared ready head) next

end EDSL.OS.MutexReplay
