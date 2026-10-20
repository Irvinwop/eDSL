/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.History

namespace EDSL.OS.Threads
open X86 AddressSpace

theorem finish_enabled (shared : Borrowing.State) (borrower identifier : Nat) (loan : Borrowing.Loan)
    (live : shared.loans identifier = some loan) (owns : loan.borrower = borrower) :
    Borrowing.finishLoan shared borrower identifier =
      .ok { shared with loans := fun query => if query = identifier then none else shared.loans query } := by
  simp [Borrowing.finishLoan, Borrowing.authorize, live, owns]

/-- A completed well-formed worker can be joined by its stored parent. -/
theorem join_enabled (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (completed : worker.phase = .completed context) :
    ∃ result, join state worker.parent identifier = .ok result := by
  obtain ⟨_, data, code, stack, dc, ds, cs, _⟩ := (valid.2 _ _ live).2
  obtain ⟨dataLoan, dataAt, dataOwner, _⟩ := data
  obtain ⟨codeLoan, codeAt, codeOwner, _⟩ := code
  obtain ⟨stackLoan, stackAt, stackOwner, _⟩ := stack
  let dataState : Borrowing.State := { state.shared with
    loans := fun query => if query = worker.dataLoan then none else state.shared.loans query }
  let codeState : Borrowing.State := { dataState with
    loans := fun query => if query = worker.codeLoan then none else dataState.loans query }
  let stackState : Borrowing.State := { codeState with
    loans := fun query => if query = worker.stackLoan then none else codeState.loans query }
  have d : Borrowing.finishLoan state.shared (principal identifier) worker.dataLoan = .ok dataState :=
    finish_enabled state.shared (principal identifier) worker.dataLoan dataLoan dataAt dataOwner
  have c : Borrowing.finishLoan dataState (principal identifier) worker.codeLoan = .ok codeState :=
    finish_enabled _ (principal identifier) worker.codeLoan codeLoan
      ((finishLoan_other d (Ne.symm dc)).trans codeAt) codeOwner
  have s : Borrowing.finishLoan codeState (principal identifier) worker.stackLoan = .ok stackState :=
    finish_enabled _ (principal identifier) worker.stackLoan stackLoan
      ((finishLoan_other c (Ne.symm cs)).trans ((finishLoan_other d (Ne.symm ds)).trans stackAt)) stackOwner
  refine ⟨({ replace state identifier none with shared := stackState }, context.registers .rax), ?_⟩
  have sameParent : ¬worker.parent ≠ worker.parent := by simp
  simp only [join, live, ite_eq_right sameParent, completed, d, c, s, Except.mapError, ok_bind, pure_ok]

/-- Two selections of a load-pending worker execute its two actual instructions.
This is an enabled schedule, not a fairness claim for arbitrary schedules. -/
theorem two_dispatches_complete (state : State) (identifier : Nat) (worker : Worker) (context : Context)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (loading : worker.phase = .loading context) :
    ∃ middle final completedWorker,
      dispatch state identifier = .ok middle ∧ dispatch middle identifier = .ok final ∧
      WellFormed final ∧ final.workers identifier = some completedWorker ∧
      completedWorker.value = worker.value ∧
      completedWorker.phase = .completed (worker.entry.returned worker.value worker.returnAddress) ∧
      ∃ joined, join final worker.parent identifier = .ok joined ∧ joined.2 = worker.value.setWidth 64 := by
  have workerValid := (valid.2 _ _ live).2
  let next : Worker := { worker with phase := .returning (worker.entry.loaded worker.value) }
  let middle := replace state identifier (some next)
  have first : dispatch state identifier = .ok middle := dispatch_loading _ _ _ _ live workerValid loading
  have middleValid := dispatch_wellFormed state identifier middle valid first
  have nextAt : middle.workers identifier = some next := by simp [middle, replace]
  have second := dispatch_returning middle identifier next (worker.entry.loaded worker.value)
    nextAt (middleValid.2 _ _ nextAt).2 rfl
  let done : Worker := { next with phase := .completed (worker.entry.returned worker.value worker.returnAddress) }
  let final := replace middle identifier (some done)
  have finalStep : dispatch middle identifier = .ok final := second
  have finalValid := dispatch_wellFormed middle identifier final middleValid finalStep
  have doneAt : final.workers identifier = some done := by simp [final, replace]
  obtain ⟨joined, joinedAt⟩ := join_enabled final identifier done _ finalValid doneAt rfl
  obtain ⟨actual, actualAt, value⟩ := join_result final worker.parent identifier joined finalValid joinedAt
  have same := Option.some.inj (actualAt.symm.trans doneAt)
  cases same
  exact ⟨middle, final, done, first, finalStep, finalValid, doneAt, rfl, rfl, joined, joinedAt, value⟩

/-- Publication relates the stored worker contract to the actual input memory. -/
theorem spawn_publishes (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    ∃ worker, result.1.workers result.2 = some worker ∧ worker.entry = start.entry ∧
      loadDWord (toMemory state.shared.resources.space) (start.entry.registers .rdi) = .ok worker.value ∧
      worker.phase = .loading start.entry := by
  obtain ⟨value, target, data, code, stack, _, _, _, input, _, _, _, _, _, same⟩ := spawn_ok _ _ _ _ _ success
  rw [same]
  exact ⟨⟨parent, start.entry, value, target, data.2, code.2, stack.2, .loading start.entry⟩,
    by simp [install], rfl, input, rfl⟩

/-- An independent initial word specification determines every successful join
across any admitted intervening environment/scheduler history. -/
theorem spawned_join_value (state : State) (parent : Nat) (start : Start) (available : Bool)
    (spawned : State × Nat) (valid : WellFormed state)
    (created : spawn state parent start available = .ok spawned) (value : BitVec 32)
    (input : loadDWord (toMemory state.shared.resources.space) (start.entry.registers .rdi) = .ok value)
    (beforeJoin : State) (history : History spawned.1 beforeJoin) (joined : State × Word)
    (completed : join beforeJoin parent spawned.2 = .ok joined) : joined.2 = value.setWidth 64 := by
  obtain ⟨worker, live, _, observed, _⟩ := spawn_publishes state parent start available spawned created
  have same := Except.ok.inj (observed.symm.trans input)
  have result := joined_value_for_history history (spawn_wellFormed _ _ _ _ _ valid created)
    spawned.2 worker live parent joined completed
  exact result.trans (congrArg (fun word : BitVec 32 => word.setWidth 64) same)

theorem History.append {before middle after : State} (first : History before middle)
    (last : History middle after) : History before after := by
  induction first with
  | refl => exact last
  | next step _ induction => exact .next step (induction last)

/-- Two separately specified publications retain both results through arbitrary
interleavings and both subsequent collection protocols. -/
theorem two_spawn_join_values (state : State) (firstStart secondStart : Start)
    (first both : State × Nat) (valid : WellFormed state)
    (createdFirst : spawn state 0 firstStart true = .ok first)
    (createdSecond : spawn first.1 0 secondStart true = .ok both)
    (firstValue secondValue : BitVec 32)
    (firstInput : loadDWord (toMemory state.shared.resources.space) (firstStart.entry.registers .rdi) = .ok firstValue)
    (secondInput : loadDWord (toMemory first.1.shared.resources.space) (secondStart.entry.registers .rdi) = .ok secondValue)
    (beforeFirst : State) (interleaving : History both.1 beforeFirst) (joinedFirst : State × Word)
    (collectedFirst : join beforeFirst 0 first.2 = .ok joinedFirst)
    (beforeSecond : State) (tail : History joinedFirst.1 beforeSecond) (joinedSecond : State × Word)
    (collectedSecond : join beforeSecond 0 both.2 = .ok joinedSecond) :
    joinedFirst.2 = firstValue.setWidth 64 ∧ joinedSecond.2 = secondValue.setWidth 64 := by
  refine ⟨spawned_join_value state 0 firstStart true first valid createdFirst firstValue firstInput
    beforeFirst (.next (.spawn createdSecond) interleaving) joinedFirst collectedFirst, ?_⟩
  exact spawned_join_value first.1 0 secondStart true both
    (spawn_wellFormed state 0 firstStart true first valid createdFirst) createdSecond secondValue secondInput
    beforeSecond (interleaving.append (.next (.join collectedFirst) tail)) joinedSecond collectedSecond

/-- Explicit executable scheduler input. Every successful prefix is meaningful;
missing/completed thread selections fail rather than silently disappearing. -/
def schedule : State → List Nat → Except Fault State
  | state, [] => .ok state
  | state, identifier :: rest => do
      let next ← dispatch state identifier
      schedule next rest

theorem schedule_history (state : State) (selections : List Nat) (result : State)
    (success : schedule state selections = .ok result) : History state result := by
  induction selections generalizing state with
  | nil => simp [schedule] at success; subst result; exact .refl
  | cons identifier rest induction =>
    cases selected : dispatch state identifier with
    | error fault => simp [schedule, selected] at success
    | ok next =>
      simp [schedule, selected] at success
      exact .next (.dispatch selected) (induction next success)

theorem schedule_wellFormed (state : State) (selections : List Nat) (result : State)
    (valid : WellFormed state) (success : schedule state selections = .ok result) : WellFormed result :=
  (schedule_history state selections result success).wellFormed valid

/-- An admitted infinite idle trace witnesses that completion cannot follow
from safety alone. No model scheduler fairness assumption is hidden here. -/
theorem idle_trace (state : State) : ∃ trace : Nat → State, trace 0 = state ∧
    ∀ index, Step (trace index) (trace (index + 1)) :=
  ⟨fun _ => state, rfl, fun _ => .idle⟩

end EDSL.OS.Threads
