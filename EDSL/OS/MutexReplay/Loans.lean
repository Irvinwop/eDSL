/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Cohort
import EDSL.OS.MutexReplay.ProtocolFrame
import EDSL.OS.Threads.Framing

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- The two retained identifiers authorize the worker's actual code and return
stack. These are live records, rather than a check of the final loan state. -/
def WorkerLoanReady (shared : Borrowing.State) (identifier : Nat) (worker : Worker) : Prop :=
  Threads.HasLoan shared identifier worker.codeLoan (codeRegion worker.entry) ∧
  Threads.HasLoan shared identifier worker.stackLoan (Threads.stackRegion worker.entry) ∧
  worker.codeLoan ≠ worker.stackLoan

/-- Logical worker identities are immutable cohort indices. Publicly constructed
states need not satisfy this property; checked spawn histories establish it. -/
def LoanReady (state : State) : Prop :=
  ∀ identifier worker, state.workers[identifier]? = some worker →
    WorkerLoanReady state.shared.shared identifier worker

theorem empty_loanReady (shared : Mutex.State) : LoanReady (empty shared) := by
  intro identifier worker live
  simp [empty] at live

private theorem readBorrow_loans {before : Mutex.State} {lender borrower : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Mutex.State × Nat}
    (success : Mutex.readBorrow before lender ticket borrower region = .ok result) :
    result.2 = before.shared.nextLoan ∧
    result.1.shared.nextLoan = before.shared.nextLoan + 1 ∧
    result.1.shared.loans result.2 = some ⟨ticket, lender, borrower, region⟩ := by
  obtain ⟨_, shared, borrowed, same⟩ := Mutex.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, _, _, _, _, shape⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ borrowed
  rw [same, shape]
  simp [Borrowing.installLoan]

private theorem hasLoan_readBorrow {before : Mutex.State} {lender borrower identifier loanId : Nat}
    {ticket : Ownership.Ticket} {region owned : Region} {result : Mutex.State × Nat}
    (valid : Mutex.WellFormed before)
    (success : Mutex.readBorrow before lender ticket borrower region = .ok result)
    (ready : Threads.HasLoan before.shared identifier loanId owned) :
    Threads.HasLoan result.1.shared identifier loanId owned := by
  obtain ⟨_, shared, borrowed, same⟩ := Mutex.readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨loan, live, actor, location⟩ := ready
  rw [same]
  exact ⟨loan, Threads.readBorrow_preserves valid.1 borrowed _ _ live, actor, location⟩

private theorem workerLoanReady_readBorrow {before : Mutex.State} {lender borrower identifier : Nat}
    {ticket : Ownership.Ticket} {region : Region} {result : Mutex.State × Nat} {worker : Worker}
    (valid : Mutex.WellFormed before)
    (success : Mutex.readBorrow before lender ticket borrower region = .ok result)
    (ready : WorkerLoanReady before.shared identifier worker) :
    WorkerLoanReady result.1.shared identifier worker :=
  ⟨hasLoan_readBorrow valid success ready.1,
    hasLoan_readBorrow valid success ready.2.1, ready.2.2⟩

/-- Both new loans come from the real checked spawn operations. Well-formedness
puts old live identifiers below the allocation frontier, so neither borrow
overwrites any prior worker's authority. -/
theorem spawn_loanReady (state : State) (start : Start) (after : State)
    (valid : Mutex.WellFormed state.shared) (ready : LoanReady state)
    (success : spawn state start = .ok after) : LoanReady after := by
  obtain ⟨_, _, target, code, stack, _, _, _, _, _, _, _, _, borrowedCode, borrowedStack, same⟩ :=
    spawn_ok _ _ _ success
  have codeValid := Mutex.readBorrow_wellFormed _ _ _ _ _ _ valid borrowedCode
  have codeShape := readBorrow_loans borrowedCode
  have stackShape := readBorrow_loans borrowedStack
  have codeLoan : Threads.HasLoan code.1.shared state.workers.length code.2 (codeRegion start.entry) :=
    ⟨_, codeShape.2.2, rfl, rfl⟩
  have stackLoan : Threads.HasLoan stack.1.shared state.workers.length stack.2 (Threads.stackRegion start.entry) :=
    ⟨_, stackShape.2.2, rfl, rfl⟩
  have distinct : code.2 ≠ stack.2 := by
    have firstId := codeShape.1
    have nextId := codeShape.2.1
    have secondId := stackShape.1
    omega
  rw [same]
  intro identifier worker live
  by_cases old : identifier < state.workers.length
  · have before : state.workers[identifier]? = some worker := by
      simpa only [List.getElem?_append_left old] using live
    exact workerLoanReady_readBorrow codeValid borrowedStack
      (workerLoanReady_readBorrow valid borrowedCode (ready identifier worker before))
  · have tail := List.getElem?_append_right (Nat.le_of_not_gt old) (l₂ := [
        ⟨start.entry, target, code.2, stack.2, start.entry, .entry, none⟩])
    simp only [tail] at live
    cases index : identifier - state.workers.length with
    | zero =>
      have identity : identifier = state.workers.length := by omega
      simp [index] at live
      subst worker
      subst identifier
      exact ⟨hasLoan_readBorrow codeValid borrowedStack codeLoan, stackLoan, distinct⟩
    | succ index => simp [index] at live

private theorem workerLoanReady_frame {before after : Borrowing.State} {identifier : Nat} {worker : Worker}
    (ready : WorkerLoanReady before identifier worker) (loans : after.loans = before.loans) :
    WorkerLoanReady after identifier worker := by
  simpa only [WorkerLoanReady, Threads.HasLoan, loans] using ready

/-- Replay preserves the entire loan map and the selected worker's immutable
entry and loan identifiers, including on acquisition, stores, and release. -/
theorem dispatch_loanReady (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (ready : LoanReady state) (success : dispatch state identifier = .ok result) :
    LoanReady result.1 := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  obtain ⟨_, operation, _, performed, _⟩ := advance_ok _ _ _ _ advanced
  have loans := (perform_loans _ _ _ _ _ performed).1
  have bound := (List.getElem_of_getElem? live).1
  rw [same]
  intro query current found
  by_cases selected : identifier = query
  · subst query
    rw [List.getElem?_set_self bound] at found
    cases found
    have retained := workerLoanReady_frame (ready identifier worker live) loans
    simpa only [WorkerLoanReady, evolved] using retained
  · have before : state.workers[query]? = some current := by
      simpa only [List.getElem?_set_ne selected] using found
    exact workerLoanReady_frame (ready query current before) loans

theorem schedule_loanReady (state : State) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (ready : LoanReady state)
    (success : schedule state selections = .ok result) : LoanReady result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact ready
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact induction first.1 tail (dispatch_loanReady _ _ _ ready head) next

/-- Readiness for a suffix retains its original principal indices during
recursive collection. No separate global uniqueness assumption is required. -/
def ReadyFrom (shared : Mutex.State) (firstId : Nat) (workers : List Worker) : Prop :=
  ∀ offset worker, workers[offset]? = some worker →
    WorkerLoanReady shared.shared (firstId + offset) worker

private theorem finishLoan_enabled (shared : Mutex.State) (borrower loanId : Nat) (loan : Borrowing.Loan)
    (live : shared.shared.loans loanId = some loan) (actor : loan.borrower = borrower) :
    ∃ after, Mutex.finishLoan shared borrower loanId = .ok after := by
  refine ⟨{ shared with shared := { shared.shared with loans := fun query =>
    if query = loanId then none else shared.shared.loans query } }, ?_⟩
  simp [Mutex.finishLoan, Borrowing.finishLoan, Borrowing.authorize, live, actor, Except.mapError]

private theorem finishLoan_other {before after : Mutex.State} {borrower loanId query : Nat}
    (success : Mutex.finishLoan before borrower loanId = .ok after) (different : query ≠ loanId) :
    after.shared.loans query = before.shared.loans query := by
  obtain ⟨_, finished, same⟩ := Mutex.finishLoan_ok _ _ _ _ success
  rw [same]
  exact Threads.finishLoan_other finished different

private theorem hasLoan_finishLoan {before after : Mutex.State} {borrower removed identifier loanId : Nat}
    {region : Region} (ready : Threads.HasLoan before.shared identifier loanId region)
    (success : Mutex.finishLoan before borrower removed = .ok after) (different : loanId ≠ removed) :
    Threads.HasLoan after.shared identifier loanId region := by
  obtain ⟨loan, live, actor, location⟩ := ready
  exact ⟨loan, (finishLoan_other success different).trans live, actor, location⟩

/-- Finishing one worker cannot revoke a later worker's loans: a live record
has just one borrower, and distinct indices have distinct principals. -/
theorem finishLoans_enabled (shared : Mutex.State) (firstId : Nat) (workers : List Worker)
    (ready : ReadyFrom shared firstId workers) :
    ∃ after, finishLoans shared firstId workers = .ok after := by
  induction workers generalizing shared firstId with
  | nil => exact ⟨shared, rfl⟩
  | cons worker rest induction =>
    have own : WorkerLoanReady shared.shared firstId worker := by
      simpa only [Nat.add_zero] using ready 0 worker (by simp)
    obtain ⟨codeRecord, codeLive, codeActor, _⟩ := own.1
    obtain ⟨code, codeDone⟩ := finishLoan_enabled shared _ _ codeRecord codeLive codeActor
    have stackReady := hasLoan_finishLoan own.2.1 codeDone (Ne.symm own.2.2)
    obtain ⟨stackRecord, stackLive, stackActor, _⟩ := stackReady
    obtain ⟨stack, stackDone⟩ := finishLoan_enabled code _ _ stackRecord stackLive stackActor
    have tailReady : ReadyFrom stack (firstId + 1) rest := by
      intro offset peer live
      have original := ready (offset + 1) peer (by simpa using live)
      have different : firstId + (offset + 1) ≠ firstId := by omega
      have codeAfter : WorkerLoanReady code.shared (firstId + (offset + 1)) peer :=
        ⟨hasLoan_finishLoan original.1 codeDone (original.1.different own.1 different),
          hasLoan_finishLoan original.2.1 codeDone (original.2.1.different own.1 different),
          original.2.2⟩
      have stackAfter : WorkerLoanReady stack.shared (firstId + (offset + 1)) peer :=
        ⟨hasLoan_finishLoan codeAfter.1 stackDone (original.1.different own.2.1 different),
          hasLoan_finishLoan codeAfter.2.1 stackDone (original.2.1.different own.2.1 different),
          original.2.2⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using stackAfter
    obtain ⟨after, finished⟩ := induction stack (firstId + 1) tailReady
    exact ⟨after, by simp [finishLoans, codeDone, stackDone, finished, Except.mapError]⟩

/-- Completion plus authority established by checked spawn and retained by
replay suffices for successful collection. No final loan checker or assumption
of a successful finishLoans call is needed. -/
theorem collect_enabled (state : State) (done : completed state = true) (ready : LoanReady state) :
    ∃ collected, collect state = .ok collected := by
  have fromZero : ReadyFrom state.shared 0 state.workers := by
    simpa only [ReadyFrom, LoanReady, Nat.zero_add] using ready
  obtain ⟨shared, finished⟩ := finishLoans_enabled state.shared 0 state.workers fromZero
  exact ⟨(shared, state.workers.map fun worker => worker.context.registers .rax), by
    simp [collect, done, finished]⟩

/-- The identifiers retained by the cohort, irrespective of worker phase. -/
def cohortLoanIds (workers : List Worker) : List Nat :=
  workers.flatMap fun worker => [worker.codeLoan, worker.stackLoan]

private theorem finishLoan_loans {before after : Mutex.State} {borrower removed : Nat}
    (success : Mutex.finishLoan before borrower removed = .ok after) (query : Nat) :
    after.shared.loans query = if query = removed then none else before.shared.loans query := by
  obtain ⟨_, finished, same⟩ := Mutex.finishLoan_ok _ _ _ _ success
  obtain ⟨_, _, shape⟩ := Borrowing.finishLoan_ok _ _ _ _ finished
  rw [same, shape]

/-- Collection revokes exactly the retained code/stack identifiers. The
statement covers every other loan record, including records outside the cohort. -/
theorem finishLoans_loans (shared : Mutex.State) (firstId : Nat) (workers : List Worker)
    (after : Mutex.State) (success : finishLoans shared firstId workers = .ok after) :
    ∀ query, after.shared.loans query =
      if query ∈ cohortLoanIds workers then none else shared.shared.loans query := by
  induction workers generalizing shared firstId after with
  | nil =>
    simp [finishLoans] at success
    cases success
    intro query
    simp [cohortLoanIds]
  | cons worker rest induction =>
    cases code : Mutex.finishLoan shared (principal firstId) worker.codeLoan with
    | error fault => simp [finishLoans, code, Except.mapError] at success
    | ok first =>
      cases stack : Mutex.finishLoan first (principal firstId) worker.stackLoan with
      | error fault => simp [finishLoans, code, stack, Except.mapError] at success
      | ok second =>
        simp [finishLoans, code, stack, Except.mapError] at success
        intro query
        rw [induction second (firstId + 1) after success query,
          finishLoan_loans stack query, finishLoan_loans code query]
        by_cases isCode : query = worker.codeLoan <;>
          by_cases isStack : query = worker.stackLoan <;>
          simp [cohortLoanIds, isCode, isStack]

theorem collect_loans (state : State) (collected : Mutex.State × List Word)
    (success : collect state = .ok collected) :
    ∀ query, collected.1.shared.loans query =
      if query ∈ cohortLoanIds state.workers then none else state.shared.shared.loans query :=
  finishLoans_loans _ _ _ _ (collect_ok _ _ success).2.1

theorem collect_revokes (state : State) (collected : Mutex.State × List Word)
    (success : collect state = .ok collected) (loanId : Nat)
    (retained : loanId ∈ cohortLoanIds state.workers) : collected.1.shared.loans loanId = none := by
  simpa only [retained, ↓reduceIte] using collect_loans _ _ success loanId

theorem collect_retains (state : State) (collected : Mutex.State × List Word)
    (success : collect state = .ok collected) (loanId : Nat)
    (unrelated : loanId ∉ cohortLoanIds state.workers) :
    collected.1.shared.loans loanId = state.shared.shared.loans loanId := by
  simpa only [unrelated, ↓reduceIte] using collect_loans _ _ success loanId

end EDSL.OS.MutexReplay
