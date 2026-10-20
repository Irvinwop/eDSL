/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Dispatch

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

theorem join_ok (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) :
    ∃ (worker : Worker) (data code stack : Atomics.State), state.workers identifier = some worker ∧
      worker.parent = parent ∧ worker.phase = .completed ∧
      Atomics.close state.shared (principal identifier) worker.handle = .ok data ∧
      Atomics.finishLoan data (principal identifier) worker.codeLoan = .ok code ∧
      Atomics.finishLoan code (principal identifier) worker.stackLoan = .ok stack ∧
      result = ({ replace state identifier none with shared := stack }, worker.context.registers .rax) := by
  cases found : state.workers identifier with
  | none => simp [join, found] at success
  | some worker =>
    by_cases parentMatches : worker.parent = parent
    · by_cases phase : worker.phase = .completed
      · cases closed : Atomics.close state.shared (principal identifier) worker.handle with
        | error fault => simp [join, found, parentMatches, phase, closed, Except.mapError] at success
        | ok data =>
          cases finishedCode : Atomics.finishLoan data (principal identifier) worker.codeLoan with
          | error fault => simp [join, found, parentMatches, phase, closed, finishedCode, Except.mapError] at success
          | ok code =>
            cases finishedStack : Atomics.finishLoan code (principal identifier) worker.stackLoan with
            | error fault => simp [join, found, parentMatches, phase, closed, finishedCode, finishedStack, Except.mapError] at success
            | ok stack =>
              simp [join, found, parentMatches, phase, closed, finishedCode, finishedStack, Except.mapError] at success
              exact ⟨worker, data, code, stack, rfl, parentMatches, phase, closed, finishedCode, finishedStack, success.symm⟩
      · simp [join, found, parentMatches, phase] at success
    · simp [join, found, parentMatches] at success

theorem join_history (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) : Atomics.History state.shared result.1.shared := by
  obtain ⟨_, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact .next (.close d) (.next (.finishLoan c) (.next (.finishLoan s) .refl))

theorem join_resources (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) : result.1.shared.shared.resources = state.shared.shared.resources := by
  obtain ⟨_, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact (finishLoan_resources s).trans ((finishLoan_resources c).trans
    (congrArg (fun shared => shared.resources) (close_shared d)))

theorem join_retains_peer (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result)
    (query : Nat) (worker : Worker) (live : state.workers query = some worker) (different : query ≠ identifier) :
    Retains state.shared result.1.shared worker := by
  obtain ⟨joined, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have peer := (valid.2 _ _ live).2
  have other := (valid.2 _ _ found).2
  rw [same]
  refine ⟨?_, ?_, ?_⟩
  · change stack.handles worker.handle = state.shared.handles worker.handle
    rw [finishLoan_handles s, finishLoan_handles c]
    exact close_other d (peer.handle.different other.handle different)
  · exact (finishLoan_other s (peer.code.different other.stack different)).trans
      ((finishLoan_other c (peer.code.different other.code different)).trans
        (congrArg (fun shared => shared.loans worker.codeLoan) (close_shared d)))
  · exact (finishLoan_other s (peer.stack.different other.stack different)).trans
      ((finishLoan_other c (peer.stack.different other.code different)).trans
        (congrArg (fun shared => shared.loans worker.stackLoan) (close_shared d)))

theorem join_wellFormed (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : WellFormed result.1 := by
  have history := join_history _ _ _ _ success
  have peers := join_retains_peer _ _ _ _ valid success
  obtain ⟨_, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same] at history peers ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro query worker live
  by_cases removed : query = identifier
  · subst query; simp [replace] at live
  · have beforeAt : state.workers query = some worker := by simpa [replace, removed] using live
    exact ⟨(valid.2 _ _ beforeAt).1, ((valid.2 _ _ beforeAt).2).frame valid.1 history (peers query worker beforeAt removed)⟩

theorem join_zero (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : result.2 = 0 := by
  obtain ⟨worker, _, _, _, found, _, phase, _, _, _, same⟩ := join_ok _ _ _ _ success
  have privateContext := ((valid.2 _ _ found).2).privateContext
  simp only [PrivateValid, phase] at privateContext
  rw [same]
  exact privateContext.2.2.2.2.2

theorem join_revokes (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧ Atomics.Revoked result.1.shared worker.handle ∧
      Borrowing.Revoked result.1.shared.shared worker.codeLoan ∧ Borrowing.Revoked result.1.shared.shared worker.stackLoan := by
  obtain ⟨worker, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have dataValid := Atomics.close_wellFormed _ _ _ _ valid.1 d
  have codeValid := Atomics.finishLoan_wellFormed _ _ _ _ dataValid c
  have hRevoked := Atomics.close_revokes _ _ _ _ valid.1 d
  have cRevoked := finishLoan_revokes dataValid c
  have sRevoked := finishLoan_revokes codeValid s
  refine ⟨worker, found, ?_, ?_, ?_⟩
  · rw [same]
    exact hRevoked.persists (.next (.finishLoan c) (.next (.finishLoan s) .refl))
  · rw [same]
    exact cRevoked.persists codeValid.shared ((Atomics.History.next (.finishLoan s) .refl).borrowing)
  · rw [same]
    exact sRevoked

theorem finishLoan_enabled (state : Atomics.State) (borrower identifier : Nat) (loan : Borrowing.Loan)
    (live : state.shared.loans identifier = some loan) (actor : loan.borrower = borrower) :
    ∃ after, Atomics.finishLoan state borrower identifier = .ok after := by
  refine ⟨{ state with shared := { state.shared with loans := fun query =>
    if query = identifier then none else state.shared.loans query } }, ?_⟩
  simp [Atomics.finishLoan, Borrowing.finishLoan, Borrowing.authorize, live, actor, Except.mapError]

theorem join_enabled (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker) (completed : worker.phase = .completed) :
    ∃ result, join state 0 identifier = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  obtain ⟨handle, authorized, _⟩ := workerValid.authorized
  let data : Atomics.State := { state.shared with handles := fun query => if query = worker.handle then none else state.shared.handles query }
  have d : Atomics.close state.shared (principal identifier) worker.handle = .ok data := by simp [Atomics.close, authorized, data]
  obtain ⟨codeLoan, codeAt, codeActor, _⟩ := workerValid.code
  have codeAfter : data.shared.loans worker.codeLoan = some codeLoan := by rw [close_shared d]; exact codeAt
  obtain ⟨code, c⟩ := finishLoan_enabled data _ _ codeLoan codeAfter codeActor
  obtain ⟨stackLoan, stackAt, stackActor, _⟩ := workerValid.stack
  have stackAfter : code.shared.loans worker.stackLoan = some stackLoan :=
    (finishLoan_other c (Ne.symm workerValid.distinct)).trans
      ((congrArg (fun shared => shared.loans worker.stackLoan) (close_shared d)).trans stackAt)
  obtain ⟨stack, s⟩ := finishLoan_enabled code _ _ stackLoan stackAfter stackActor
  exact ⟨({ replace state identifier none with shared := stack }, worker.context.registers .rax), by
    simp [join, live, workerValid.parent, completed, d, c, s, Except.mapError]⟩

end EDSL.OS.CounterThreads
