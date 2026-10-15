/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Dispatch

namespace EDSL.OS.Threads
open X86 AddressSpace

theorem join_ok (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) :
    ∃ (worker : Worker) (context : Context) (data code stack : Borrowing.State),
      state.workers identifier = some worker ∧ worker.parent = parent ∧
      worker.phase = .completed context ∧
      Borrowing.finishLoan state.shared (principal identifier) worker.dataLoan = .ok data ∧
      Borrowing.finishLoan data (principal identifier) worker.codeLoan = .ok code ∧
      Borrowing.finishLoan code (principal identifier) worker.stackLoan = .ok stack ∧
      result = ({ replace state identifier none with shared := stack }, context.registers .rax) := by
  cases found : state.workers identifier with
  | none => simp [join, found] at success
  | some worker =>
    by_cases parentMatches : worker.parent = parent
    · cases phase : worker.phase with
      | loading context => simp [join, found, parentMatches, phase] at success
      | returning context => simp [join, found, parentMatches, phase] at success
      | completed context =>
        cases finishedData : Borrowing.finishLoan state.shared (principal identifier) worker.dataLoan with
        | error fault => simp [join, found, parentMatches, phase, finishedData, Except.mapError] at success
        | ok data =>
          cases finishedCode : Borrowing.finishLoan data (principal identifier) worker.codeLoan with
          | error fault => simp [join, found, parentMatches, phase, finishedData, finishedCode, Except.mapError] at success
          | ok code =>
            cases finishedStack : Borrowing.finishLoan code (principal identifier) worker.stackLoan with
            | error fault =>
              simp [join, found, parentMatches, phase, finishedData, finishedCode, finishedStack, Except.mapError] at success
            | ok stack =>
              simp [join, found, parentMatches, phase, finishedData, finishedCode, finishedStack, Except.mapError] at success
              exact ⟨worker, context, data, code, stack, rfl, parentMatches, phase,
                finishedData, finishedCode, finishedStack, success.symm⟩
    · simp [join, found, parentMatches] at success

theorem join_history (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) : Borrowing.History state.shared result.1.shared := by
  obtain ⟨_, _, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact .next (.finishLoan d) (.next (.finishLoan c) (.next (.finishLoan s) .refl))

theorem join_resources (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) : result.1.shared.resources = state.shared.resources := by
  obtain ⟨_, _, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact (finishLoan_resources s).trans ((finishLoan_resources c).trans (finishLoan_resources d))

theorem join_retains_peer (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result)
    (query : Nat) (worker : Worker) (live : state.workers query = some worker) (different : query ≠ identifier) :
    Retains state.shared result.1.shared worker := by
  obtain ⟨joined, _, _, _, _, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  obtain ⟨_, peerData, peerCode, peerStack, _⟩ := (valid.2 _ _ live).2
  obtain ⟨_, joinedData, joinedCode, joinedStack, _⟩ := (valid.2 _ _ found).2
  rw [same]
  intro loanId member
  have has : ∃ region, HasLoan state.shared query loanId region := by
    rcases member with rfl | rfl | rfl
    · exact ⟨_, peerData⟩
    · exact ⟨_, peerCode⟩
    · exact ⟨_, peerStack⟩
  obtain ⟨_, peerLoan⟩ := has
  exact (finishLoan_other s (peerLoan.different joinedStack different)).trans
    ((finishLoan_other c (peerLoan.different joinedCode different)).trans
      (finishLoan_other d (peerLoan.different joinedData different)))

theorem join_wellFormed (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : WellFormed result.1 := by
  have history := join_history state parent identifier result success
  have peer := join_retains_peer state parent identifier result valid success
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same] at history peer ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro query worker live
  by_cases removed : query = identifier
  · subst query; simp [replace] at live
  · have old : state.workers query = some worker := by simpa [replace, removed] using live
    obtain ⟨below, workerValid⟩ := valid.2 _ _ old
    exact ⟨below, workerValid.frame valid.1 history (peer query worker old removed)⟩

/-- The value comes from retained actual registers. Its agreement with the
published word follows from the worker invariant, not from computing join anew. -/
theorem join_result (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧ result.2 = worker.value.setWidth 64 := by
  obtain ⟨worker, context, _, _, _, found, _, phase, _, _, _, same⟩ := join_ok _ _ _ _ success
  refine ⟨worker, found, ?_⟩
  rw [same]
  exact ((valid.2 _ _ found).2).completed_result phase

/-- Joining releases precisely this worker's loans, leaving all other IDs alone. -/
theorem join_loan_frame (state : State) (parent identifier : Nat) (result : State × Word)
    (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      ∀ query, query ≠ worker.dataLoan → query ≠ worker.codeLoan → query ≠ worker.stackLoan →
        result.1.shared.loans query = state.shared.loans query := by
  obtain ⟨worker, _, _, _, _, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  refine ⟨worker, found, ?_⟩
  rw [same]
  intro query notData notCode notStack
  exact (finishLoan_other s notStack).trans ((finishLoan_other c notCode).trans (finishLoan_other d notData))

theorem join_revokes (state : State) (parent identifier : Nat) (result : State × Word)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      Borrowing.Revoked result.1.shared worker.dataLoan ∧
      Borrowing.Revoked result.1.shared worker.codeLoan ∧
      Borrowing.Revoked result.1.shared worker.stackLoan := by
  obtain ⟨worker, _, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have dataValid := (Borrowing.finishLoan_wellFormed _ _ _ _ valid.1 d).1
  have codeValid := (Borrowing.finishLoan_wellFormed _ _ _ _ dataValid c).1
  have dRevoked := Borrowing.finishLoan_revokes _ _ _ _ valid.1 d
  have cRevoked := Borrowing.finishLoan_revokes _ _ _ _ dataValid c
  have sRevoked := Borrowing.finishLoan_revokes _ _ _ _ codeValid s
  refine ⟨worker, found, ?_, ?_, ?_⟩
  · rw [same]
    exact dRevoked.persists dataValid (.next (.finishLoan c) (.next (.finishLoan s) .refl))
  · rw [same]
    exact cRevoked.persists codeValid (.next (.finishLoan s) .refl)
  · rw [same]
    exact sRevoked

end EDSL.OS.Threads
