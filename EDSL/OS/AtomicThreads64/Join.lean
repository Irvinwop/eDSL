/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Dispatch

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

theorem join_ok (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    ∃ (worker : Worker) (event : Atomics64.Event) (context : Context) (data code stack : Atomics64.State),
      state.workers identifier = some worker ∧ worker.parent = parent ∧
      worker.phase = .completed event context ∧
      Atomics64.close state.shared (principal identifier) worker.handle = .ok data ∧
      Atomics64.finishLoan data (principal identifier) worker.codeLoan = .ok code ∧
      Atomics64.finishLoan code (principal identifier) worker.stackLoan = .ok stack ∧
      result = ({ replace state identifier none with shared := stack }, context) := by
  cases found : state.workers identifier with
  | none => simp [join, found] at success
  | some worker =>
    by_cases parentMatches : worker.parent = parent
    · cases phase : worker.phase with
      | applying context | returning event context => simp [join, found, parentMatches, phase] at success
      | completed event context =>
        cases closed : Atomics64.close state.shared (principal identifier) worker.handle with
        | error fault => simp [join, found, parentMatches, phase, closed, Except.mapError] at success
        | ok data =>
          cases finishedCode : Atomics64.finishLoan data (principal identifier) worker.codeLoan with
          | error fault => simp [join, found, parentMatches, phase, closed, finishedCode, Except.mapError] at success
          | ok code =>
            cases finishedStack : Atomics64.finishLoan code (principal identifier) worker.stackLoan with
            | error fault => simp [join, found, parentMatches, phase, closed, finishedCode,
                finishedStack, Except.mapError] at success
            | ok stack =>
              simp [join, found, parentMatches, phase, closed, finishedCode, finishedStack, Except.mapError] at success
              exact ⟨worker, event, context, data, code, stack, rfl, parentMatches, phase,
                closed, finishedCode, finishedStack, success.symm⟩
    · simp [join, found, parentMatches] at success

theorem join_history (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    Atomics64.History state.shared [none, none, none] result.1.shared := by
  obtain ⟨_, _, _, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact .next (.close d) (.next (.finishLoan c) (.next (.finishLoan s) .refl))

/-- Join preserves CURRENT memory, permissions, allocation/ownership metadata
and the persistent cell registry, including values written by peers after RET. -/
theorem join_resources (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    result.1.shared.legacy.shared.resources = state.shared.legacy.shared.resources ∧
      result.1.shared.cells = state.shared.cells := by
  obtain ⟨_, _, _, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨(finishLoan_frames s).2.2.trans ((finishLoan_frames c).2.2.trans
    (congrArg (fun legacy => legacy.shared.resources) (close_frames d).1)),
    (finishLoan_frames s).2.1.trans ((finishLoan_frames c).2.1.trans (close_frames d).2)⟩

theorem join_retains_peer (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result)
    (query : Nat) (worker : Worker) (live : state.workers query = some worker) (different : query ≠ identifier) :
    Retains state.shared result.1.shared worker := by
  have resources := join_resources _ _ _ _ success
  obtain ⟨joined, _, _, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have peer := (valid.2 _ _ live).2
  have other := (valid.2 _ _ found).2
  rw [same] at resources ⊢
  refine ⟨?_, congrFun resources.2 _, ?_, ?_⟩
  · change stack.handles worker.handle = state.shared.handles worker.handle
    rw [(finishLoan_frames s).1, (finishLoan_frames c).1]
    exact close_other d (peer.handle.different other.handle different)
  · exact (finishLoan_other s (peer.code.different other.stack different)).trans
      ((finishLoan_other c (peer.code.different other.code different)).trans
        (congrArg (fun legacy => legacy.shared.loans worker.codeLoan) (close_frames d).1))
  · exact (finishLoan_other s (peer.stack.different other.stack different)).trans
      ((finishLoan_other c (peer.stack.different other.code different)).trans
        (congrArg (fun legacy => legacy.shared.loans worker.stackLoan) (close_frames d).1))

theorem join_wellFormed (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) : WellFormed result.1 := by
  have history := join_history _ _ _ _ success
  have peers := join_retains_peer _ _ _ _ valid success
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same] at history peers ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro query worker live
  by_cases removed : query = identifier
  · subst query; simp [replace] at live
  · have beforeAt : state.workers query = some worker := by simpa [replace, removed] using live
    exact ⟨(valid.2 _ _ beforeAt).1,
      ((valid.2 _ _ beforeAt).2).frame valid.1 history (peers query worker beforeAt removed)⟩

/-- JOIN returns the completed private context; all GPRs except RSP retain
entry values. In particular RAX is not the fetched-old event value. -/
theorem join_result (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker event, state.workers identifier = some worker ∧ worker.captured = some event ∧
      result.2.registers .rax = worker.entry.registers .rax ∧
      result.2.registers .rsp = worker.entry.registers .rsp + 8 ∧
      result.2.rip = worker.returnAddress ∧
      ∀ register, register ≠ .rsp → result.2.registers register = worker.entry.registers register := by
  obtain ⟨worker, event, context, _, _, _, found, _, phase, _, _, _, same⟩ := join_ok _ _ _ _ success
  refine ⟨worker, event, found, by simp [Worker.captured, phase], ?_⟩
  rw [same]
  exact ((valid.2 _ _ found).2).completed_result phase

def dropLoan (state : Atomics64.State) (identifier : Nat) : Atomics64.State :=
  { state with legacy := { state.legacy with shared := { state.legacy.shared with
      loans := fun query => if query = identifier then none else state.legacy.shared.loans query } } }

theorem finishLoan_success (state : Atomics64.State) (borrower identifier : Nat)
    (loan : Borrowing.Loan) (live : state.legacy.shared.loans identifier = some loan)
    (actor : loan.borrower = borrower) :
    Atomics64.finishLoan state borrower identifier = .ok (dropLoan state identifier) := by
  simp [Atomics64.finishLoan, Atomics.finishLoan, Borrowing.finishLoan, Borrowing.authorize,
    live, actor, dropLoan, Except.mapError]

/-- Completion still pins the resources needed to join. No future-success
premise or raw environment close can replace this present-resource proof. -/
theorem join_enabled (state : State) (identifier : Nat) (worker : Worker)
    (event : Atomics64.Event) (context : Context) (valid : WellFormed state)
    (live : state.workers identifier = some worker) (completed : worker.phase = .completed event context) :
    ∃ result, join state 0 identifier = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  obtain ⟨handle, cell, authorized, _, _⟩ := workerValid.authorized valid.1
  have closed : Atomics64.close state.shared (principal identifier) worker.handle =
      .ok (Atomics64.removeHandle state.shared worker.handle) := by
    simp [Atomics64.close, authorized]
  obtain ⟨codeLoan, codeAt, codeActor, _⟩ := workerValid.code
  obtain ⟨stackLoan, stackAt, stackActor, _⟩ := workerValid.stack
  have codeAtAfter : (Atomics64.removeHandle state.shared worker.handle).legacy.shared.loans worker.codeLoan =
      some codeLoan := codeAt
  have finishedCode := finishLoan_success _ _ _ codeLoan codeAtAfter codeActor
  have stackAtAfter : (dropLoan (Atomics64.removeHandle state.shared worker.handle) worker.codeLoan).legacy.shared.loans
      worker.stackLoan = some stackLoan := by
    rw [finishLoan_other finishedCode workerValid.distinct.symm]
    exact stackAt
  have finishedStack := finishLoan_success _ _ _ stackLoan stackAtAfter stackActor
  exact ⟨({ replace state identifier none with shared := dropLoan (dropLoan (Atomics64.removeHandle state.shared worker.handle) worker.codeLoan) worker.stackLoan }, context),
    by simp [join, live, workerValid.parent, completed, closed, finishedCode, finishedStack, Except.mapError]⟩

/-- Only the joined worker is removed. Peer private contexts and the thread
frontier stay exactly current. -/
theorem join_workers (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    result.1.workers identifier = none ∧ result.1.nextThread = state.nextThread ∧
      ∀ query, query ≠ identifier → result.1.workers query = state.workers query := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨by simp [replace], rfl, fun query different => by simp [replace, different]⟩

/-- The handle and both loans are individually revoked after JOIN. Their
monotone IDs cannot silently become another worker's resources. -/
theorem join_revokes (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      Atomics64.HandleRevoked result.1.shared worker.handle ∧
      Borrowing.Revoked result.1.shared.legacy.shared worker.codeLoan ∧
      Borrowing.Revoked result.1.shared.legacy.shared worker.stackLoan := by
  obtain ⟨worker, _, _, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have dataValid := Atomics64.close_wellFormed _ _ _ _ valid.1 d
  have codeValid := Atomics64.finishLoan_wellFormed _ _ _ _ dataValid c
  have later : Atomics64.History data [none, none] stack :=
    .next (.finishLoan c) (.next (.finishLoan s) .refl)
  refine ⟨worker, found, ?_, ?_, ?_⟩
  · rw [same]
    exact later.handle_revoked (Atomics64.close_revokes _ _ _ _ valid.1 d)
  · rw [same]
    exact Atomics64.finished_for_history _ _ dataValid c (.next (.finishLoan s) .refl)
  · rw [same]
    exact Atomics64.finished_for_history _ _ codeValid s .refl

/-- Every unrelated handle and loan is unchanged, including resources not
owned by another worker. The registry of persistent cells is unchanged too. -/
theorem join_only_resources (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      (∀ query, query ≠ worker.handle → result.1.shared.handles query = state.shared.handles query) ∧
      (∀ query, query ≠ worker.codeLoan → query ≠ worker.stackLoan →
        result.1.shared.legacy.shared.loans query = state.shared.legacy.shared.loans query) ∧
      result.1.shared.cells = state.shared.cells := by
  obtain ⟨worker, _, _, _, _, _, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  refine ⟨worker, found, ?_, ?_, (join_resources _ _ _ _ success).2⟩
  · intro query different
    rw [same]
    change _ = state.shared.handles query
    rw [(finishLoan_frames s).1, (finishLoan_frames c).1]
    exact close_other d different
  · intro query notCode notStack
    rw [same]
    exact (finishLoan_other s notStack).trans ((finishLoan_other c notCode).trans
      (congrArg (fun legacy => legacy.shared.loans query) (close_frames d).1))

end EDSL.OS.AtomicThreads64
