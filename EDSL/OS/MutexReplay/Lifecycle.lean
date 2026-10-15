/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Safety

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

theorem spawn_history (state : State) (start : Start) (after : State)
    (success : spawn state start = .ok after) : Mutex.History state.shared after.shared := by
  by_cases running : started state = true
  · simp [spawn, running] at success
  · cases registered : Mutex.registered state.shared with
    | error fault => simp [spawn, running, registered, Except.mapError] at success
    | ok record =>
      by_cases owner : record.config.owner = 0
      · by_cases held : record.holder.isSome = true
        · simp [spawn, running, registered, owner, held, Except.mapError] at success
        · by_cases operands : start.entry.registers .rdi ≠ record.config.lockAddress ∨
              start.entry.registers .rsi ≠ record.config.dataAddress
          · simp [spawn, running, registered, owner, held, operands, Except.mapError] at success
          · by_cases executable : checkCode (toMemory state.shared.shared.resources.space) start.entry.rip bytes = true
            · cases target : readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp) with
              | error fault => simp [spawn, running, registered, owner, held, operands, executable, target, Except.mapError] at success
              | ok address =>
                by_cases canonical : X86.canonical address = true
                · cases code : Mutex.readBorrow state.shared 0 start.codeTicket
                      (principal state.workers.length) (codeRegion start.entry) with
                  | error fault => simp [spawn, running, registered, owner, held, operands, executable, target, canonical, code, Except.mapError] at success
                  | ok first =>
                    cases stack : Mutex.readBorrow first.1 0 start.stackTicket
                        (principal state.workers.length) (Threads.stackRegion start.entry) with
                    | error fault => simp [spawn, running, registered, owner, held, operands, executable, target, canonical, code, stack, Except.mapError] at success
                    | ok second =>
                      simp [spawn, running, registered, owner, held, operands, executable, target, canonical, code, stack, Except.mapError] at success
                      subst after
                      exact .next (.readBorrow code) (.next (.readBorrow stack) .refl)
                · simp [spawn, running, registered, owner, held, operands, executable, target, canonical, Except.mapError] at success
            · simp [spawn, running, registered, owner, held, operands, executable, Except.mapError] at success
      · simp [spawn, running, registered, owner, Except.mapError] at success

theorem spawn_wellFormed (state : State) (start : Start) (after : State)
    (valid : Mutex.WellFormed state.shared) (success : spawn state start = .ok after) :
    Mutex.WellFormed after.shared := (spawn_history _ _ _ success).wellFormed valid

theorem finishLoans_history (shared : Mutex.State) (identifier : Nat) (workers : List Worker)
    (after : Mutex.State) (success : finishLoans shared identifier workers = .ok after) :
    Mutex.History shared after := by
  induction workers generalizing shared identifier with
  | nil => simp [finishLoans] at success; cases success; exact .refl
  | cons worker rest induction =>
    cases code : Mutex.finishLoan shared (principal identifier) worker.codeLoan with
    | error fault => simp [finishLoans, code, Except.mapError] at success
    | ok first =>
      cases stack : Mutex.finishLoan first (principal identifier) worker.stackLoan with
      | error fault => simp [finishLoans, code, stack, Except.mapError] at success
      | ok second =>
        simp [finishLoans, code, stack, Except.mapError] at success
        exact .next (.finishLoan code) (.next (.finishLoan stack) (induction second (identifier + 1) success))

theorem finishLoans_resources (shared : Mutex.State) (identifier : Nat) (workers : List Worker)
    (after : Mutex.State) (success : finishLoans shared identifier workers = .ok after) :
    after.shared.resources = shared.shared.resources ∧ after.mutex = shared.mutex := by
  induction workers generalizing shared identifier with
  | nil => simp [finishLoans] at success; cases success; exact ⟨rfl, rfl⟩
  | cons worker rest induction =>
    cases code : Mutex.finishLoan shared (principal identifier) worker.codeLoan with
    | error fault => simp [finishLoans, code, Except.mapError] at success
    | ok first =>
      cases stack : Mutex.finishLoan first (principal identifier) worker.stackLoan with
      | error fault => simp [finishLoans, code, stack, Except.mapError] at success
      | ok second =>
        simp [finishLoans, code, stack, Except.mapError] at success
        have tail := induction second (identifier + 1) success
        obtain ⟨firstBorrow, firstFinished, firstEq⟩ := Mutex.finishLoan_ok _ _ _ _ code
        obtain ⟨secondBorrow, secondFinished, secondEq⟩ := Mutex.finishLoan_ok _ _ _ _ stack
        obtain ⟨_, _, firstBorrowEq⟩ := Borrowing.finishLoan_ok _ _ _ _ firstFinished
        obtain ⟨_, _, secondBorrowEq⟩ := Borrowing.finishLoan_ok _ _ _ _ secondFinished
        rw [firstEq, firstBorrowEq] at secondEq
        constructor
        · rw [tail.1, secondEq, secondBorrowEq, firstEq, firstBorrowEq]
        · rw [tail.2, secondEq]

theorem collect_ok (state : State) (result : Mutex.State × List Word)
    (success : collect state = .ok result) :
    completed state = true ∧ finishLoans state.shared 0 state.workers = .ok result.1 ∧
      result.2 = state.workers.map (fun worker => worker.context.registers .rax) := by
  by_cases done : completed state = true
  · cases finished : finishLoans state.shared 0 state.workers with
    | error fault => simp [collect, done, finished] at success
    | ok shared =>
      simp [collect, done, finished] at success
      cases success
      exact ⟨done, rfl, rfl⟩
  · simp [collect, done] at success

theorem collect_zero (state : State) (result : Mutex.State × List Word)
    (success : collect state = .ok result) : result.2 = List.replicate state.workers.length 0 := by
  obtain ⟨done, _, values⟩ := collect_ok _ _ success
  rw [values]
  have each : ∀ worker ∈ state.workers, worker.context.registers .rax = 0 := by
    intro worker member
    have checked := List.all_eq_true.mp done worker member
    exact (of_decide_eq_true checked).2.1
  exact List.map_eq_replicate_iff.mpr each

theorem collect_resources (state : State) (result : Mutex.State × List Word)
    (success : collect state = .ok result) :
    result.1.shared.resources = state.shared.shared.resources ∧ result.1.mutex = state.shared.mutex :=
  finishLoans_resources _ _ _ _ (collect_ok _ _ success).2.1

theorem collect_wellFormed (state : State) (result : Mutex.State × List Word)
    (valid : Mutex.WellFormed state.shared) (success : collect state = .ok result) :
    Mutex.WellFormed result.1 := (finishLoans_history _ _ _ _ (collect_ok _ _ success).2.1).wellFormed valid

end EDSL.OS.MutexReplay
