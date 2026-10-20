/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Machine

namespace EDSL.OS.Threads
open X86 AddressSpace

theorem spawn_ok (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    ∃ (value : BitVec 32) (target : Word) (data code stack : Borrowing.State × Nat),
      parent = 0 ∧ available = true ∧
      codeMatches state.shared.resources.space start.entry.rip = true ∧
      loadDWord (toMemory state.shared.resources.space) (start.entry.registers .rdi) = .ok value ∧
      readWord (toMemory state.shared.resources.space) (start.entry.registers .rsp) = .ok target ∧
      canonical target = true ∧
      Borrowing.readBorrow state.shared parent start.dataTicket (principal state.nextThread)
        (dataRegion start.entry) = .ok data ∧
      Borrowing.readBorrow data.1 parent start.codeTicket (principal state.nextThread)
        (codeRegion start.entry) = .ok code ∧
      Borrowing.readBorrow code.1 parent start.stackTicket (principal state.nextThread)
        (stackRegion start.entry) = .ok stack ∧
      result = (install state stack.1 ⟨parent, start.entry, value, target, data.2, code.2, stack.2,
        .loading start.entry⟩, state.nextThread) := by
  by_cases root : parent = 0
  · have guard : ¬parent ≠ 0 := by simp [root]
    by_cases free : available = true
    · by_cases collision : (state.workers state.nextThread).isSome = true
      · simp [spawn, guard, free, collision] at success
      · by_cases bound : codeMatches state.shared.resources.space start.entry.rip = true
        · cases read : loadDWord (toMemory state.shared.resources.space) (start.entry.registers .rdi) with
          | error fault => simp [spawn, guard, free, collision, bound, read, Except.mapError] at success
          | ok value =>
            cases targetRead : readWord (toMemory state.shared.resources.space) (start.entry.registers .rsp) with
            | error fault => simp [spawn, guard, free, collision, bound, read, targetRead, Except.mapError] at success
            | ok target =>
              by_cases targetValid : canonical target = true
              · cases borrowedData : Borrowing.readBorrow state.shared parent start.dataTicket
                  (principal state.nextThread) (dataRegion start.entry) with
                | error fault =>
                  simp [spawn, guard, free, collision, bound, read, targetRead, targetValid,
                    borrowedData, Except.mapError] at success
                | ok data =>
                  cases borrowedCode : Borrowing.readBorrow data.1 parent start.codeTicket
                      (principal state.nextThread) (codeRegion start.entry) with
                  | error fault =>
                    simp [spawn, guard, free, collision, bound, read, targetRead, targetValid,
                      borrowedData, borrowedCode, Except.mapError] at success
                  | ok code =>
                    cases borrowedStack : Borrowing.readBorrow code.1 parent start.stackTicket
                        (principal state.nextThread) (stackRegion start.entry) with
                    | error fault =>
                      simp [spawn, guard, free, collision, bound, read, targetRead, targetValid,
                        borrowedData, borrowedCode, borrowedStack, Except.mapError] at success
                    | ok stack =>
                      simp [spawn, guard, free, collision, bound, read, targetRead, targetValid,
                        borrowedData, borrowedCode, borrowedStack, Except.mapError] at success
                      refine ⟨value, target, data, code, stack, root, free, bound, rfl, rfl,
                        targetValid, rfl, borrowedCode, borrowedStack, ?_⟩
                      exact success.symm
              · simp [spawn, guard, free, collision, bound, read, targetRead, targetValid, Except.mapError] at success
        · simp [spawn, guard, free, collision, bound] at success
    · simp [spawn, guard, free] at success
  · simp [spawn, root] at success

theorem empty_wellFormed (shared : Borrowing.State) (valid : Borrowing.WellFormed shared) :
    WellFormed (empty shared) := ⟨valid, by simp [empty]⟩

theorem spawn_history (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    Borrowing.History state.shared result.1.shared := by
  obtain ⟨_, _, data, code, stack, _, _, _, _, _, _, d, c, s, same⟩ := spawn_ok _ _ _ _ _ success
  rw [same]
  exact .next (.readBorrow d) (.next (.readBorrow c) (.next (.readBorrow s) .refl))

theorem spawn_keeps (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) :
    ∀ identifier loan, state.shared.loans identifier = some loan → result.1.shared.loans identifier = some loan := by
  obtain ⟨_, _, data, code, stack, _, _, _, _, _, _, d, c, s, same⟩ := spawn_ok _ _ _ _ _ success
  rw [same]
  have dataValid := (Borrowing.readBorrow_wellFormed _ _ _ _ _ _ valid.1 d).1
  have codeValid := (Borrowing.readBorrow_wellFormed _ _ _ _ _ _ dataValid c).1
  intro identifier loan live
  exact readBorrow_preserves codeValid s _ _
    (readBorrow_preserves dataValid c _ _ (readBorrow_preserves valid.1 d _ _ live))

theorem spawn_wellFormed (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) : WellFormed result.1 := by
  have history := spawn_history state parent start available result success
  have keeps := spawn_keeps state parent start available result valid success
  obtain ⟨value, target, data, code, stack, root, _, executable, valueAt, targetAt, targetValid,
    d, c, s, same⟩ := spawn_ok _ _ _ _ _ success
  have dataFacts := Borrowing.readBorrow_wellFormed _ _ _ _ _ _ valid.1 d
  have codeFacts := Borrowing.readBorrow_wellFormed _ _ _ _ _ _ dataFacts.1 c
  have stackFacts := Borrowing.readBorrow_wellFormed _ _ _ _ _ _ codeFacts.1 s
  have dc := readBorrow_advances d
  have cc := readBorrow_advances c
  have sc := readBorrow_advances s
  have dataLive := readBorrow_preserves codeFacts.1 s _ _
    (readBorrow_preserves dataFacts.1 c _ _ dataFacts.2)
  have codeLive := readBorrow_preserves codeFacts.1 s _ _ codeFacts.2
  have space : stack.1.resources = state.shared.resources :=
    (readBorrow_resources s).trans ((readBorrow_resources c).trans (readBorrow_resources d))
  rw [same] at history keeps ⊢
  refine ⟨stackFacts.1, ?_⟩
  intro identifier worker live
  by_cases new : identifier = state.nextThread
  · subst identifier
    simp [install] at live
    cases live
    refine ⟨by simp [install], root, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, targetValid, rfl⟩
    · exact ⟨_, dataLive, rfl, rfl⟩
    · exact ⟨_, codeLive, rfl, rfl⟩
    · exact ⟨_, stackFacts.2, rfl, rfl⟩
    · change data.2 ≠ code.2
      omega
    · change data.2 ≠ stack.2
      omega
    · change code.2 ≠ stack.2
      omega
    · simpa only [install, space] using codeMatches_sound _ _ executable
    · simpa only [install, space] using valueAt
    · simpa only [install, space] using targetAt
  · have old : state.workers identifier = some worker := by simpa [install, new] using live
    obtain ⟨below, workerValid⟩ := valid.2 _ _ old
    refine ⟨by simp only [install]; omega, workerValid.frame valid.1 history ?_⟩
    intro loanId member
    have has : ∃ loan, state.shared.loans loanId = some loan := by
      obtain ⟨_, dataLoan, codeLoan, stackLoan, _⟩ := workerValid
      rcases member with rfl | rfl | rfl
      · exact ⟨_, dataLoan.choose_spec.1⟩
      · exact ⟨_, codeLoan.choose_spec.1⟩
      · exact ⟨_, stackLoan.choose_spec.1⟩
    obtain ⟨loan, atLoan⟩ := has
    exact (keeps _ _ atLoan).trans atLoan.symm

end EDSL.OS.Threads
