/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Machine

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

theorem spawn_ok (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    ∃ (target : Word) (code stack data : Atomics.State × Nat),
      parent = 0 ∧ available = true ∧ codeMatches state.shared.shared.resources.space start.entry.rip = true ∧
      readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp) = .ok target ∧
      canonical target = true ∧
      Atomics.readBorrow state.shared parent start.codeTicket (principal state.nextThread)
        (codeRegion start.entry) = .ok code ∧
      Atomics.readBorrow code.1 parent start.stackTicket (principal state.nextThread)
        (stackRegion start.entry) = .ok stack ∧
      Atomics.issue stack.1 parent start.dataTicket (principal state.nextThread)
        (start.entry.registers .rdi) = .ok data ∧
      result = (install state data.1 ⟨parent, start.entry, target, data.2, code.2, stack.2,
        .preparing start.entry⟩, state.nextThread) := by
  by_cases root : parent = 0
  · have guard : ¬parent ≠ 0 := by simp [root]
    by_cases free : available = true
    · by_cases collision : (state.workers state.nextThread).isSome = true
      · simp [spawn, guard, free, collision] at success
      · by_cases bound : codeMatches state.shared.shared.resources.space start.entry.rip = true
        · cases targetRead : readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp) with
          | error fault => simp [spawn, guard, free, collision, bound, targetRead, Except.mapError] at success
          | ok target =>
            by_cases targetValid : canonical target = true
            · cases borrowedCode : Atomics.readBorrow state.shared parent start.codeTicket
                (principal state.nextThread) (codeRegion start.entry) with
              | error fault =>
                simp [spawn, guard, free, collision, bound, targetRead, targetValid, borrowedCode, Except.mapError] at success
              | ok code =>
                cases borrowedStack : Atomics.readBorrow code.1 parent start.stackTicket
                    (principal state.nextThread) (stackRegion start.entry) with
                | error fault =>
                  simp [spawn, guard, free, collision, bound, targetRead, targetValid,
                    borrowedCode, borrowedStack, Except.mapError] at success
                | ok stack =>
                  cases issuedData : Atomics.issue stack.1 parent start.dataTicket
                      (principal state.nextThread) (start.entry.registers .rdi) with
                  | error fault =>
                    simp [spawn, guard, free, collision, bound, targetRead, targetValid,
                      borrowedCode, borrowedStack, issuedData, Except.mapError] at success
                  | ok data =>
                    simp [spawn, guard, free, collision, bound, targetRead, targetValid,
                      borrowedCode, borrowedStack, issuedData, Except.mapError] at success
                    exact ⟨target, code, stack, data, root, free, bound, rfl, targetValid,
                      rfl, borrowedStack, issuedData, success.symm⟩
            · simp [spawn, guard, free, collision, bound, targetRead, targetValid, Except.mapError] at success
        · simp [spawn, guard, free, collision, bound] at success
    · simp [spawn, guard, free] at success
  · simp [spawn, root] at success

theorem empty_wellFormed (shared : Atomics.State) (valid : Atomics.WellFormed shared) :
    WellFormed (empty shared) := ⟨valid, by simp [empty]⟩

theorem spawn_history (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    Atomics.History state.shared result.1.shared := by
  obtain ⟨_, code, stack, data, _, _, _, _, _, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  rw [same]
  exact .next (.readBorrow c) (.next (.readBorrow s) (.next (.issue d) .refl))

theorem spawn_keeps (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) :
    (∀ identifier handle, state.shared.handles identifier = some handle → result.1.shared.handles identifier = some handle) ∧
    (∀ identifier loan, state.shared.shared.loans identifier = some loan → result.1.shared.shared.loans identifier = some loan) := by
  obtain ⟨_, code, stack, data, _, _, _, _, _, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  have codeValid := Atomics.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  have stackValid := Atomics.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  rw [same]
  constructor
  · intro identifier handle live
    apply issue_preserves stackValid d identifier handle
    rw [readBorrow_handles s, readBorrow_handles c]
    exact live
  · intro identifier loan live
    change data.1.shared.loans identifier = some loan
    rw [issue_shared d]
    exact readBorrow_preserves codeValid s _ _ (readBorrow_preserves valid.1 c _ _ live)

theorem spawn_wellFormed (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) : WellFormed result.1 := by
  have history := spawn_history _ _ _ _ _ success
  have keeps := spawn_keeps _ _ _ _ _ valid success
  obtain ⟨target, code, stack, data, root, _, executable, targetAt, targetValid, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  have codeValid := Atomics.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  have stackValid := Atomics.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  have dataFacts := Atomics.issue_wellFormed _ _ _ _ _ _ stackValid d
  have cc := readBorrow_advances c
  have sc := readBorrow_advances s
  have codeLive := readBorrow_preserves codeValid s _ _ (readBorrow_loan c)
  have space : data.1.shared.resources = state.shared.shared.resources :=
    (congrArg (fun shared => shared.resources) (issue_shared d)).trans
      ((readBorrow_resources s).trans (readBorrow_resources c))
  rw [same] at history keeps ⊢
  refine ⟨dataFacts.1, ?_⟩
  intro identifier worker live
  by_cases new : identifier = state.nextThread
  · subst identifier
    simp [install] at live
    cases live
    refine ⟨by simp [install], root, ?_, ?_, ?_, ?_, ?_, ?_, targetValid, rfl⟩
    · exact ⟨_, dataFacts.2, rfl, rfl⟩
    · exact ⟨_, by simpa only [install, issue_shared d] using codeLive, rfl, rfl⟩
    · exact ⟨_, by simpa only [install, issue_shared d] using readBorrow_loan s, rfl, rfl⟩
    · change code.2 ≠ stack.2
      omega
    · simpa only [install, space] using codeMatches_sound _ _ executable
    · simpa only [install, space] using targetAt
  · have old : state.workers identifier = some worker := by simpa [install, new] using live
    obtain ⟨below, workerValid⟩ := valid.2 _ _ old
    refine ⟨by simp only [install]; omega, workerValid.frame valid.1 history ?_⟩
    obtain ⟨record, atHandle, _, _⟩ := workerValid.handle
    obtain ⟨codeRecord, atCode, _, _⟩ := workerValid.code
    obtain ⟨stackRecord, atStack, _, _⟩ := workerValid.stack
    exact ⟨(keeps.1 _ _ atHandle).trans atHandle.symm,
      (keeps.2 _ _ atCode).trans atCode.symm, (keeps.2 _ _ atStack).trans atStack.symm⟩

end EDSL.OS.AtomicThreads
