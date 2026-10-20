/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Machine

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

/-- Inversion of the entire checked transaction; there is no partial-state
success result for an earlier loan acquisition. -/
theorem spawn_ok (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    ∃ (cell : Atomics64.Cell) (target : Word) (code stack : Atomics64.State × Nat)
      (data : Atomics64.State × Atomics64.HandleId64),
      parent = 0 ∧ available = true ∧
      codeMatches state.shared.legacy.shared.resources.space start.entry.rip = true ∧
      Atomics64.authorizeCell state.shared parent start.cell = .ok cell ∧
      start.entry.registers .rdi = cell.address ∧
      readWord (toMemory state.shared.legacy.shared.resources.space) (start.entry.registers .rsp) = .ok target ∧
      canonical target = true ∧
      Atomics64.readBorrow state.shared parent start.codeTicket (principal state.nextThread)
        (codeRegion start.entry) = .ok code ∧
      Atomics64.readBorrow code.1 parent start.stackTicket (principal state.nextThread)
        (stackRegion start.entry) = .ok stack ∧
      Atomics64.issue stack.1 parent start.cell (principal state.nextThread) = .ok data ∧
      result = (install state data.1 ⟨parent, start.entry, start.cell, target, data.2,
        code.2, stack.2, .applying start.entry⟩, state.nextThread) := by
  by_cases root : parent = 0
  · have guard : ¬parent ≠ 0 := by simp [root]
    by_cases free : available = true
    · by_cases collision : (state.workers state.nextThread).isSome = true
      · simp [spawn, guard, free, collision] at success
      · by_cases executable : codeMatches state.shared.legacy.shared.resources.space start.entry.rip = true
        · cases authorized : Atomics64.authorizeCell state.shared parent start.cell with
          | error fault => simp [spawn, guard, free, collision, executable, authorized, Except.mapError] at success
          | ok cell =>
            by_cases address : start.entry.registers .rdi = cell.address
            · cases targetRead : readWord (toMemory state.shared.legacy.shared.resources.space)
                  (start.entry.registers .rsp) with
              | error fault => simp [spawn, guard, free, collision, executable, authorized, address,
                  targetRead, Except.mapError] at success
              | ok target =>
                by_cases targetValid : canonical target = true
                · cases borrowedCode : Atomics64.readBorrow state.shared parent start.codeTicket
                      (principal state.nextThread) (codeRegion start.entry) with
                  | error fault => simp [spawn, guard, free, collision, executable, authorized, address,
                      targetRead, targetValid, borrowedCode, Except.mapError] at success
                  | ok code =>
                    cases borrowedStack : Atomics64.readBorrow code.1 parent start.stackTicket
                        (principal state.nextThread) (stackRegion start.entry) with
                    | error fault => simp [spawn, guard, free, collision, executable, authorized, address,
                        targetRead, targetValid, borrowedCode, borrowedStack, Except.mapError] at success
                    | ok stack =>
                      cases issued : Atomics64.issue stack.1 parent start.cell (principal state.nextThread) with
                      | error fault => simp [spawn, guard, free, collision, executable, authorized, address,
                          targetRead, targetValid, borrowedCode, borrowedStack, issued, Except.mapError] at success
                      | ok data =>
                        simp [spawn, guard, free, collision, executable, authorized, address,
                          targetRead, targetValid, borrowedCode, borrowedStack, issued, Except.mapError] at success
                        exact ⟨cell, target, code, stack, data, root, free, executable,
                          rfl, address, rfl, targetValid, rfl, borrowedStack, issued, success.symm⟩
                · simp [spawn, guard, free, collision, executable, authorized, address,
                    targetRead, targetValid, Except.mapError] at success
            · simp [spawn, guard, free, collision, executable, authorized, address, Except.mapError] at success
        · simp [spawn, guard, free, collision, executable] at success
    · simp [spawn, guard, free] at success
  · simp [spawn, root] at success

theorem empty_wellFormed (shared : Atomics64.State) (valid : Atomics64.WellFormed shared) :
    WellFormed (empty shared) := ⟨valid, by simp [empty]⟩

theorem spawn_history (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    Atomics64.History state.shared [none, none, none] result.1.shared := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  rw [same]
  exact .next (.readBorrow c) (.next (.readBorrow s) (.next (.issue d) .refl))

theorem spawn_keeps (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) :
    (∀ identifier handle, state.shared.handles identifier = some handle →
      result.1.shared.handles identifier = some handle) ∧
    result.1.shared.cells = state.shared.cells ∧
    (∀ identifier loan, state.shared.legacy.shared.loans identifier = some loan →
      result.1.shared.legacy.shared.loans identifier = some loan) := by
  obtain ⟨_, _, code, stack, data, _, _, _, _, _, _, _, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  have codeValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  have stackValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  rw [same]
  refine ⟨?_, (issue_legacy d).2.trans ((readBorrow_registry s).2.trans (readBorrow_registry c).2), ?_⟩
  · intro identifier handle live
    apply issue_preserves stackValid d identifier handle
    rw [(readBorrow_registry s).1, (readBorrow_registry c).1]
    exact live
  · intro identifier loan live
    change data.1.legacy.shared.loans identifier = some loan
    rw [(issue_legacy d).1]
    exact readBorrow_preserves codeValid s _ _ (readBorrow_preserves valid.1 c _ _ live)

theorem spawn_resources (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    result.1.shared.legacy.shared.resources = state.shared.legacy.shared.resources := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  rw [same]
  exact (congrArg (fun legacy => legacy.shared.resources) (issue_legacy d).1).trans
    ((readBorrow_resources s).trans (readBorrow_resources c))

theorem spawn_wellFormed (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) : WellFormed result.1 := by
  have history := spawn_history _ _ _ _ _ success
  have keeps := spawn_keeps _ _ _ _ _ valid success
  have resources := spawn_resources _ _ _ _ _ success
  obtain ⟨cell, target, code, stack, data, root, _, executable, auth, address, targetAt,
    targetValid, c, s, d, same⟩ := spawn_ok _ _ _ _ _ success
  have codeValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  have stackValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  have dataFacts := Atomics64.issue_wellFormed _ _ _ _ _ stackValid d
  have cc := readBorrow_advances c
  have sc := readBorrow_advances s
  have codeLive := readBorrow_preserves codeValid s _ _ (readBorrow_loan c)
  have linked := (Atomics64.authorizeCell_ok _ _ _ _ auth).1
  rw [same] at history keeps resources ⊢
  change data.1.legacy.shared.resources = state.shared.legacy.shared.resources at resources
  refine ⟨dataFacts.1, ?_⟩
  intro identifier worker live
  by_cases new : identifier = state.nextThread
  · subst identifier
    simp [install] at live
    cases live
    refine ⟨by simp [install], root, ?_, ?_, ?_, ?_, ?_, ?_, targetValid, rfl⟩
    · exact ⟨_, cell, dataFacts.2, rfl, rfl, by rw [keeps.2.1]; exact linked, address.symm⟩
    · exact ⟨_, by simpa only [install, (issue_legacy d).1] using codeLive, rfl, rfl⟩
    · exact ⟨_, by simpa only [install, (issue_legacy d).1] using readBorrow_loan s, rfl, rfl⟩
    · change code.2 ≠ stack.2
      omega
    · simpa only [install, resources] using codeMatches_sound _ _ executable
    · simpa only [install, resources] using targetAt
  · have old : state.workers identifier = some worker := by simpa [install, new] using live
    obtain ⟨below, workerValid⟩ := valid.2 _ _ old
    refine ⟨by simp only [install]; omega, workerValid.frame valid.1 history ?_⟩
    obtain ⟨record, _, atHandle, _⟩ := workerValid.handle
    obtain ⟨codeRecord, atCode, _⟩ := workerValid.code
    obtain ⟨stackRecord, atStack, _⟩ := workerValid.stack
    exact ⟨(keeps.1 _ _ atHandle).trans atHandle.symm, congrFun keeps.2.1 _,
      (keeps.2.2 _ _ atCode).trans atCode.symm, (keeps.2.2 _ _ atStack).trans atStack.symm⟩

end EDSL.OS.AtomicThreads64
