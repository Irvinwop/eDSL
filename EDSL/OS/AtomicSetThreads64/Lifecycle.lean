/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Resources

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

/-- All successful creation effects are one transaction. Each intermediate
borrow and issuance is recovered from the actual checked result. -/
theorem spawn_ok (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    ∃ (operations : List Sequential.LogicalOp) (cell : Atomics64.Cell) (target : Word)
      (code stack : Atomics64.State × Nat) (data : Atomics64.State × Atomics64.HandleId64),
      parent = 0 ∧ available = true ∧ checkLayout start.bytes = some operations ∧
      codeMatches state.shared.legacy.shared.resources.space start.entry.rip start.bytes = true ∧
      Atomics64.authorizeCell state.shared parent start.cell = .ok cell ∧
      start.entry.registers .rdi = cell.address ∧
      readWord (toMemory state.shared.legacy.shared.resources.space) (start.entry.registers .rsp) = .ok target ∧
      canonical target = true ∧ (start.entry.registers .rsp).toNat + 8 < 2^64 ∧
      canonical (start.entry.registers .rsp + 8) = true ∧
      Atomics64.readBorrow state.shared parent start.codeTicket (principal state.nextThread)
        (codeRegion start.entry start.bytes) = .ok code ∧
      Atomics64.readBorrow code.1 parent start.stackTicket (principal state.nextThread)
        (stackRegion start.entry) = .ok stack ∧
      Atomics64.issue stack.1 parent start.cell (principal state.nextThread) = .ok data ∧
      result = (install state data.1 ⟨parent, start.entry, start.bytes, operations,
        start.cell, target, data.2, code.2, stack.2, start.entry, 0, [], .running⟩,
        state.nextThread) := by
  by_cases root : parent = 0
  · have guard : ¬parent ≠ 0 := by simp [root]
    by_cases free : available = true
    · by_cases collision : (state.workers state.nextThread).isSome = true
      · simp [spawn, guard, free, collision] at success
      · cases layout : checkLayout start.bytes with
        | none => simp [spawn, guard, free, collision, layout] at success
        | some operations =>
          by_cases executable : codeMatches state.shared.legacy.shared.resources.space start.entry.rip start.bytes = true
          · cases authorized : Atomics64.authorizeCell state.shared parent start.cell with
            | error fault => simp [spawn, guard, free, collision, layout, executable, authorized, Except.mapError] at success
            | ok cell =>
              by_cases address : start.entry.registers .rdi = cell.address
              · cases targetRead : readWord (toMemory state.shared.legacy.shared.resources.space)
                    (start.entry.registers .rsp) with
                | error fault => simp [spawn, guard, free, collision, layout, executable, authorized,
                    address, targetRead, Except.mapError] at success
                | ok target =>
                  by_cases targetValid : canonical target = true
                  · by_cases stackBound : (start.entry.registers .rsp).toNat + 8 < 2^64
                    · by_cases stackCanonical : canonical (start.entry.registers .rsp + (8#64)) = true
                      · cases borrowedCode : Atomics64.readBorrow state.shared parent start.codeTicket
                            (principal state.nextThread) (codeRegion start.entry start.bytes) with
                        | error fault => simp [spawn, guard, free, collision, layout, executable,
                            authorized, address, targetRead, targetValid, stackBound, stackCanonical,
                            borrowedCode, Except.mapError] at success
                        | ok code =>
                          cases borrowedStack : Atomics64.readBorrow code.1 parent start.stackTicket
                              (principal state.nextThread) (stackRegion start.entry) with
                          | error fault => simp [spawn, guard, free, collision, layout, executable,
                              authorized, address, targetRead, targetValid, stackBound, stackCanonical,
                              borrowedCode, borrowedStack, Except.mapError] at success
                          | ok stack =>
                            cases issued : Atomics64.issue stack.1 parent start.cell (principal state.nextThread) with
                            | error fault => simp [spawn, guard, free, collision, layout, executable,
                                authorized, address, targetRead, targetValid, stackBound, stackCanonical,
                                borrowedCode, borrowedStack, issued, Except.mapError] at success
                            | ok data =>
                              simp [spawn, guard, free, collision, layout, executable, authorized,
                                address, targetRead, targetValid, stackBound, stackCanonical,
                                borrowedCode, borrowedStack, issued, Except.mapError] at success
                              exact ⟨operations, cell, target, code, stack, data, root, free, rfl,
                                executable, rfl, address, rfl, targetValid, stackBound,
                                stackCanonical, rfl, borrowedStack, issued, success.symm⟩
                      · simp [spawn, guard, free, collision, layout, executable, authorized, address,
                          targetRead, targetValid, stackBound, stackCanonical, Except.mapError] at success
                    · simp [spawn, guard, free, collision, layout, executable, authorized, address,
                        targetRead, targetValid, stackBound, Except.mapError] at success
                  · simp [spawn, guard, free, collision, layout, executable, authorized, address,
                      targetRead, targetValid, Except.mapError] at success
              · simp [spawn, guard, free, collision, layout, executable, authorized, address,
                  Except.mapError] at success
          · simp [spawn, guard, free, collision, layout, executable] at success
    · simp [spawn, guard, free] at success
  · simp [spawn, root] at success

theorem spawn_history (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    Atomics64.History state.shared [none, none, none] result.1.shared := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, c, s, d, same⟩ :=
    spawn_ok _ _ _ _ _ success
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
  obtain ⟨_, _, _, code, stack, data, _, _, _, _, _, _, _, _, _, _, c, s, d, same⟩ :=
    spawn_ok _ _ _ _ _ success
  have codeValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  have stackValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  rw [same]
  refine ⟨?_, (AtomicThreads64.issue_legacy d).2.trans
    ((AtomicThreads64.readBorrow_registry s).2.trans (AtomicThreads64.readBorrow_registry c).2), ?_⟩
  · intro identifier handle live
    apply AtomicThreads64.issue_preserves stackValid d identifier handle
    rw [(AtomicThreads64.readBorrow_registry s).1, (AtomicThreads64.readBorrow_registry c).1]
    exact live
  · intro identifier loan live
    change data.1.legacy.shared.loans identifier = some loan
    rw [(AtomicThreads64.issue_legacy d).1]
    exact AtomicThreads64.readBorrow_preserves codeValid s _ _
      (AtomicThreads64.readBorrow_preserves valid.1 c _ _ live)

theorem spawn_resources (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (success : spawn state parent start available = .ok result) :
    result.1.shared.legacy.shared.resources = state.shared.legacy.shared.resources := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, c, s, d, same⟩ :=
    spawn_ok _ _ _ _ _ success
  rw [same]
  exact (congrArg (fun legacy => legacy.shared.resources) (AtomicThreads64.issue_legacy d).1).trans
    ((AtomicThreads64.readBorrow_resources s).trans (AtomicThreads64.readBorrow_resources c))

theorem spawn_wellFormed (state : State) (parent : Nat) (start : Start) (available : Bool)
    (result : State × Nat) (valid : WellFormed state)
    (success : spawn state parent start available = .ok result) : WellFormed result.1 := by
  have history := spawn_history _ _ _ _ _ success
  have keeps := spawn_keeps _ _ _ _ _ valid success
  have resources := spawn_resources _ _ _ _ _ success
  obtain ⟨operations, cell, target, code, stack, data, root, _, layout, executable, auth,
    address, targetAt, targetValid, stackBound, stackCanonical, c, s, d, same⟩ :=
    spawn_ok _ _ _ _ _ success
  have codeValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  have stackValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  have dataFacts := Atomics64.issue_wellFormed _ _ _ _ _ stackValid d
  have cc := AtomicThreads64.readBorrow_advances c
  have sc := AtomicThreads64.readBorrow_advances s
  have codeLive := AtomicThreads64.readBorrow_preserves codeValid s _ _ (AtomicThreads64.readBorrow_loan c)
  have linked := (Atomics64.authorizeCell_ok _ _ _ _ auth).1
  rw [same] at history keeps resources ⊢
  change data.1.legacy.shared.resources = state.shared.legacy.shared.resources at resources
  refine ⟨dataFacts.1, ?_⟩
  intro identifier worker live
  by_cases new : identifier = state.nextThread
  · subst identifier
    simp [install] at live
    cases live
    refine ⟨by simp [install], root, ?_, ?_, ?_, ?_, checkLayout_sound layout, ?_, ?_,
      targetValid, stackBound, stackCanonical, ?_, ?_⟩
    · exact ⟨_, cell, dataFacts.2, rfl, rfl, by rw [keeps.2.1]; exact linked, address.symm⟩
    · exact ⟨_, by simpa only [install, (AtomicThreads64.issue_legacy d).1] using codeLive, rfl, rfl⟩
    · exact ⟨_, by simpa only [install, (AtomicThreads64.issue_legacy d).1] using
        AtomicThreads64.readBorrow_loan s, rfl, rfl⟩
    · change code.2 ≠ stack.2
      omega
    · simpa only [install, resources] using codeMatches_sound executable
    · simpa only [install, resources] using targetAt
    · intro offset event present
      simp at present
    · exact ⟨rfl, Nat.zero_le _, ContextPrefix.nil⟩
  · have old : state.workers identifier = some worker := by simpa [install, new] using live
    obtain ⟨below, workerValid⟩ := valid.2 _ _ old
    refine ⟨by simp only [install]; omega, workerValid.frame valid.1 history.borrowing ?_⟩
    obtain ⟨record, _, atHandle, _⟩ := workerValid.handle
    obtain ⟨codeRecord, atCode, _⟩ := workerValid.code
    obtain ⟨stackRecord, atStack, _⟩ := workerValid.stack
    exact ⟨(keeps.1 _ _ atHandle).trans atHandle.symm, congrFun keeps.2.1 _,
      (keeps.2.2 _ _ atCode).trans atCode.symm, (keeps.2.2 _ _ atStack).trans atStack.symm⟩

/-- Both borrows and issuance are constructed from present resource facts.
No Ready field assumes a successful future operation. -/
theorem spawn_enabled (state : State) (start : Start) (available : Bool)
    (valid : WellFormed state) (ready : SpawnReady state start) (free : available = true) :
    ∃ result, spawn state 0 start available = .ok result ∧ WellFormed result.1 := by
  obtain ⟨bodyLayout, codeAt, cell, authorized, address, codeReady, stackReady,
    target, targetRead, targetCanonical, stackBound, stackCanonical⟩ := ready
  simp only [BitVec.ofNat_eq_ofNat] at stackCanonical
  have fresh : state.workers state.nextThread = none := by
    cases found : state.workers state.nextThread with
    | none => rfl
    | some worker => have below := (valid.2 _ _ found).1; omega
  obtain ⟨code, c⟩ := codeReady.enabled valid.1 (principal state.nextThread)
  have codeValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ valid.1 c
  obtain ⟨stack, s⟩ := (BorrowReady.after_readBorrow c stackReady).enabled codeValid (principal state.nextThread)
  have stackValid := Atomics64.readBorrow_wellFormed _ _ _ _ _ _ codeValid s
  have cells : stack.1.cells = state.shared.cells :=
    (AtomicThreads64.readBorrow_registry s).2.trans (AtomicThreads64.readBorrow_registry c).2
  have selected := Atomics64.authorizeCell_ok _ _ _ _ authorized
  have issued := Atomics64.issue_success stack.1 0 start.cell (principal state.nextThread)
    cell stackValid (by rw [cells]; exact selected.1) selected.2.1
  let data := Atomics64.installHandle stack.1 ⟨principal state.nextThread, start.cell⟩
  let result : State × Nat :=
    (install state data ⟨0, start.entry, start.bytes, bodyLayout.operations,
      start.cell, target, ⟨stack.1.nextHandle⟩, code.2, stack.2,
      start.entry, 0, [], .running⟩, state.nextThread)
  have layout : checkLayout start.bytes = some bodyLayout.operations := by
    exact (checkLayout_iff _ _).2 bodyLayout.exactBytes
  have success : spawn state 0 start available = .ok result := by
    simp [spawn, free, fresh, layout, codeMatches_complete codeAt, authorized,
      address, targetRead, targetCanonical, stackBound, stackCanonical,
      c, s, issued, Except.mapError, result, data]
  exact ⟨result, success, spawn_wellFormed _ _ _ _ _ valid success⟩

/-- Inversion keeps the checked close and both checked finishes together. -/
theorem join_ok (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    ∃ (worker : Worker) (data code stack : Atomics64.State),
      state.workers identifier = some worker ∧ worker.parent = parent ∧
      worker.phase = .completed ∧
      Atomics64.close state.shared (principal identifier) worker.handle = .ok data ∧
      Atomics64.finishLoan data (principal identifier) worker.codeLoan = .ok code ∧
      Atomics64.finishLoan code (principal identifier) worker.stackLoan = .ok stack ∧
      result = ({ replace state identifier none with shared := stack }, worker.context) := by
  cases found : state.workers identifier with
  | none => simp [join, found] at success
  | some worker =>
    by_cases parentMatches : worker.parent = parent
    · cases phase : worker.phase with
      | running => simp [join, found, parentMatches, phase] at success
      | completed =>
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
              exact ⟨worker, data, code, stack, rfl, parentMatches, phase,
                closed, finishedCode, finishedStack, success.symm⟩
    · simp [join, found, parentMatches] at success

/-- Administrative operations alone have the old lower history; generic
logical dispatches use the operation-neutral borrowing bridge instead. -/
theorem join_history (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    Atomics64.History state.shared [none, none, none] result.1.shared := by
  obtain ⟨_, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact .next (.close d) (.next (.finishLoan c) (.next (.finishLoan s) .refl))

/-- Collection preserves the entire current ownership world and persistent
cell registry, including peer writes performed after this worker's RET. -/
theorem join_resources (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    result.1.shared.legacy.shared.resources = state.shared.legacy.shared.resources ∧
      result.1.shared.cells = state.shared.cells := by
  obtain ⟨_, _, _, _, _, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨(AtomicThreads64.finishLoan_frames s).2.2.trans ((AtomicThreads64.finishLoan_frames c).2.2.trans
    (congrArg (fun legacy => legacy.shared.resources) (AtomicThreads64.close_frames d).1)),
    (AtomicThreads64.finishLoan_frames s).2.1.trans ((AtomicThreads64.finishLoan_frames c).2.1.trans
      (AtomicThreads64.close_frames d).2)⟩

theorem join_retains_peer (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result)
    (query : Nat) (worker : Worker) (live : state.workers query = some worker) (different : query ≠ identifier) :
    Retains state.shared result.1.shared worker := by
  have resources := join_resources _ _ _ _ success
  obtain ⟨joined, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  have peer := (valid.2 _ _ live).2
  have other := (valid.2 _ _ found).2
  rw [same] at resources ⊢
  refine ⟨?_, congrFun resources.2 _, ?_, ?_⟩
  · change stack.handles worker.handle = state.shared.handles worker.handle
    rw [(AtomicThreads64.finishLoan_frames s).1, (AtomicThreads64.finishLoan_frames c).1]
    exact AtomicThreads64.close_other d (AtomicThreads64.HasHandle.different peer.handle other.handle different)
  · exact (AtomicThreads64.finishLoan_other s (peer.code.different other.stack different)).trans
      ((AtomicThreads64.finishLoan_other c (peer.code.different other.code different)).trans
        (congrArg (fun legacy => legacy.shared.loans worker.codeLoan) (AtomicThreads64.close_frames d).1))
  · exact (AtomicThreads64.finishLoan_other s (peer.stack.different other.stack different)).trans
      ((AtomicThreads64.finishLoan_other c (peer.stack.different other.code different)).trans
        (congrArg (fun legacy => legacy.shared.loans worker.stackLoan) (AtomicThreads64.close_frames d).1))

theorem join_wellFormed (state : State) (parent identifier : Nat) (result : State × Context)
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
    exact ⟨(valid.2 _ _ beforeAt).1,
      ((valid.2 _ _ beforeAt).2).frame valid.1 history.borrowing (peers query worker beforeAt removed)⟩

/-- Completion retains all present resources needed for constructive join. -/
theorem join_enabled (state : State) (identifier : Nat) (worker : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (completed : worker.phase = .completed) :
    ∃ result, join state 0 identifier = .ok result ∧ WellFormed result.1 := by
  have workerValid := (valid.2 _ _ live).2
  obtain ⟨handle, cell, authorized, _, _⟩ := workerValid.authorized valid.1
  have closed : Atomics64.close state.shared (principal identifier) worker.handle =
      .ok (Atomics64.removeHandle state.shared worker.handle) := by
    simp [Atomics64.close, authorized]
  obtain ⟨codeLoan, codeAt, codeActor, _⟩ := workerValid.code
  obtain ⟨stackLoan, stackAt, stackActor, _⟩ := workerValid.stack
  have codeAtAfter : (Atomics64.removeHandle state.shared worker.handle).legacy.shared.loans worker.codeLoan =
      some codeLoan := codeAt
  have finishedCode := AtomicThreads64.finishLoan_success _ _ _ codeLoan codeAtAfter codeActor
  have stackAtAfter : (AtomicThreads64.dropLoan (Atomics64.removeHandle state.shared worker.handle)
      worker.codeLoan).legacy.shared.loans worker.stackLoan = some stackLoan := by
    rw [AtomicThreads64.finishLoan_other finishedCode workerValid.distinct.symm]
    exact stackAt
  have finishedStack := AtomicThreads64.finishLoan_success _ _ _ stackLoan stackAtAfter stackActor
  let result : State × Context :=
    ({ replace state identifier none with shared := (AtomicThreads64.dropLoan
      (AtomicThreads64.dropLoan (Atomics64.removeHandle state.shared worker.handle)
        worker.codeLoan) worker.stackLoan) }, worker.context)
  have success : join state 0 identifier = .ok result := by
    simp [join, live, workerValid.parent, completed, closed, finishedCode, finishedStack,
      Except.mapError, result]
  exact ⟨result, success, join_wellFormed _ _ _ _ valid success⟩

theorem join_workers (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    result.1.workers identifier = none ∧ result.1.nextThread = state.nextThread ∧
      ∀ query, query ≠ identifier → result.1.workers query = state.workers query := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, same⟩ := join_ok _ _ _ _ success
  rw [same]
  exact ⟨by simp [replace], rfl, fun query different => by simp [replace, different]⟩

theorem join_revokes (state : State) (parent identifier : Nat) (result : State × Context)
    (valid : WellFormed state) (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      Atomics64.HandleRevoked result.1.shared worker.handle ∧
      Borrowing.Revoked result.1.shared.legacy.shared worker.codeLoan ∧
      Borrowing.Revoked result.1.shared.legacy.shared worker.stackLoan := by
  obtain ⟨worker, data, code, stack, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
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

theorem join_only_resources (state : State) (parent identifier : Nat) (result : State × Context)
    (success : join state parent identifier = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧
      (∀ query, query ≠ worker.handle → result.1.shared.handles query = state.shared.handles query) ∧
      (∀ query, query ≠ worker.codeLoan → query ≠ worker.stackLoan →
        result.1.shared.legacy.shared.loans query = state.shared.legacy.shared.loans query) ∧
      result.1.shared.cells = state.shared.cells := by
  obtain ⟨worker, _, _, _, found, _, _, d, c, s, same⟩ := join_ok _ _ _ _ success
  refine ⟨worker, found, ?_, ?_, (join_resources _ _ _ _ success).2⟩
  · intro query different
    rw [same]
    change _ = state.shared.handles query
    rw [(AtomicThreads64.finishLoan_frames s).1, (AtomicThreads64.finishLoan_frames c).1]
    exact AtomicThreads64.close_other d different
  · intro query notCode notStack
    rw [same]
    exact (AtomicThreads64.finishLoan_other s notStack).trans
      ((AtomicThreads64.finishLoan_other c notCode).trans
        (congrArg (fun legacy => legacy.shared.loans query) (AtomicThreads64.close_frames d).1))

theorem mutate_ok (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    ∃ shared, Atomics64.mutate state.shared operation = .ok shared ∧
      result = ({ state with shared := shared.1 }, shared.2) := by
  cases changed : Atomics64.mutate state.shared operation with
  | error fault => simp [mutate, changed, Except.mapError] at success
  | ok shared =>
    simp [mutate, changed, Except.mapError] at success
    exact ⟨shared, rfl, success.symm⟩

theorem mutate_history (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    Atomics64.History state.shared [none] result.1.shared := by
  obtain ⟨_, changed, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact .next (.mutate changed) .refl

theorem mutate_keeps (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.cells = state.shared.cells ∧
      result.1.shared.legacy.shared.loans = state.shared.legacy.shared.loans := by
  obtain ⟨shared, changed, same⟩ := mutate_ok _ _ _ success
  obtain ⟨_, legacy, mutation, outerEq⟩ := Atomics64.mutate_ok _ _ _ changed
  obtain ⟨_, borrowing, borrowed, legacyEq⟩ := Atomics.mutate_ok _ _ _ mutation
  obtain ⟨_, _, _, borrowEq⟩ := Borrowing.mutate_ok _ _ _ borrowed
  rw [same, outerEq]
  exact ⟨rfl, rfl,
    (congrArg (fun pair : Atomics.State × Option Ownership.Ticket => pair.1.shared.loans) legacyEq).trans
      (congrArg (fun pair : Borrowing.State × Option Ownership.Ticket => pair.1.loans) borrowEq)⟩

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (valid : WellFormed state)
    (success : mutate state operation = .ok result) : WellFormed result.1 := by
  have history := mutate_history _ _ _ success
  have keeps := mutate_keeps _ _ _ success
  obtain ⟨_, _, same⟩ := mutate_ok _ _ _ success
  rw [same] at history keeps ⊢
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro identifier worker live
  exact ⟨(valid.2 _ _ live).1, ((valid.2 _ _ live).2).frame valid.1 history.borrowing
    ⟨congrFun keeps.1 _, congrFun keeps.2.1 _, congrFun keeps.2.2 _, congrFun keeps.2.2 _⟩⟩

theorem retire_ok (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (success : retire state owner cell = .ok after) :
    owner = 0 ∧ ∃ shared, Atomics64.retire state.shared owner cell = .ok shared ∧
      after = { state with shared := shared } := by
  by_cases root : owner = 0
  · have guard : ¬owner ≠ 0 := by simp [root]
    cases changed : Atomics64.retire state.shared owner cell with
    | error fault => simp [retire, guard, changed, Except.mapError] at success
    | ok shared =>
      simp [retire, guard, changed, Except.mapError] at success
      exact ⟨root, shared, rfl, success.symm⟩
  · simp [retire, root] at success

/-- Both unfinished and completed workers pin their persistent cell. -/
theorem retire_in_use_denied (state : State) (owner : Nat) (cell : Atomics64.CellId64)
    (valid : WellFormed state) (identifier : Nat) (worker : Worker)
    (live : state.workers identifier = some worker) (sameCell : worker.cell = cell) (after : State) :
    retire state owner cell ≠ .ok after := by
  intro success
  obtain ⟨_, shared, retired, _⟩ := retire_ok _ _ _ _ success
  obtain ⟨handle, _, atHandle, _, link, _⟩ := ((valid.2 _ _ live).2).handle
  have excluded := Atomics64.retire_no_handles _ _ _ _ valid.1 retired worker.handle handle atHandle
  exact excluded (link.trans sameCell)

theorem retire_wellFormed (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (valid : WellFormed state) (success : retire state owner cell = .ok after) : WellFormed after := by
  obtain ⟨_, shared, retired, same⟩ := retire_ok _ _ _ _ success
  have history : Atomics64.History state.shared [none] shared := .next (.retire retired) .refl
  obtain ⟨_, _, _, sharedEq⟩ := Atomics64.retire_ok _ _ _ _ retired
  rw [same]
  refine ⟨history.wellFormed valid.1, ?_⟩
  intro identifier worker live
  have previous := (valid.2 _ _ live).2
  have other : worker.cell ≠ cell := by
    intro equal
    exact retire_in_use_denied state owner cell valid identifier worker live equal _ success
  refine ⟨(valid.2 _ _ live).1, previous.frame valid.1 history.borrowing ?_⟩
  rw [sharedEq]
  exact ⟨rfl, by simp [Atomics64.removeCell, other], rfl, rfl⟩

theorem retire_history (state : State) (owner : Nat) (cell : Atomics64.CellId64) (after : State)
    (success : retire state owner cell = .ok after) :
    Atomics64.History state.shared [none] after.shared := by
  obtain ⟨_, _, retired, same⟩ := retire_ok _ _ _ _ success
  rw [same]
  exact .next (.retire retired) .refl

end EDSL.OS.AtomicSetThreads64
