/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Operations

namespace EDSL.OS.Atomics64
open X86 AddressSpace

theorem enroll_wellFormed (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (result : State × CellId64) (valid : WellFormed state)
    (success : enroll state owner ticket address = .ok result) :
    WellFormed result.1 ∧ result.1.cells result.2 = some ⟨owner, ticket, address⟩ := by
  obtain ⟨cellValid, unreserved, legacyFree, readers, same⟩ := enroll_ok _ _ _ _ _ success
  subst result
  refine ⟨⟨valid.legacy, ?_, ?_, ?_, ?_, ?_⟩, by simp [installCell]⟩
  · intro identifier cell live
    by_cases fresh : identifier = ⟨state.nextCell⟩
    · subst identifier
      simp [installCell] at live
      cases live
      exact ⟨by change state.nextCell < state.nextCell + 1; omega, cellValid⟩
    · have old : state.cells identifier = some cell := by simpa [installCell, fresh] using live
      exact ⟨by have below := (valid.cells _ _ old).1; change identifier.index < state.nextCell + 1; omega,
        (valid.cells _ _ old).2⟩
  · intro identifier handle live
    obtain ⟨below, cell, linked⟩ := valid.handles identifier handle live
    have different : handle.cell ≠ ⟨state.nextCell⟩ := by
      intro eq
      rw [eq, fresh_cell _ valid] at linked
      cases linked
    exact ⟨below, cell, by simpa [installCell, different] using linked⟩
  · intro identifier cell live loanId loan reader
    by_cases fresh : identifier = ⟨state.nextCell⟩
    · subst identifier
      simp [installCell] at live
      cases live
      have blocked := Borrowing.allowed_sound _ _ valid.legacy.shared readers loanId loan reader
      simpa [Ownership.Mutation.target, eq_comm] using blocked
    · exact valid.noReaders identifier cell (by simpa [installCell, fresh] using live) loanId loan reader
  · intro identifier cell live handleId handle oldHandle
    by_cases fresh : identifier = ⟨state.nextCell⟩
    · subst identifier
      simp [installCell] at live
      cases live
      intro eq
      have pinned := Atomics.reserved_of_live state.legacy valid.legacy handleId handle oldHandle
      rw [eq, legacyFree] at pinned
      cases pinned
    · exact valid.noLegacy identifier cell (by simpa [installCell, fresh] using live) handleId handle oldHandle
  · intro left a right b atLeft atRight sameAllocation
    by_cases freshLeft : left = ⟨state.nextCell⟩
    · subst left
      simp [installCell] at atLeft
      cases atLeft
      by_cases freshRight : right = ⟨state.nextCell⟩
      · exact freshRight.symm
      · have old : state.cells right = some b := by simpa [installCell, freshRight] using atRight
        exact False.elim ((unreserved_sound state valid ticket.identifier unreserved right b old) sameAllocation.symm)
    · have oldLeft : state.cells left = some a := by simpa [installCell, freshLeft] using atLeft
      by_cases freshRight : right = ⟨state.nextCell⟩
      · subst right
        simp [installCell] at atRight
        cases atRight
        exact False.elim ((unreserved_sound state valid ticket.identifier unreserved left a oldLeft) sameAllocation)
      · exact valid.unique left a right b oldLeft (by simpa [installCell, freshRight] using atRight) sameAllocation

theorem issue_wellFormed (state : State) (owner : Nat) (identifier : CellId64) (actor : Nat)
    (result : State × HandleId64) (valid : WellFormed state)
    (success : issue state owner identifier actor = .ok result) :
    WellFormed result.1 ∧ result.1.handles result.2 = some ⟨actor, identifier⟩ := by
  obtain ⟨cell, authorized, same⟩ := issue_ok _ _ _ _ _ success
  have linked := (authorizeCell_ok _ _ _ _ authorized).1
  subst result
  refine ⟨⟨valid.legacy, valid.cells, ?_, valid.noReaders, valid.noLegacy, valid.unique⟩,
    by simp [installHandle]⟩
  intro query handle live
  by_cases fresh : query = ⟨state.nextHandle⟩
  · subst query
    simp [installHandle] at live
    cases live
    exact ⟨by change state.nextHandle < state.nextHandle + 1; omega, cell, linked⟩
  · have old : state.handles query = some handle := by simpa [installHandle, fresh] using live
    exact ⟨by have below := (valid.handles _ _ old).1; change query.index < state.nextHandle + 1; omega,
      (valid.handles _ _ old).2⟩

theorem close_wellFormed (state : State) (actor : Nat) (identifier : HandleId64) (after : State)
    (valid : WellFormed state) (success : close state actor identifier = .ok after) : WellFormed after := by
  obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
  subst after
  exact ⟨valid.legacy, valid.cells, fun query handle live => valid.handles query handle (removeHandle_live live),
    valid.noReaders, valid.noLegacy, valid.unique⟩

theorem retire_wellFormed (state : State) (owner : Nat) (identifier : CellId64) (after : State)
    (valid : WellFormed state) (success : retire state owner identifier = .ok after) : WellFormed after := by
  obtain ⟨_, _, empty, same⟩ := retire_ok _ _ _ _ success
  subst after
  refine ⟨valid.legacy, fun query cell live => valid.cells query cell (removeCell_live live), ?_,
    fun query cell live => valid.noReaders query cell (removeCell_live live),
    fun query cell live => valid.noLegacy query cell (removeCell_live live),
    fun left a right b atLeft atRight => valid.unique left a right b (removeCell_live atLeft) (removeCell_live atRight)⟩
  intro query handle live
  obtain ⟨below, cell, linked⟩ := valid.handles query handle live
  have different := no_handles_sound state valid identifier empty query handle live
  exact ⟨below, cell, by simpa [removeCell, different] using linked⟩

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (valid : WellFormed state)
    (success : mutate state operation = .ok result) : WellFormed result.1 := by
  obtain ⟨checked, legacy, changed, same⟩ := mutate_ok _ _ _ success
  subst result
  obtain ⟨_, shared, mutation, legacyEq⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, performed, sharedEq⟩ := Borrowing.mutate_ok _ _ _ mutation
  refine ⟨Atomics.mutate_wellFormed _ _ _ valid.legacy changed, ?_, valid.handles, ?_, ?_, valid.unique⟩
  · intro identifier cell live
    obtain ⟨below, cellValid⟩ := valid.cells identifier cell live
    have framed := cellValid.frame valid.legacy.shared.1
      (operation.run_preserves _ _ _ valid.legacy.shared.1 performed
        (allowed_sound state operation valid checked identifier cell live))
    rw [legacyEq, sharedEq]
    exact ⟨below, framed⟩
  · intro identifier cell live loanId loan reader
    apply valid.noReaders identifier cell live loanId loan
    simpa only [legacyEq, sharedEq] using reader
  · intro identifier cell live handleId handle oldHandle
    apply valid.noLegacy identifier cell live handleId handle
    simpa only [legacyEq] using oldHandle

theorem readBorrow_wellFormed (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat) (valid : WellFormed state)
    (success : readBorrow state lender ticket borrower region = .ok result) : WellFormed result.1 := by
  obtain ⟨unreserved, legacy, borrowed, same⟩ := readBorrow_ok _ _ _ _ _ _ success
  obtain ⟨_, shared, checked, legacyEq⟩ := Atomics.readBorrow_ok _ _ _ _ _ _ borrowed
  obtain ⟨_, _, _, _, _, sharedEq⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ checked
  subst result
  refine ⟨Atomics.readBorrow_wellFormed _ _ _ _ _ _ valid.legacy borrowed, ?_, valid.handles,
    ?_, ?_, valid.unique⟩
  · intro identifier cell live
    rw [legacyEq, sharedEq]
    exact valid.cells identifier cell live
  · intro identifier cell live loanId loan reader
    rw [legacyEq, sharedEq] at reader
    by_cases fresh : loanId = state.legacy.shared.nextLoan
    · subst loanId
      simp [Borrowing.installLoan] at reader
      cases reader
      exact Ne.symm (unreserved_sound state valid ticket.identifier unreserved identifier cell live)
    · exact valid.noReaders identifier cell live loanId loan
        (by simpa [Borrowing.installLoan, fresh] using reader)
  · intro identifier cell live handleId handle oldHandle
    apply valid.noLegacy identifier cell live handleId handle
    simpa only [legacyEq] using oldHandle

theorem finishLoan_wellFormed (state : State) (borrower identifier : Nat) (after : State)
    (valid : WellFormed state) (success : finishLoan state borrower identifier = .ok after) : WellFormed after := by
  obtain ⟨legacy, finished, same⟩ := finishLoan_ok _ _ _ _ success
  obtain ⟨shared, checked, legacyEq⟩ := Atomics.finishLoan_ok _ _ _ _ finished
  obtain ⟨_, _, sharedEq⟩ := Borrowing.finishLoan_ok _ _ _ _ checked
  subst after
  refine ⟨Atomics.finishLoan_wellFormed _ _ _ _ valid.legacy finished, ?_, valid.handles,
    ?_, ?_, valid.unique⟩
  · intro query cell live
    rw [legacyEq, sharedEq]
    exact valid.cells query cell live
  · intro query cell live loanId loan reader
    rw [legacyEq, sharedEq] at reader
    by_cases removed : loanId = identifier
    · simp [removed] at reader
    · exact valid.noReaders query cell live loanId loan (by simpa [removed] using reader)
  · intro query cell live handleId handle oldHandle
    apply valid.noLegacy query cell live handleId handle
    simpa only [legacyEq] using oldHandle

theorem issue32_wellFormed (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (address : Word) (result : State × Nat) (valid : WellFormed state)
    (success : issue32 state owner ticket actor address = .ok result) : WellFormed result.1 := by
  obtain ⟨unreserved, legacy, issued, same⟩ := issue32_ok _ _ _ _ _ _ success
  have legacyValid := (Atomics.issue_wellFormed _ _ _ _ _ _ valid.legacy issued).1
  obtain ⟨_, _, _, _, _, _, _, legacyEq⟩ := Atomics.issue_ok _ _ _ _ _ _ issued
  subst result
  rw [legacyEq] at legacyValid ⊢
  refine ⟨legacyValid, valid.cells, valid.handles, valid.noReaders, ?_, valid.unique⟩
  intro identifier cell live handleId handle oldHandle
  by_cases fresh : handleId = state.legacy.nextHandle
  · subst handleId
    simp [Atomics.install] at oldHandle
    cases oldHandle
    exact Ne.symm (unreserved_sound state valid ticket.identifier unreserved identifier cell live)
  · exact valid.noLegacy identifier cell live handleId handle (by simpa [Atomics.install, fresh] using oldHandle)

theorem close32_wellFormed (state : State) (actor identifier : Nat) (after : State)
    (valid : WellFormed state) (success : close32 state actor identifier = .ok after) : WellFormed after := by
  obtain ⟨legacy, closed, same⟩ := close32_ok _ _ _ _ success
  obtain ⟨_, _, legacyEq⟩ := Atomics.close_ok _ _ _ _ closed
  subst after
  refine ⟨Atomics.close_wellFormed _ _ _ _ valid.legacy closed, ?_, valid.handles, ?_, ?_, valid.unique⟩
  · intro query cell live
    rw [legacyEq]
    exact valid.cells query cell live
  · intro query cell live loanId loan reader
    apply valid.noReaders query cell live loanId loan
    simpa only [legacyEq] using reader
  · intro query cell live handleId handle oldHandle
    rw [legacyEq] at oldHandle
    by_cases removed : handleId = identifier
    · simp [removed] at oldHandle
    · exact valid.noLegacy query cell live handleId handle (by simpa [removed] using oldHandle)

/-- Every targeted ordinary mutation is rejected, independent of which bytes
within the registered allocation it would touch. -/
theorem mutate_reserved (state : State) (operation : Ownership.Mutation) (valid : WellFormed state)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (target : operation.target = some cell.ticket.identifier) :
    mutate state operation = .error .reserved := by
  have pinned := reserved_of_live state valid identifier cell live
  simp [mutate, allowed, target, pinned]

theorem readBorrow_reserved (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (valid : WellFormed state)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (same : ticket.identifier = cell.ticket.identifier) :
    readBorrow state lender ticket borrower region = .error .reserved := by
  simp [readBorrow, same, reserved_of_live state valid identifier cell live]

theorem issue32_reserved (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (address : Word) (valid : WellFormed state)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (same : ticket.identifier = cell.ticket.identifier) :
    issue32 state owner ticket actor address = .error .reserved := by
  simp [issue32, same, reserved_of_live state valid identifier cell live]

theorem enroll_legacy_excluded (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (valid : WellFormed state) (handleId : Nat) (handle : Atomics.Handle)
    (live : state.legacy.handles handleId = some handle) (same : handle.ticket.identifier = ticket.identifier)
    (result : State × CellId64) : enroll state owner ticket address ≠ .ok result := by
  intro success
  obtain ⟨_, _, unreserved, _, _⟩ := enroll_ok _ _ _ _ _ success
  have pinned := Atomics.reserved_of_live state.legacy valid.legacy handleId handle live
  rw [same, unreserved] at pinned
  cases pinned

theorem enroll_reader_excluded (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (valid : WellFormed state) (loanId : Nat) (loan : Borrowing.Loan)
    (live : state.legacy.shared.loans loanId = some loan) (same : loan.ticket.identifier = ticket.identifier)
    (result : State × CellId64) : enroll state owner ticket address ≠ .ok result := by
  intro success
  obtain ⟨_, _, _, checked, _⟩ := enroll_ok _ _ _ _ _ success
  have different := Borrowing.allowed_sound _ _ valid.legacy.shared checked loanId loan live
  exact different (congrArg some same.symm)

theorem enroll_reserved_excluded (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (address : Word) (valid : WellFormed state) (identifier : CellId64) (cell : Cell)
    (live : state.cells identifier = some cell) (same : cell.ticket.identifier = ticket.identifier)
    (result : State × CellId64) : enroll state owner ticket address ≠ .ok result := by
  intro success
  obtain ⟨_, unreserved, _, _, _⟩ := enroll_ok _ _ _ _ _ success
  exact unreserved_sound state valid ticket.identifier unreserved identifier cell live same

/-- Closing the last handle retains the registration and its allocation gate. -/
theorem close_cells (state : State) (actor : Nat) (identifier : HandleId64) (after : State)
    (success : close state actor identifier = .ok after) :
    after.cells = state.cells ∧ after.nextCell = state.nextCell ∧ after.legacy = state.legacy := by
  obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
  subst after
  exact ⟨rfl, rfl, rfl⟩

theorem close_reserved (state : State) (actor : Nat) (handleId : HandleId64) (after : State)
    (valid : WellFormed state) (success : close state actor handleId = .ok after)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell) :
    reserved after cell.ticket.identifier = true := by
  obtain ⟨same, frontier, _⟩ := close_cells _ _ _ _ success
  simpa only [reserved, same, frontier] using reserved_of_live state valid identifier cell live

/-- Successful retirement excludes every stored live handle, independently
of its actor label. The outer worker layer must separately retain handles to join. -/
theorem retire_no_handles (state : State) (owner : Nat) (identifier : CellId64) (after : State)
    (valid : WellFormed state) (success : retire state owner identifier = .ok after)
    (handleId : HandleId64) (handle : Handle) (live : state.handles handleId = some handle) :
    handle.cell ≠ identifier := by
  obtain ⟨_, _, empty, _⟩ := retire_ok _ _ _ _ success
  exact no_handles_sound state valid identifier empty handleId handle live

theorem retire_success (state : State) (owner : Nat) (identifier : CellId64) (cell : Cell)
    (valid : WellFormed state) (live : state.cells identifier = some cell) (owns : cell.owner = owner)
    (empty : hasHandles state identifier = false) :
    retire state owner identifier = .ok (removeCell state identifier) := by
  simp [retire, authorizeCell_success _ _ _ _ valid live owns, empty]

theorem close_success (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (valid : WellFormed state)
    (live : state.handles identifier = some handle) (acts : handle.actor = actor)
    (linked : state.cells handle.cell = some cell) :
    close state actor identifier = .ok (removeHandle state identifier) := by
  simp [close, authorize_success _ _ _ _ _ valid live acts linked]

/-- The existing32 manager's checked store64 has exactly the Borrowing gate
and no returned allocation ticket. This fact grants no independent atomicity. -/
theorem legacy_store64_guarded {before : Atomics.State} {owner : Nat}
    {ticket : Ownership.Ticket} {address value : Word}
    {result : Atomics.State × Option Ownership.Ticket}
    (success : Atomics.mutate before (.store64 owner ticket address value) = .ok result) :
    Borrowing.mutate before.shared (.store64 owner ticket address value) =
      .ok (result.1.shared, none) := by
  obtain ⟨_, shared, stored, same⟩ := Atomics.mutate_ok _ _ _ success
  have noTicket := Borrowing.store64_none stored
  rw [same]
  rw [← noTicket]
  exact stored

theorem logicalDiscard_guarded (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalDiscard state actor identifier mask = .ok result) :
    ∃ handle cell, authorize state actor identifier = .ok (handle, cell) ∧
      result.2 = ⟨actor, identifier, handle.cell, ⟨.bor, mask, ⟨cell.address,
        result.2.logical.event.before, Sequential.LogicalOp.eval .bor result.2.logical.event.before mask⟩⟩⟩ ∧
      Atomics.mutate state.legacy
        (.store64 cell.owner cell.ticket cell.address result.2.logical.event.after) =
          .ok (result.1.legacy, none) := by
  obtain ⟨handle, cell, old, legacy, authorized, _, stored, same⟩ := logicalDiscard_ok _ _ _ _ _ success
  obtain ⟨_, shared, sharedStore, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  have noTicket : legacy.2 = none := by
    rw [legacyEq]
    exact Borrowing.store64_none sharedStore
  subst result
  refine ⟨handle, cell, authorized, rfl, ?_⟩
  change Atomics.mutate state.legacy
    (.store64 cell.owner cell.ticket cell.address (Sequential.LogicalOp.eval .bor old mask)) =
      .ok (legacy.1, none)
  rw [← noTicket]
  exact stored

/-- Complete projected RAM agrees with one full64 RMWTransition64, and the
operation/mask are fixed by this checked OR operation. No store-only atomicity
claim or ABI old-value result is involved. -/
theorem logicalDiscard_sound (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalDiscard state actor identifier mask = .ok result) :
    RMWTransition64 (toMemory state.legacy.shared.resources.space) result.2.logical.event
      (toMemory result.1.legacy.shared.resources.space) ∧
    result.2.logical.op = .bor ∧ result.2.logical.mask = mask ∧
    result.2.logical.event.after = Sequential.LogicalOp.eval .bor result.2.logical.event.before mask ∧
    result.2.actor = actor ∧ result.2.handle = identifier := by
  obtain ⟨handle, cell, old, legacy, authorized, read, stored, same⟩ := logicalDiscard_ok _ _ _ _ _ success
  have checked := (authorize_ok _ _ _ _ authorized).2.2.2
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  subst result
  exact ⟨⟨checked.2.1, checked.1.writable, read, effect.projection⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem logicalDiscard_primitive (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalDiscard state actor identifier mask = .ok result) :
    logicalRmwQWord .bor (toMemory state.legacy.shared.resources.space) result.2.logical.event.address mask =
      .ok (toMemory result.1.legacy.shared.resources.space, result.2.logical) := by
  obtain ⟨handle, cell, old, legacy, authorized, read, stored, same⟩ := logicalDiscard_ok _ _ _ _ _ success
  have checked := (authorize_ok _ _ _ _ authorized).2.2.2
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  subst result
  rw [effect.projection]
  exact logicalRmwQWord_success .bor _ cell.address mask old checked.2.1 checked.1.writable read

/-- The exact checked memory effect plus every registry frame. `shared` supplies
all allocation metadata/frontiers, loans, permissions and the eight-byte frame. -/
structure Effect (before after : State) (event : Event) : Prop where
  shared : Borrowing.StoreEffect64 before.legacy.shared after.legacy.shared
    event.logical.event.address event.logical.event.after
  cells : after.cells = before.cells
  nextCell : after.nextCell = before.nextCell
  handles : after.handles = before.handles
  nextHandle : after.nextHandle = before.nextHandle
  legacyHandles : after.legacy.handles = before.legacy.handles
  legacyNextHandle : after.legacy.nextHandle = before.legacy.nextHandle

theorem logicalDiscard_effect (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalDiscard state actor identifier mask = .ok result) :
    Effect state result.1 result.2 := by
  obtain ⟨_, _, _, legacy, _, _, stored, same⟩ := logicalDiscard_ok _ _ _ _ _ success
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  obtain ⟨_, _, _, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  subst result
  exact ⟨effect, rfl, rfl, rfl, rfl, by rw [legacyEq], by rw [legacyEq]⟩

theorem logicalDiscard_wellFormed (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (valid : WellFormed state)
    (success : logicalDiscard state actor identifier mask = .ok result) : WellFormed result.1 := by
  obtain ⟨_, _, _, legacy, _, _, stored, same⟩ := logicalDiscard_ok _ _ _ _ _ success
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  obtain ⟨_, _, _, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  subst result
  refine ⟨Atomics.mutate_wellFormed _ _ _ valid.legacy stored, ?_, valid.handles, ?_, ?_, valid.unique⟩
  · intro query cell live
    have previous := valid.cells query cell live
    exact ⟨previous.1, previous.2.permissions effect.allocations effect.permissions⟩
  · intro query cell live loanId loan reader
    apply valid.noReaders query cell live loanId loan
    rwa [effect.loans] at reader
  · intro query cell live handleId handle oldHandle
    apply valid.noLegacy query cell live handleId handle
    simpa only [legacyEq] using oldHandle

theorem legacy_allowed64 (state : State) (identifier : CellId64) (cell : Cell) (value : Word)
    (valid : WellFormed state) (live : state.cells identifier = some cell) :
    Atomics.allowed state.legacy (.store64 cell.owner cell.ticket cell.address value) = true := by
  apply List.all_eq_true.mpr
  intro handleId _
  cases present : state.legacy.handles handleId with
  | none => rfl
  | some handle =>
    have different := valid.noLegacy identifier cell live handleId handle present
    simpa only [Ownership.Mutation.target, decide_eq_true_eq, ne_eq, Option.some.injEq] using Ne.symm different

/-- Every present actor handle can perform OR for every full64 current word
and mask, including unchanged-value RMWs. Current authority derives success;
no future execution or successful mutation is a precondition. -/
theorem logicalDiscard_enabled (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (handle : Handle) (cell : Cell) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    ∃ result, logicalDiscard state actor identifier mask = .ok result := by
  obtain ⟨_, _, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  obtain ⟨allocation, authority, fits⟩ := checked.1.authorize
  obtain ⟨old, read⟩ := checked.1.load_exists
  let value := Sequential.LogicalOp.eval .bor old mask
  obtain ⟨after, stored⟩ := Borrowing.store64_admitted state.legacy.shared cell.owner cell.ticket
    cell.address value allocation authority fits checked.1.writable (valid.noReaders _ _ linked)
  have permitted := legacy_allowed64 state handle.cell cell value valid linked
  have legacyStore : Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value) =
      .ok ({ state.legacy with shared := after }, none) := by
    simp [Atomics.mutate, permitted, stored, Except.mapError]
  refine ⟨({ state with legacy := { state.legacy with shared := after } },
    ⟨actor, identifier, handle.cell, ⟨.bor, mask, ⟨cell.address, old, value⟩⟩⟩), ?_⟩
  simp [logicalDiscard, authorized, read, legacyStore, Except.mapError, value]

/-- The checked RMW retains actual bytes of every pre-existing ordinary loan. -/
theorem logicalDiscard_loan_contents (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (valid : WellFormed state)
    (success : logicalDiscard state actor identifier mask = .ok result)
    (loanId : Nat) (loan : Borrowing.Loan) (live : state.legacy.shared.loans loanId = some loan) :
    ∀ query, loan.region.Contains query →
      result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query := by
  obtain ⟨_, _, _, _, stored⟩ := logicalDiscard_guarded _ _ _ _ _ success
  have gate := legacy_store64_guarded stored
  have history : Borrowing.History state.legacy.shared result.1.legacy.shared := .next (.mutate gate) .refl
  have effect := (logicalDiscard_effect _ _ _ _ _ success).shared
  exact (history.loan_stable valid.legacy.shared loanId (valid.legacy.shared.2 _ _ live).1 loan
    ((congrFun effect.loans loanId).trans live)).2

theorem cell_loan_disjoint (state : State) (valid : WellFormed state)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (loanId : Nat) (loan : Borrowing.Loan) (reader : state.legacy.shared.loans loanId = some loan) :
    QWordDisjoint cell.address loan.region.base loan.region.length :=
  WordResources64.word_loan_disjoint valid.legacy.shared (valid.cells _ _ live).2.1 reader
    (valid.noReaders _ _ live _ _ reader).symm

/-- Ordinary environment changes preserve the complete allocation of every
registered cell, including bytes outside its selected eight-byte operand. -/
theorem mutate_preserves_cell (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (valid : WellFormed state)
    (success : mutate state operation = .ok result)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell) :
    Ownership.PreservesAllocation state.legacy.shared.resources result.1.legacy.shared.resources
      cell.ticket.identifier := by
  obtain ⟨checked, legacy, changed, same⟩ := mutate_ok _ _ _ success
  obtain ⟨_, shared, mutation, legacyEq⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, performed, sharedEq⟩ := Borrowing.mutate_ok _ _ _ mutation
  have framed := operation.run_preserves _ _ _ valid.legacy.shared.1 performed
    (allowed_sound state operation valid checked identifier cell live)
  rw [same, legacyEq, sharedEq]
  exact framed

theorem logicalDiscard_preserves_other (state : State) (actor : Nat) (handleId : HandleId64) (mask : Word)
    (result : State × Event) (valid : WellFormed state)
    (success : logicalDiscard state actor handleId mask = .ok result)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (other : identifier ≠ result.2.cell) :
    Ownership.PreservesAllocation state.legacy.shared.resources result.1.legacy.shared.resources
      cell.ticket.identifier := by
  obtain ⟨handle, target, authorized, eventEq, stored⟩ := logicalDiscard_guarded _ _ _ _ _ success
  have targetLive := (authorize_ok _ _ _ _ authorized).2.2.1
  have different : cell.ticket.identifier ≠ target.ticket.identifier := by
    intro sameAllocation
    have sameId := valid.unique identifier cell handle.cell target live targetLive sameAllocation
    apply other
    rw [eventEq]
    exact sameId
  exact Borrowing.store64_preservesAllocation valid.legacy.shared.1 (legacy_store64_guarded stored)
    cell.ticket.identifier different

theorem finishLoan_wrongBorrower (state : State) (borrower identifier : Nat) (loan : Borrowing.Loan)
    (live : state.legacy.shared.loans identifier = some loan) (wrong : loan.borrower ≠ borrower) :
    finishLoan state borrower identifier = .error (.legacy (.authority .wrongBorrower)) := by
  simp [finishLoan, Atomics.finishLoan, Borrowing.finishLoan, Borrowing.authorize, live, wrong, Except.mapError]

theorem authorize_wrongActor (state : State) (actor : Nat) (identifier : HandleId64) (handle : Handle)
    (live : state.handles identifier = some handle) (wrong : handle.actor ≠ actor) :
    authorize state actor identifier = .error .wrongActor := by
  simp [authorize, live, wrong]

/-- Surviving identities below an earlier frontier keep their original stored
records. The two frontiers never decrease, so removed IDs cannot be recycled. -/
structure Advances (before after : State) : Prop where
  cellFrontier : before.nextCell ≤ after.nextCell
  cells : ∀ identifier, identifier.index < before.nextCell → ∀ cell,
    after.cells identifier = some cell → before.cells identifier = some cell
  handleFrontier : before.nextHandle ≤ after.nextHandle
  handles : ∀ identifier, identifier.index < before.nextHandle → ∀ handle,
    after.handles identifier = some handle → before.handles identifier = some handle

theorem Advances.refl (state : State) : Advances state state :=
  ⟨Nat.le_refl _, fun _ _ _ live => live, Nat.le_refl _, fun _ _ _ live => live⟩

theorem Advances.trans {before middle after : State} (first : Advances before middle)
    (last : Advances middle after) : Advances before after := by
  refine ⟨Nat.le_trans first.cellFrontier last.cellFrontier, ?_,
    Nat.le_trans first.handleFrontier last.handleFrontier, ?_⟩
  · intro identifier below cell live
    exact first.cells identifier below cell
      (last.cells identifier (Nat.lt_of_lt_of_le below first.cellFrontier) cell live)
  · intro identifier below handle live
    exact first.handles identifier below handle
      (last.handles identifier (Nat.lt_of_lt_of_le below first.handleFrontier) handle live)

theorem installCell_advances (state : State) (cell : Cell) : Advances state (installCell state cell) := by
  refine ⟨by simp [installCell], ?_, Nat.le_refl _, fun _ _ _ live => live⟩
  intro identifier below stored live
  have different : identifier ≠ ⟨state.nextCell⟩ := by
    intro eq
    subst identifier
    exact Nat.lt_irrefl _ below
  simpa [installCell, different] using live

theorem installHandle_advances (state : State) (handle : Handle) : Advances state (installHandle state handle) := by
  refine ⟨Nat.le_refl _, fun _ _ _ live => live, by simp [installHandle], ?_⟩
  intro identifier below stored live
  have different : identifier ≠ ⟨state.nextHandle⟩ := by
    intro eq
    subst identifier
    exact Nat.lt_irrefl _ below
  simpa [installHandle, different] using live

theorem removeCell_advances (state : State) (identifier : CellId64) : Advances state (removeCell state identifier) :=
  ⟨Nat.le_refl _, fun _ _ _ live => removeCell_live live, Nat.le_refl _, fun _ _ _ live => live⟩

theorem removeHandle_advances (state : State) (identifier : HandleId64) : Advances state (removeHandle state identifier) :=
  ⟨Nat.le_refl _, fun _ _ _ live => live, Nat.le_refl _, fun _ _ _ live => removeHandle_live live⟩

theorem legacy_update_advances (state : State) (legacy : Atomics.State) :
    Advances state { state with legacy := legacy } :=
  ⟨Nat.le_refl _, fun _ _ _ live => live, Nat.le_refl _, fun _ _ _ live => live⟩

theorem enroll_advances (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (result : State × CellId64) (success : enroll state owner ticket address = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, _, _, same⟩ := enroll_ok _ _ _ _ _ success
  rw [same]
  exact installCell_advances _ _

theorem issue_advances (state : State) (owner : Nat) (identifier : CellId64) (actor : Nat)
    (result : State × HandleId64) (success : issue state owner identifier actor = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, same⟩ := issue_ok _ _ _ _ _ success
  rw [same]
  exact installHandle_advances _ _

theorem close_advances (state : State) (actor : Nat) (identifier : HandleId64) (after : State)
    (success : close state actor identifier = .ok after) : Advances state after := by
  obtain ⟨_, _, same⟩ := close_ok _ _ _ _ success
  rw [same]
  exact removeHandle_advances _ _

theorem retire_advances (state : State) (owner : Nat) (identifier : CellId64) (after : State)
    (success : retire state owner identifier = .ok after) : Advances state after := by
  obtain ⟨_, _, _, same⟩ := retire_ok _ _ _ _ success
  rw [same]
  exact removeCell_advances _ _

theorem mutate_advances (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, _, same⟩ := mutate_ok _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

theorem readBorrow_advances (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat)
    (success : readBorrow state lender ticket borrower region = .ok result) : Advances state result.1 := by
  obtain ⟨_, _, _, same⟩ := readBorrow_ok _ _ _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

theorem finishLoan_advances (state : State) (borrower identifier : Nat) (after : State)
    (success : finishLoan state borrower identifier = .ok after) : Advances state after := by
  obtain ⟨_, _, same⟩ := finishLoan_ok _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

theorem issue32_advances (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (address : Word) (result : State × Nat)
    (success : issue32 state owner ticket actor address = .ok result) : Advances state result.1 := by
  obtain ⟨_, _, _, same⟩ := issue32_ok _ _ _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

theorem close32_advances (state : State) (actor identifier : Nat) (after : State)
    (success : close32 state actor identifier = .ok after) : Advances state after := by
  obtain ⟨_, _, same⟩ := close32_ok _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

theorem logicalDiscard_advances (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalDiscard state actor identifier mask = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, _, _, _, _, _, same⟩ := logicalDiscard_ok _ _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

def CellRevoked (state : State) (identifier : CellId64) : Prop :=
  identifier.index < state.nextCell ∧ state.cells identifier = none

def HandleRevoked (state : State) (identifier : HandleId64) : Prop :=
  identifier.index < state.nextHandle ∧ state.handles identifier = none

theorem CellRevoked.persists {before after : State} {identifier : CellId64}
    (revoked : CellRevoked before identifier) (advances : Advances before after) : CellRevoked after identifier := by
  refine ⟨Nat.lt_of_lt_of_le revoked.1 advances.cellFrontier, ?_⟩
  cases found : after.cells identifier with
  | none => rfl
  | some cell =>
    have original := advances.cells identifier revoked.1 cell found
    rw [revoked.2] at original
    cases original

theorem HandleRevoked.persists {before after : State} {identifier : HandleId64}
    (revoked : HandleRevoked before identifier) (advances : Advances before after) : HandleRevoked after identifier := by
  refine ⟨Nat.lt_of_lt_of_le revoked.1 advances.handleFrontier, ?_⟩
  cases found : after.handles identifier with
  | none => rfl
  | some handle =>
    have original := advances.handles identifier revoked.1 handle found
    rw [revoked.2] at original
    cases original

theorem close_revokes (state : State) (actor : Nat) (identifier : HandleId64) (after : State)
    (valid : WellFormed state) (success : close state actor identifier = .ok after) : HandleRevoked after identifier := by
  obtain ⟨selected, authorized, same⟩ := close_ok _ _ _ _ success
  have live := (authorize_ok _ _ _ _ authorized).1
  subst after
  exact ⟨(valid.handles _ _ live).1, by simp [removeHandle]⟩

theorem retire_revokes (state : State) (owner : Nat) (identifier : CellId64) (after : State)
    (valid : WellFormed state) (success : retire state owner identifier = .ok after) : CellRevoked after identifier := by
  obtain ⟨cell, authorized, _, same⟩ := retire_ok _ _ _ _ success
  have live := (authorizeCell_ok _ _ _ _ authorized).1
  subst after
  exact ⟨(valid.cells _ _ live).1, by simp [removeCell]⟩

theorem HandleRevoked.unauthorized {state : State} {identifier : HandleId64}
    (revoked : HandleRevoked state identifier) (actor : Nat) :
    authorize state actor identifier = .error .missingHandle := by
  simp [authorize, revoked.2]

theorem HandleRevoked.logicalDiscard_denied {state : State} {identifier : HandleId64}
    (revoked : HandleRevoked state identifier) (actor : Nat) (mask : Word) :
    logicalDiscard state actor identifier mask = .error .missingHandle := by
  simp [logicalDiscard, revoked.unauthorized actor]

theorem CellRevoked.unauthorized {state : State} {identifier : CellId64}
    (revoked : CellRevoked state identifier) : currentCell state identifier = .error .missingCell := by
  simp [currentCell, revoked.2]

theorem CellRevoked.issue_denied {state : State} {identifier : CellId64}
    (revoked : CellRevoked state identifier) (owner actor : Nat) :
    issue state owner identifier actor = .error .missingCell := by
  simp [issue, authorizeCell, revoked.unauthorized]

/-- Even re-enrollment at the same raw address gets a different cell identity.
This theorem composes with CellRevoked.persists across admitted transitions. -/
theorem enroll_fresh_from_revoked (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (result : State × CellId64) (identifier : CellId64) (revoked : CellRevoked state identifier)
    (success : enroll state owner ticket address = .ok result) : result.2 ≠ identifier := by
  obtain ⟨_, _, _, _, same⟩ := enroll_ok _ _ _ _ _ success
  rw [same]
  intro eq
  have equal := congrArg CellId64.index eq
  have below := revoked.1
  change state.nextCell = identifier.index at equal
  omega

end EDSL.OS.Atomics64
