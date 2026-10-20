/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Logical
import EDSL.OS.Atomics64.Preservation

namespace EDSL.OS.Atomics64
open X86 AddressSpace

theorem logicalUpdate_guarded (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalUpdate op state actor identifier mask = .ok result) :
    ∃ handle cell, authorize state actor identifier = .ok (handle, cell) ∧
      result.2 = ⟨actor, identifier, handle.cell, ⟨op, mask, ⟨cell.address,
        result.2.logical.event.before, Sequential.LogicalOp.eval op result.2.logical.event.before mask⟩⟩⟩ ∧
      Atomics.mutate state.legacy
        (.store64 cell.owner cell.ticket cell.address result.2.logical.event.after) =
          .ok (result.1.legacy, none) := by
  obtain ⟨handle, cell, old, legacy, authorized, _, stored, same⟩ := logicalUpdate_ok _ _ _ _ _ _ success
  obtain ⟨_, shared, sharedStore, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  have noTicket : legacy.2 = none := by
    rw [legacyEq]
    exact Borrowing.store64_none sharedStore
  subst result
  refine ⟨handle, cell, authorized, rfl, ?_⟩
  change Atomics.mutate state.legacy
    (.store64 cell.owner cell.ticket cell.address (Sequential.LogicalOp.eval op old mask)) =
      .ok (legacy.1, none)
  rw [← noTicket]
  exact stored

/-- Complete projected RAM agrees with one full64 RMWTransition64, and the
operation/mask are fixed by this checked logical operation. No store-only atomicity
claim or ABI old-value result is involved. -/
theorem logicalUpdate_sound (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalUpdate op state actor identifier mask = .ok result) :
    RMWTransition64 (toMemory state.legacy.shared.resources.space) result.2.logical.event
      (toMemory result.1.legacy.shared.resources.space) ∧
    result.2.logical.op = op ∧ result.2.logical.mask = mask ∧
    result.2.logical.event.after = Sequential.LogicalOp.eval op result.2.logical.event.before mask ∧
    result.2.actor = actor ∧ result.2.handle = identifier := by
  obtain ⟨handle, cell, old, legacy, authorized, read, stored, same⟩ := logicalUpdate_ok _ _ _ _ _ _ success
  have checked := (authorize_ok _ _ _ _ authorized).2.2.2
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  subst result
  exact ⟨⟨checked.2.1, checked.1.writable, read, effect.projection⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem logicalUpdate_primitive (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalUpdate op state actor identifier mask = .ok result) :
    logicalRmwQWord op (toMemory state.legacy.shared.resources.space) result.2.logical.event.address mask =
      .ok (toMemory result.1.legacy.shared.resources.space, result.2.logical) := by
  obtain ⟨handle, cell, old, legacy, authorized, read, stored, same⟩ := logicalUpdate_ok _ _ _ _ _ _ success
  have checked := (authorize_ok _ _ _ _ authorized).2.2.2
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  subst result
  rw [effect.projection]
  exact logicalRmwQWord_success op _ cell.address mask old checked.2.1 checked.1.writable read

/-- The existing operation-neutral effect retains allocation metadata, all
registry frontiers, loans, permissions, and every byte outside the operand. -/
theorem logicalUpdate_effect (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalUpdate op state actor identifier mask = .ok result) :
    Effect state result.1 result.2 := by
  obtain ⟨_, _, _, legacy, _, _, stored, same⟩ := logicalUpdate_ok _ _ _ _ _ _ success
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  obtain ⟨_, _, _, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  subst result
  exact ⟨effect, rfl, rfl, rfl, rfl, by rw [legacyEq], by rw [legacyEq]⟩

theorem logicalUpdate_wellFormed (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (valid : WellFormed state)
    (success : logicalUpdate op state actor identifier mask = .ok result) : WellFormed result.1 := by
  obtain ⟨_, _, _, legacy, _, _, stored, same⟩ := logicalUpdate_ok _ _ _ _ _ _ success
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
/-- Every present actor handle admits every mask, including unchanged results.
Success is derived from current authority and resource invariants, rather than
assumed as a future-execution premise. -/
theorem logicalUpdate_enabled (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (handle : Handle) (cell : Cell) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    ∃ result, logicalUpdate op state actor identifier mask = .ok result := by
  obtain ⟨_, _, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  obtain ⟨allocation, authority, fits⟩ := checked.1.authorize
  obtain ⟨old, read⟩ := checked.1.load_exists
  let value := Sequential.LogicalOp.eval op old mask
  obtain ⟨after, stored⟩ := Borrowing.store64_admitted state.legacy.shared cell.owner cell.ticket
    cell.address value allocation authority fits checked.1.writable (valid.noReaders _ _ linked)
  have permitted := legacy_allowed64 state handle.cell cell value valid linked
  have legacyStore : Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value) =
      .ok ({ state.legacy with shared := after }, none) := by
    simp [Atomics.mutate, permitted, stored, Except.mapError]
  refine ⟨({ state with legacy := { state.legacy with shared := after } },
    ⟨actor, identifier, handle.cell, ⟨op, mask, ⟨cell.address, old, value⟩⟩⟩), ?_⟩
  simp [logicalUpdate, authorized, read, legacyStore, Except.mapError, value]

theorem logicalUpdate_enabled_of_live (op : Sequential.LogicalOp) (state : State)
    (actor : Nat) (identifier : HandleId64) (mask : Word) (handle : Handle) (cell : Cell)
    (valid : WellFormed state) (live : state.handles identifier = some handle)
    (acts : handle.actor = actor) (linked : state.cells handle.cell = some cell) :
    ∃ result, logicalUpdate op state actor identifier mask = .ok result :=
  logicalUpdate_enabled op state actor identifier mask handle cell valid
    (authorize_success state actor identifier handle cell valid live acts linked)

/-- The actual event's identities come from the stored handle and current cell,
including allocation/epoch and nonexecutable full64 operand validity. -/
theorem logicalUpdate_context (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (result : State × Event)
    (success : logicalUpdate op state actor identifier mask = .ok result) :
    ∃ handle cell, state.handles identifier = some handle ∧ handle.actor = actor ∧
      state.cells handle.cell = some cell ∧ ValidCell state.legacy.shared cell ∧
      result.2.cell = handle.cell ∧ result.2.logical.event.address = cell.address := by
  obtain ⟨handle, cell, authorized, eventEq, _⟩ := logicalUpdate_guarded _ _ _ _ _ _ success
  obtain ⟨live, acts, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  exact ⟨handle, cell, live, acts, linked, checked, by rw [eventEq], by rw [eventEq]⟩

/-- With a supplied checked current selection, the event retains that exact
cell identity and operand address. -/
theorem logicalUpdate_identity (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (result : State × Event) (handle : Handle) (cell : Cell)
    (success : logicalUpdate op state actor identifier mask = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    result.2.cell = handle.cell ∧ result.2.logical.event.address = cell.address := by
  obtain ⟨selected, target, observed, eventEq, _⟩ := logicalUpdate_guarded _ _ _ _ _ _ success
  have same := Except.ok.inj (authorized.symm.trans observed)
  cases same
  rw [eventEq]
  exact ⟨rfl, rfl⟩

/-- Logical updates retain persistent registration even after a no-change RMW;
the allocation does not become available to ordinary mutations. -/
theorem logicalUpdate_reserved (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (result : State × Event)
    (valid : WellFormed state) (success : logicalUpdate op state actor identifier mask = .ok result)
    (cellId : CellId64) (cell : Cell) (live : state.cells cellId = some cell) :
    reserved result.1 cell.ticket.identifier = true := by
  have effect := logicalUpdate_effect _ _ _ _ _ _ success
  simpa only [reserved, effect.cells, effect.nextCell] using reserved_of_live state valid cellId cell live

/-- Other actors' stored handles remain live and must reauthorize against the
returned current memory, rather than retaining an issuance-time value. -/
theorem logicalUpdate_authority_retained (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (result : State × Event)
    (valid : WellFormed state) (success : logicalUpdate op state actor identifier mask = .ok result)
    (otherActor : Nat) (otherId : HandleId64) (handle : Handle) (cell : Cell)
    (live : state.handles otherId = some handle) (acts : handle.actor = otherActor)
    (linked : state.cells handle.cell = some cell) :
    authorize result.1 otherActor otherId = .ok (handle, cell) := by
  have effect := logicalUpdate_effect _ _ _ _ _ _ success
  exact authorize_success _ _ _ _ _ (logicalUpdate_wellFormed _ _ _ _ _ _ valid success)
    (by rwa [effect.handles]) acts (by rwa [effect.cells])

/-- The checked RMW retains actual bytes of every pre-existing ordinary loan. -/
theorem logicalUpdate_loan_contents (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (valid : WellFormed state)
    (success : logicalUpdate op state actor identifier mask = .ok result)
    (loanId : Nat) (loan : Borrowing.Loan) (live : state.legacy.shared.loans loanId = some loan) :
    ∀ query, loan.region.Contains query →
      result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query := by
  obtain ⟨_, _, _, _, stored⟩ := logicalUpdate_guarded _ _ _ _ _ _ success
  have gate := legacy_store64_guarded stored
  have history : Borrowing.History state.legacy.shared result.1.legacy.shared := .next (.mutate gate) .refl
  have effect := (logicalUpdate_effect _ _ _ _ _ _ success).shared
  exact (history.loan_stable valid.legacy.shared loanId (valid.legacy.shared.2 _ _ live).1 loan
    ((congrFun effect.loans loanId).trans live)).2


theorem logicalUpdate_preserves_other (op : Sequential.LogicalOp) (state : State) (actor : Nat) (handleId : HandleId64) (mask : Word)
    (result : State × Event) (valid : WellFormed state)
    (success : logicalUpdate op state actor handleId mask = .ok result)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (other : identifier ≠ result.2.cell) :
    Ownership.PreservesAllocation state.legacy.shared.resources result.1.legacy.shared.resources
      cell.ticket.identifier := by
  obtain ⟨handle, target, authorized, eventEq, stored⟩ := logicalUpdate_guarded _ _ _ _ _ _ success
  have targetLive := (authorize_ok _ _ _ _ authorized).2.2.1
  have different : cell.ticket.identifier ≠ target.ticket.identifier := by
    intro sameAllocation
    have sameId := valid.unique identifier cell handle.cell target live targetLive sameAllocation
    apply other
    rw [eventEq]
    exact sameId
  exact Borrowing.store64_preservesAllocation valid.legacy.shared.1 (legacy_store64_guarded stored)
    cell.ticket.identifier different

theorem logicalUpdate_advances (op : Sequential.LogicalOp) (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalUpdate op state actor identifier mask = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, _, _, _, _, _, same⟩ := logicalUpdate_ok _ _ _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

/-- Failure of current authorization propagates before any read or mutation. -/
theorem logicalUpdate_authorize_error (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (fault : Fault)
    (denied : authorize state actor identifier = .error fault) :
    logicalUpdate op state actor identifier mask = .error fault := by
  simp [logicalUpdate, denied]

theorem logicalUpdate_wrongActor (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (handle : Handle)
    (live : state.handles identifier = some handle) (wrong : handle.actor ≠ actor) :
    logicalUpdate op state actor identifier mask = .error .wrongActor :=
  logicalUpdate_authorize_error op state actor identifier mask .wrongActor
    (authorize_wrongActor state actor identifier handle live wrong)

theorem HandleRevoked.logicalUpdate_denied {state : State} {identifier : HandleId64}
    (revoked : HandleRevoked state identifier) (op : Sequential.LogicalOp) (actor : Nat) (mask : Word) :
    logicalUpdate op state actor identifier mask = .error .missingHandle :=
  logicalUpdate_authorize_error op state actor identifier mask .missingHandle (revoked.unauthorized actor)

/-- This also covers a hostile present-state handle still naming a revoked cell;
the handle cannot resurrect retired allocation authority. -/
theorem CellRevoked.logicalUpdate_denied {state : State} {identifier : CellId64}
    (revoked : CellRevoked state identifier) (op : Sequential.LogicalOp) (actor : Nat)
    (handleId : HandleId64) (mask : Word) (handle : Handle)
    (live : state.handles handleId = some handle) (acts : handle.actor = actor)
    (linked : handle.cell = identifier) :
    logicalUpdate op state actor handleId mask = .error .missingCell := by
  apply logicalUpdate_authorize_error
  simp [authorize, live, acts, linked, revoked.unauthorized]

/-- Stale epochs, missing allocations and wrong owners are rechecked on the
current resource state, even if the handle record itself is still present. -/
theorem logicalUpdate_ownership_denied (op : Sequential.LogicalOp) (state : State)
    (actor : Nat) (identifier : HandleId64) (mask : Word) (handle : Handle) (cell : Cell)
    (fault : Ownership.Fault) (live : state.handles identifier = some handle)
    (acts : handle.actor = actor) (linked : state.cells handle.cell = some cell)
    (denied : Ownership.authorize state.legacy.shared.resources cell.owner cell.ticket = .error fault) :
    logicalUpdate op state actor identifier mask = .error (.ownership fault) := by
  simp [logicalUpdate, authorize, live, acts, currentCell, linked, validateCell, denied, Except.mapError]

end EDSL.OS.Atomics64
