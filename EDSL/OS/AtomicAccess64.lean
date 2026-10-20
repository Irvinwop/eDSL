/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Preservation

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- An actual current-memory read with checked managed identities. A value is
not a reads-from witness: equal values may originate at different writes. -/
structure LoadEvent64 where
  actor : Nat
  handle : HandleId64
  cell : CellId64
  address : Word
  value : Word
  deriving DecidableEq, Repr

/-- Publication of one complete managed qword. This records neither an RMW nor
a source release operation, and has no implied instruction/RET interval. -/
structure StoreEvent64 where
  actor : Nat
  handle : HandleId64
  cell : CellId64
  address : Word
  value : Word
  deriving DecidableEq, Repr

/-- Reauthorize the current shared cell and read its actual published qword.
The state is unchanged. This primitive has no store-buffer forwarding or
acquire synchronization semantics; a scheduler must separately establish those
relations. The current normal-memory/address-profile assumptions of
`atomicAddressable64` remain external obligations. -/
def load (state : State) (actor : Nat) (identifier : HandleId64) :
    Except Fault (State × LoadEvent64) := do
  let selected ← authorize state actor identifier
  let value ← (loadQWord (toMemory state.legacy.shared.resources.space)
    selected.2.address).mapError Fault.machine
  return (state, ⟨actor, identifier, selected.1.cell, selected.2.address, value⟩)

/-- Publish one handle-authorized full64 value to the current managed cell.
The existing checked legacy store is private to this exact authorized
operation; ordinary mutations remain excluded by the managed reservation.

This is a shared-memory publication primitive, not instruction issue, source
release, or a claim about physical x86-TSO/Linux. A scheduler using buffered
stores must recheck its original cell identity and FIFO head before calling it.
No source ordering, reads-from relation or synchronization is established here. -/
def publishStore (state : State) (actor : Nat) (identifier : HandleId64) (value : Word) :
    Except Fault (State × StoreEvent64) := do
  let selected ← authorize state actor identifier
  let cell := selected.2
  let result ← (Atomics.mutate state.legacy
    (.store64 cell.owner cell.ticket cell.address value)).mapError Fault.legacy
  return ({ state with legacy := result.1 },
    ⟨actor, identifier, selected.1.cell, cell.address, value⟩)

theorem load_ok (state : State) (actor : Nat) (identifier : HandleId64)
    (result : State × LoadEvent64) (success : load state actor identifier = .ok result) :
    ∃ handle cell value,
      authorize state actor identifier = .ok (handle, cell) ∧
      loadQWord (toMemory state.legacy.shared.resources.space) cell.address = .ok value ∧
      result = (state, ⟨actor, identifier, handle.cell, cell.address, value⟩) := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [load, authorized] at success
  | ok selected =>
    cases read : loadQWord (toMemory state.legacy.shared.resources.space) selected.2.address with
    | error fault => simp [load, authorized, read, Except.mapError] at success
    | ok value =>
      simp [load, authorized, read, Except.mapError] at success
      exact ⟨selected.1, selected.2, value, rfl, read, success.symm⟩

theorem load_unchanged (state : State) (actor : Nat) (identifier : HandleId64)
    (result : State × LoadEvent64) (success : load state actor identifier = .ok result) :
    result.1 = state := by
  obtain ⟨_, _, _, _, _, same⟩ := load_ok _ _ _ _ success
  exact congrArg Prod.fst same

/-- Value and identities all come from this actual authorized current read. -/
theorem load_context (state : State) (actor : Nat) (identifier : HandleId64)
    (result : State × LoadEvent64) (success : load state actor identifier = .ok result) :
    ∃ handle cell,
      state.handles identifier = some handle ∧ handle.actor = actor ∧
      state.cells handle.cell = some cell ∧ ValidCell state.legacy.shared cell ∧
      result.2 = ⟨actor, identifier, handle.cell, cell.address, result.2.value⟩ ∧
      loadQWord (toMemory state.legacy.shared.resources.space) cell.address = .ok result.2.value := by
  obtain ⟨handle, cell, value, authorized, read, same⟩ := load_ok _ _ _ _ success
  obtain ⟨live, acts, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  subst result
  exact ⟨handle, cell, live, acts, linked, checked, rfl, read⟩

theorem load_read (state : State) (actor : Nat) (identifier : HandleId64)
    (result : State × LoadEvent64) (success : load state actor identifier = .ok result) :
    loadQWord (toMemory state.legacy.shared.resources.space) result.2.address = .ok result.2.value := by
  obtain ⟨_, _, _, _, read, same⟩ := load_ok _ _ _ _ success
  subst result
  exact read

/-- Current authorization alone derives read success; no desired value or
future operation is an admission premise. -/
theorem load_enabled (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    ∃ result, load state actor identifier = .ok result := by
  have checked := (authorize_ok _ _ _ _ authorized).2.2.2
  obtain ⟨value, read⟩ := checked.1.load_exists
  refine ⟨(state, ⟨actor, identifier, handle.cell, cell.address, value⟩), ?_⟩
  simp [load, authorized, read, Except.mapError]

theorem load_enabled_of_live (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (valid : WellFormed state) (live : state.handles identifier = some handle)
    (acts : handle.actor = actor) : ∃ result, load state actor identifier = .ok result := by
  obtain ⟨_, cell, linked⟩ := valid.handles _ _ live
  exact load_enabled _ _ _ _ _ (authorize_success _ _ _ _ _ valid live acts linked)

theorem load_enabled_iff (state : State) (actor : Nat) (identifier : HandleId64)
    (valid : WellFormed state) :
    (∃ result, load state actor identifier = .ok result) ↔
      ∃ handle, state.handles identifier = some handle ∧ handle.actor = actor := by
  constructor
  · rintro ⟨result, success⟩
    obtain ⟨handle, _, live, acts, _⟩ := load_context _ _ _ _ success
    exact ⟨handle, live, acts⟩
  · rintro ⟨handle, live, acts⟩
    exact load_enabled_of_live _ _ _ _ valid live acts

theorem load_wellFormed (state : State) (actor : Nat) (identifier : HandleId64)
    (result : State × LoadEvent64) (valid : WellFormed state)
    (success : load state actor identifier = .ok result) : WellFormed result.1 := by
  rw [load_unchanged _ _ _ _ success]
  exact valid

theorem load_frame (state : State) (actor : Nat) (identifier : HandleId64)
    (result : State × LoadEvent64) (success : load state actor identifier = .ok result)
    (query : Word) :
    result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query := by
  rw [load_unchanged _ _ _ _ success]

theorem load_denied (state : State) (actor : Nat) (identifier : HandleId64) (fault : Fault)
    (denied : authorize state actor identifier = .error fault) :
    load state actor identifier = .error fault := by
  simp [load, denied]

theorem publishStore_ok (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    ∃ handle cell legacy,
      authorize state actor identifier = .ok (handle, cell) ∧
      Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value) = .ok legacy ∧
      result = ({ state with legacy := legacy.1 },
        ⟨actor, identifier, handle.cell, cell.address, value⟩) := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [publishStore, authorized] at success
  | ok selected =>
    cases stored : Atomics.mutate state.legacy
        (.store64 selected.2.owner selected.2.ticket selected.2.address value) with
    | error fault => simp [publishStore, authorized, stored, Except.mapError] at success
    | ok legacy =>
      simp [publishStore, authorized, stored, Except.mapError] at success
      exact ⟨selected.1, selected.2, legacy, rfl, stored, success.symm⟩

theorem publishStore_guarded (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    ∃ handle cell,
      authorize state actor identifier = .ok (handle, cell) ∧
      result.2 = ⟨actor, identifier, handle.cell, cell.address, value⟩ ∧
      Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value) =
        .ok (result.1.legacy, none) := by
  obtain ⟨handle, cell, legacy, authorized, stored, same⟩ := publishStore_ok _ _ _ _ _ success
  obtain ⟨_, shared, changed, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  have noTicket : legacy.2 = none := by
    rw [legacyEq]
    exact Borrowing.store64_none changed
  subst result
  refine ⟨handle, cell, authorized, rfl, ?_⟩
  change Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value) =
    .ok (legacy.1, none)
  rw [← noTicket]
  exact stored

theorem publishStore_context (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    ∃ handle cell,
      state.handles identifier = some handle ∧ handle.actor = actor ∧
      state.cells handle.cell = some cell ∧ ValidCell state.legacy.shared cell ∧
      result.2 = ⟨actor, identifier, handle.cell, cell.address, value⟩ := by
  obtain ⟨handle, cell, authorized, eventEq, _⟩ := publishStore_guarded _ _ _ _ _ success
  obtain ⟨live, acts, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  exact ⟨handle, cell, live, acts, linked, checked, eventEq⟩

/-- Complete checked store effect, with no arithmetic or RMW interpretation. -/
structure PublishStoreEffect64 (before after : State) (event : StoreEvent64) : Prop where
  shared : Borrowing.StoreEffect64 before.legacy.shared after.legacy.shared event.address event.value
  cells : after.cells = before.cells
  nextCell : after.nextCell = before.nextCell
  handles : after.handles = before.handles
  nextHandle : after.nextHandle = before.nextHandle
  legacyHandles : after.legacy.handles = before.legacy.handles
  legacyNextHandle : after.legacy.nextHandle = before.legacy.nextHandle

theorem publishStore_effect (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    PublishStoreEffect64 state result.1 result.2 := by
  obtain ⟨_, _, _, _, stored, same⟩ := publishStore_ok _ _ _ _ _ success
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  obtain ⟨_, _, _, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  subst result
  exact ⟨effect, rfl, rfl, rfl, rfl, by rw [legacyEq], by rw [legacyEq]⟩

/-- Equality of the complete RAM/permission projection to the checked qword
primitive; this is stronger than equality of the selected word alone. -/
theorem publishStore_primitive (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    X86.storeQWord (toMemory state.legacy.shared.resources.space) result.2.address result.2.value =
      .ok (toMemory result.1.legacy.shared.resources.space) :=
  (publishStore_effect _ _ _ _ _ success).shared.machine

theorem publishStore_projection (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    toMemory result.1.legacy.shared.resources.space =
      writeQWordUnchecked (toMemory state.legacy.shared.resources.space) result.2.address result.2.value :=
  (publishStore_effect _ _ _ _ _ success).shared.projection

theorem publishStore_readback (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result) :
    loadQWord (toMemory result.1.legacy.shared.resources.space) result.2.address = .ok value := by
  obtain ⟨_, _, _, eventEq, _⟩ := publishStore_guarded _ _ _ _ _ success
  have read := (publishStore_effect _ _ _ _ _ success).shared.readback
  rw [eventEq] at read ⊢
  exact read

theorem publishStore_wellFormed (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64) (valid : WellFormed state)
    (success : publishStore state actor identifier value = .ok result) : WellFormed result.1 := by
  obtain ⟨_, _, _, _, stored, same⟩ := publishStore_ok _ _ _ _ _ success
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

/-- Current well-formed resources derive publication for every value, including
unchanged values. No desired successor or successful future store is assumed. -/
theorem publishStore_enabled (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (handle : Handle) (cell : Cell) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    ∃ result, publishStore state actor identifier value = .ok result := by
  obtain ⟨_, _, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  obtain ⟨allocation, authority, fits⟩ := checked.1.authorize
  obtain ⟨after, stored⟩ := Borrowing.store64_admitted state.legacy.shared cell.owner cell.ticket
    cell.address value allocation authority fits checked.1.writable (valid.noReaders _ _ linked)
  have permitted := legacy_allowed64 state handle.cell cell value valid linked
  have legacyStore : Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value) =
      .ok ({ state.legacy with shared := after }, none) := by
    simp [Atomics.mutate, permitted, stored, Except.mapError]
  refine ⟨({ state with legacy := { state.legacy with shared := after } },
    ⟨actor, identifier, handle.cell, cell.address, value⟩), ?_⟩
  simp [publishStore, authorized, legacyStore, Except.mapError]

theorem publishStore_enabled_of_live (state : State) (actor : Nat) (identifier : HandleId64)
    (value : Word) (handle : Handle) (valid : WellFormed state)
    (live : state.handles identifier = some handle) (acts : handle.actor = actor) :
    ∃ result, publishStore state actor identifier value = .ok result := by
  obtain ⟨_, cell, linked⟩ := valid.handles _ _ live
  exact publishStore_enabled _ _ _ _ _ _ valid (authorize_success _ _ _ _ _ valid live acts linked)

theorem publishStore_enabled_iff (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (valid : WellFormed state) :
    (∃ result, publishStore state actor identifier value = .ok result) ↔
      ∃ handle, state.handles identifier = some handle ∧ handle.actor = actor := by
  constructor
  · rintro ⟨result, success⟩
    obtain ⟨handle, _, live, acts, _⟩ := publishStore_context _ _ _ _ _ success
    exact ⟨handle, live, acts⟩
  · rintro ⟨handle, live, acts⟩
    exact publishStore_enabled_of_live _ _ _ _ _ valid live acts

theorem publishStore_frame (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result)
    (query : Word) (outside : ¬(qwordRegion result.2.address).Contains query) :
    result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query :=
  (publishStore_effect _ _ _ _ _ success).shared.outside query outside

/-- Live original loans retain all their bytes, independently of registers or
the region used by an eventual caller-return instruction. -/
theorem publishStore_loan_contents (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64) (valid : WellFormed state)
    (success : publishStore state actor identifier value = .ok result)
    (loanId : Nat) (loan : Borrowing.Loan) (live : state.legacy.shared.loans loanId = some loan) :
    ∀ query, loan.region.Contains query →
      result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query := by
  obtain ⟨_, _, _, _, stored⟩ := publishStore_guarded _ _ _ _ _ success
  have history : Borrowing.History state.legacy.shared result.1.legacy.shared :=
    .next (.mutate (legacy_store64_guarded stored)) .refl
  have effect := (publishStore_effect _ _ _ _ _ success).shared
  exact (history.loan_stable valid.legacy.shared loanId (valid.legacy.shared.2 _ _ live).1 loan
    ((congrFun effect.loans loanId).trans live)).2

theorem publishStore_loan_read (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64) (valid : WellFormed state)
    (success : publishStore state actor identifier value = .ok result)
    (borrower loanId : Nat) (address old : Word)
    (read : Borrowing.loadWord64 state.legacy.shared borrower loanId address = .ok old) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId address = .ok old := by
  obtain ⟨_, _, _, _, stored⟩ := publishStore_guarded _ _ _ _ _ success
  have history : Borrowing.History state.legacy.shared result.1.legacy.shared :=
    .next (.mutate (legacy_store64_guarded stored)) .refl
  obtain ⟨loan, authority, _, _⟩ := Borrowing.loadWord64_ok _ _ _ _ _ read
  have live := (Borrowing.authorize_ok _ _ _ _ authority).1
  apply history.loadWord64_stable valid.legacy.shared borrower loanId address old read
  rw [(publishStore_effect _ _ _ _ _ success).shared.loans, live]
  rfl

theorem publishStore_preserves_other (state : State) (actor : Nat) (handleId : HandleId64) (value : Word)
    (result : State × StoreEvent64) (valid : WellFormed state)
    (success : publishStore state actor handleId value = .ok result)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (other : identifier ≠ result.2.cell) :
    Ownership.PreservesAllocation state.legacy.shared.resources result.1.legacy.shared.resources
      cell.ticket.identifier := by
  obtain ⟨handle, target, authorized, eventEq, stored⟩ := publishStore_guarded _ _ _ _ _ success
  have targetLive := (authorize_ok _ _ _ _ authorized).2.2.1
  have different : cell.ticket.identifier ≠ target.ticket.identifier := by
    intro sameAllocation
    have sameId := valid.unique identifier cell handle.cell target live targetLive sameAllocation
    apply other
    rw [eventEq]
    exact sameId
  exact Borrowing.store64_preservesAllocation valid.legacy.shared.1 (legacy_store64_guarded stored)
    cell.ticket.identifier different

theorem publishStore_current_retained (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64)
    (success : publishStore state actor identifier value = .ok result)
    (owner : Nat) (ticket : Ownership.Ticket) :
    Ownership.Current result.1.legacy.shared.resources owner ticket ↔
      Ownership.Current state.legacy.shared.resources owner ticket := by
  unfold Ownership.Current
  rw [(publishStore_effect _ _ _ _ _ success).shared.allocations]

theorem publishStore_authority_retained (state : State) (actor : Nat) (identifier : HandleId64)
    (value : Word) (result : State × StoreEvent64) (valid : WellFormed state)
    (success : publishStore state actor identifier value = .ok result)
    (otherActor : Nat) (otherId : HandleId64) (handle : Handle) (cell : Cell)
    (live : state.handles otherId = some handle) (acts : handle.actor = otherActor)
    (linked : state.cells handle.cell = some cell) :
    authorize result.1 otherActor otherId = .ok (handle, cell) := by
  have effect := publishStore_effect _ _ _ _ _ success
  exact authorize_success _ _ _ _ _ (publishStore_wellFormed _ _ _ _ _ valid success)
    (by rwa [effect.handles]) acts (by rwa [effect.cells])

theorem publishStore_denied (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (fault : Fault) (denied : authorize state actor identifier = .error fault) :
    publishStore state actor identifier value = .error fault := by
  simp [publishStore, denied]

/-- Immediate peer observation in the abstract shared-memory state. The reader
uses its original live handle to the same persistent cell. This theorem has no
intervening scheduler actions and supplies no source reads-from identity. -/
theorem publishStore_load (state : State) (actor : Nat) (identifier : HandleId64) (value : Word)
    (result : State × StoreEvent64) (valid : WellFormed state)
    (success : publishStore state actor identifier value = .ok result)
    (reader : Nat) (readerId : HandleId64) (handle : Handle) (cell : Cell)
    (live : state.handles readerId = some handle) (acts : handle.actor = reader)
    (linked : state.cells handle.cell = some cell) (sameCell : result.2.cell = handle.cell) :
    load result.1 reader readerId =
      .ok (result.1, ⟨reader, readerId, handle.cell, cell.address, value⟩) := by
  have authorized := publishStore_authority_retained _ _ _ _ _ valid success
    reader readerId handle cell live acts linked
  obtain ⟨writer, target, writerAuthority, eventEq, _⟩ := publishStore_guarded _ _ _ _ _ success
  have targetLive := (authorize_ok _ _ _ _ writerAuthority).2.2.1
  have sameId : writer.cell = handle.cell := by simpa only [eventEq] using sameCell
  rw [sameId] at targetLive
  have targetEq : target = cell := Option.some.inj (targetLive.symm.trans linked)
  have read := publishStore_readback _ _ _ _ _ success
  rw [eventEq, targetEq] at read
  simp [load, authorized, read, Except.mapError]

end EDSL.OS.Atomics64
