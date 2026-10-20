/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Preservation
import EDSL.X86.AtomicAdd64

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- A current-authority arithmetic response, including the complete old word
in `arithmetic.event.before`. The delta and stored actor/handle/cell identities
are retained even when the sum is unchanged. This is not a logical operation
or a discarded-old response. Actor labels are modeled principals. -/
structure FetchAddEvent where
  actor : Nat
  handle : HandleId64
  cell : CellId64
  arithmetic : X86.FetchAddEvent64
  deriving DecidableEq, Repr

/-- One abstract functional OS-managed fetch-add transition on current full64
memory. Current authorization rechecks owner, epoch, whole8 containment,
alignment/address profile, every read/write permission and nonexecutable byte,
including for delta0. The private checked store exposes no intermediate state.

This is the managed-memory operation only: no instruction decoder, register or
flags result, scheduling/TSO history, linearizability, source-language ordering,
native Linux or physical LOCK refinement is claimed. The environmental
requirements documented by `atomicAddressable64` remain external obligations;
all access to managed allocations must respect this resource layer's gates. -/
def fetchAdd (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word) :
    Except Fault (State × FetchAddEvent) := do
  let selected ← authorize state actor identifier
  let cell := selected.2
  let old ← (loadQWord (toMemory state.legacy.shared.resources.space) cell.address).mapError Fault.machine
  let result ← (Atomics.mutate state.legacy
    (.store64 cell.owner cell.ticket cell.address (old + delta))).mapError Fault.legacy
  return ({ state with legacy := result.1 },
    ⟨actor, identifier, selected.1.cell, ⟨delta, ⟨cell.address, old, old + delta⟩⟩⟩)

theorem fetchAdd_ok (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    ∃ handle cell old legacy,
      authorize state actor identifier = .ok (handle, cell) ∧
      loadQWord (toMemory state.legacy.shared.resources.space) cell.address = .ok old ∧
      Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address (old + delta)) = .ok legacy ∧
      result = ({ state with legacy := legacy.1 },
        ⟨actor, identifier, handle.cell, ⟨delta, ⟨cell.address, old, old + delta⟩⟩⟩) := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [fetchAdd, authorized] at success
  | ok selected =>
    cases read : loadQWord (toMemory state.legacy.shared.resources.space) selected.2.address with
    | error fault => simp [fetchAdd, authorized, read, Except.mapError] at success
    | ok old =>
      cases stored : Atomics.mutate state.legacy
          (.store64 selected.2.owner selected.2.ticket selected.2.address (old + delta)) with
      | error fault => simp [fetchAdd, authorized, read, stored, Except.mapError] at success
      | ok legacy =>
        simp [fetchAdd, authorized, read, stored, Except.mapError] at success
        exact ⟨selected.1, selected.2, old, legacy, rfl, read, stored, success.symm⟩

theorem fetchAdd_guarded (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    ∃ handle cell, authorize state actor identifier = .ok (handle, cell) ∧
      result.2 = ⟨actor, identifier, handle.cell, ⟨delta, ⟨cell.address,
        result.2.arithmetic.event.before, result.2.arithmetic.event.before + delta⟩⟩⟩ ∧
      Atomics.mutate state.legacy
        (.store64 cell.owner cell.ticket cell.address result.2.arithmetic.event.after) =
          .ok (result.1.legacy, none) := by
  obtain ⟨handle, cell, old, legacy, authorized, _, stored, same⟩ := fetchAdd_ok _ _ _ _ _ success
  obtain ⟨_, _, sharedStore, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  have noTicket : legacy.2 = none := by
    rw [legacyEq]
    exact Borrowing.store64_none sharedStore
  subst result
  refine ⟨handle, cell, authorized, rfl, ?_⟩
  change Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address (old + delta)) =
    .ok (legacy.1, none)
  rw [← noTicket]
  exact stored

/-- Equality of the entire actual RAM projection, including permissions, to
the independently implemented full64 primitive and its typed arithmetic event. -/
theorem fetchAdd_primitive (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    fetchAddQWord (toMemory state.legacy.shared.resources.space) result.2.arithmetic.event.address delta =
      .ok (toMemory result.1.legacy.shared.resources.space, result.2.arithmetic) := by
  obtain ⟨_, cell, old, legacy, authorized, read, stored, same⟩ := fetchAdd_ok _ _ _ _ _ success
  have checked := (authorize_ok _ _ _ _ authorized).2.2.2
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  subst result
  rw [effect.projection]
  exact fetchAddQWord_success _ cell.address delta old checked.2.1 checked.1.writable read

theorem fetchAdd_sound (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    RMWTransition64 (toMemory state.legacy.shared.resources.space) result.2.arithmetic.event
      (toMemory result.1.legacy.shared.resources.space) ∧
    result.2.arithmetic.delta = delta ∧
    result.2.arithmetic.event.after = result.2.arithmetic.event.before + delta ∧
    result.2.actor = actor ∧ result.2.handle = identifier := by
  have primitive := fetchAddQWord_sound _ _ _ _ (fetchAdd_primitive _ _ _ _ _ success)
  obtain ⟨_, _, _, _, _, _, _, same⟩ := fetchAdd_ok _ _ _ _ _ success
  exact ⟨primitive.1, primitive.2.1, primitive.2.2.2, by rw [same], by rw [same]⟩

/-- Independent natural-number specification of the modular sum. -/
theorem fetchAdd_modular (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    result.2.arithmetic.event.after.toNat =
      (result.2.arithmetic.event.before.toNat + delta.toNat) % 2^64 :=
  fetchAddQWord_modular _ _ _ _ (fetchAdd_primitive _ _ _ _ _ success)

theorem fetchAdd_old (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    loadQWord (toMemory state.legacy.shared.resources.space) result.2.arithmetic.event.address =
      .ok result.2.arithmetic.event.before :=
  (fetchAdd_sound _ _ _ _ _ success).1.2.2.1

theorem fetchAdd_readback (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    loadQWord (toMemory result.1.legacy.shared.resources.space) result.2.arithmetic.event.address =
      .ok result.2.arithmetic.event.after :=
  (fetchAdd_sound _ _ _ _ _ success).1.readback

/-- Typed arithmetic wrapper around the operation-neutral checked store effect.
No logical event is constructed to reuse byte-store or ownership proofs. -/
structure FetchAddEffect (before after : State) (event : FetchAddEvent) : Prop where
  shared : Borrowing.StoreEffect64 before.legacy.shared after.legacy.shared
    event.arithmetic.event.address event.arithmetic.event.after
  cells : after.cells = before.cells
  nextCell : after.nextCell = before.nextCell
  handles : after.handles = before.handles
  nextHandle : after.nextHandle = before.nextHandle
  legacyHandles : after.legacy.handles = before.legacy.handles
  legacyNextHandle : after.legacy.nextHandle = before.legacy.nextHandle

theorem fetchAdd_effect (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    FetchAddEffect state result.1 result.2 := by
  obtain ⟨_, _, _, _, _, _, stored, same⟩ := fetchAdd_ok _ _ _ _ _ success
  have effect := Borrowing.store64_effect (legacy_store64_guarded stored)
  obtain ⟨_, _, _, legacyEq⟩ := Atomics.mutate_ok _ _ _ stored
  subst result
  exact ⟨effect, rfl, rfl, rfl, rfl, by rw [legacyEq], by rw [legacyEq]⟩

theorem fetchAdd_wellFormed (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result) : WellFormed result.1 := by
  obtain ⟨_, _, _, _, _, _, stored, same⟩ := fetchAdd_ok _ _ _ _ _ success
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

/-- Current resource invariants and authorization derive success for every
delta. No successful future store or future execution is assumed. -/
theorem fetchAdd_enabled (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (handle : Handle) (cell : Cell) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    ∃ result, fetchAdd state actor identifier delta = .ok result := by
  obtain ⟨_, _, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  obtain ⟨allocation, authority, fits⟩ := checked.1.authorize
  obtain ⟨old, read⟩ := checked.1.load_exists
  obtain ⟨after, stored⟩ := Borrowing.store64_admitted state.legacy.shared cell.owner cell.ticket
    cell.address (old + delta) allocation authority fits checked.1.writable (valid.noReaders _ _ linked)
  have permitted := legacy_allowed64 state handle.cell cell (old + delta) valid linked
  have legacyStore : Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address (old + delta)) =
      .ok ({ state.legacy with shared := after }, none) := by
    simp [Atomics.mutate, permitted, stored, Except.mapError]
  refine ⟨({ state with legacy := { state.legacy with shared := after } },
    ⟨actor, identifier, handle.cell, ⟨delta, ⟨cell.address, old, old + delta⟩⟩⟩), ?_⟩
  simp [fetchAdd, authorized, read, legacyStore, Except.mapError]

theorem fetchAdd_enabled_of_live (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (handle : Handle) (valid : WellFormed state) (live : state.handles identifier = some handle)
    (acts : handle.actor = actor) : ∃ result, fetchAdd state actor identifier delta = .ok result := by
  obtain ⟨_, cell, linked⟩ := valid.handles _ _ live
  exact fetchAdd_enabled _ _ _ _ _ _ valid (authorize_success _ _ _ _ _ valid live acts linked)

theorem fetchAdd_enabled_iff (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (valid : WellFormed state) :
    (∃ result, fetchAdd state actor identifier delta = .ok result) ↔
      ∃ handle, state.handles identifier = some handle ∧ handle.actor = actor := by
  constructor
  · rintro ⟨result, success⟩
    obtain ⟨handle, _, authorized, _, _⟩ := fetchAdd_guarded _ _ _ _ _ success
    have checked := authorize_ok _ _ _ _ authorized
    exact ⟨handle, checked.1, checked.2.1⟩
  · rintro ⟨handle, live, acts⟩
    exact fetchAdd_enabled_of_live _ _ _ _ _ valid live acts

/-- Actual selected identities and present allocation owner/epoch/full8 validity,
independent of WellFormed or an issuance-time authority snapshot. -/
theorem fetchAdd_context (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    ∃ handle cell, state.handles identifier = some handle ∧ handle.actor = actor ∧
      state.cells handle.cell = some cell ∧ ValidCell state.legacy.shared cell ∧
      result.2.cell = handle.cell ∧ result.2.arithmetic.event.address = cell.address := by
  obtain ⟨handle, cell, authorized, eventEq, _⟩ := fetchAdd_guarded _ _ _ _ _ success
  obtain ⟨live, acts, linked, checked⟩ := authorize_ok _ _ _ _ authorized
  exact ⟨handle, cell, live, acts, linked, checked, by rw [eventEq], by rw [eventEq]⟩

theorem fetchAdd_identity (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (handle : Handle) (cell : Cell)
    (success : fetchAdd state actor identifier delta = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    result.2.cell = handle.cell ∧ result.2.arithmetic.event.address = cell.address := by
  obtain ⟨_, _, observed, eventEq, _⟩ := fetchAdd_guarded _ _ _ _ _ success
  have same := Except.ok.inj (authorized.symm.trans observed)
  cases same
  rw [eventEq]
  exact ⟨rfl, rfl⟩

/-- All eight bytes were present, readable, writable and nonexecutable in the
current state, even for an unchanged result. -/
theorem fetchAdd_full_permissions (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result)
    (offset : Nat) (bound : offset < 8) :
    let memory := toMemory state.legacy.shared.resources.space
    let address := result.2.arithmetic.event.address + BitVec.ofNat 64 offset
    memory.writable address = true ∧ (memory.read address).isSome = true ∧
      memory.executable address = false := by
  have permissions := (fetchAdd_sound _ _ _ _ _ success).1.full_permissions offset bound
  obtain ⟨_, cell, _, _, _, checked, _, addressEq⟩ := fetchAdd_context _ _ _ _ _ success
  refine ⟨permissions.1, permissions.2, ?_⟩
  rw [addressEq]
  exact dataOnly64_bytes _ _ checked.2.2 offset bound

/-- Every allocation record is byte-for-byte identical, retaining identity,
owner, epoch and region; allocation and loan frontiers are part of the effect. -/
theorem fetchAdd_current_retained (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result)
    (owner : Nat) (ticket : Ownership.Ticket) :
    Ownership.Current result.1.legacy.shared.resources owner ticket ↔
      Ownership.Current state.legacy.shared.resources owner ticket := by
  unfold Ownership.Current
  rw [(fetchAdd_effect _ _ _ _ _ success).shared.allocations]

theorem fetchAdd_reserved (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result)
    (cellId : CellId64) (cell : Cell) (live : state.cells cellId = some cell) :
    reserved result.1 cell.ticket.identifier = true := by
  have effect := fetchAdd_effect _ _ _ _ _ success
  simpa only [reserved, effect.cells, effect.nextCell] using reserved_of_live state valid cellId cell live

theorem fetchAdd_blocks_mutation (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result)
    (cellId : CellId64) (cell : Cell) (live : state.cells cellId = some cell)
    (operation : Ownership.Mutation) (target : operation.target = some cell.ticket.identifier) :
    mutate result.1 operation = .error .reserved := by
  exact mutate_reserved _ _ (fetchAdd_wellFormed _ _ _ _ _ valid success) cellId cell
    (by rwa [(fetchAdd_effect _ _ _ _ _ success).cells]) target

theorem fetchAdd_authority_retained (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result)
    (otherActor : Nat) (otherId : HandleId64) (handle : Handle) (cell : Cell)
    (live : state.handles otherId = some handle) (acts : handle.actor = otherActor)
    (linked : state.cells handle.cell = some cell) :
    authorize result.1 otherActor otherId = .ok (handle, cell) := by
  have effect := fetchAdd_effect _ _ _ _ _ success
  exact authorize_success _ _ _ _ _ (fetchAdd_wellFormed _ _ _ _ _ valid success)
    (by rwa [effect.handles]) acts (by rwa [effect.cells])

theorem fetchAdd_frame (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result)
    (query : Word) (outside : ¬(qwordRegion result.2.arithmetic.event.address).Contains query) :
    result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query :=
  (fetchAdd_effect _ _ _ _ _ success).shared.outside query outside

theorem fetchAdd_preserves_code (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result)
    (base : Word) (bytes : List Byte) (code : CodeAt (toMemory state.legacy.shared.resources.space) base bytes)
    (disjoint : QWordDisjoint result.2.arithmetic.event.address base bytes.length) :
    CodeAt (toMemory result.1.legacy.shared.resources.space) base bytes :=
  (fetchAdd_sound _ _ _ _ _ success).1.preserves_code base bytes code disjoint

/-- The original caller slot is an explicit address, independent of RSP or any
instruction/return semantics. This preserves the existing RET read primitive. -/
theorem fetchAdd_preserves_caller (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result)
    (stack returnAddress : Word)
    (caller : readWord (toMemory state.legacy.shared.resources.space) stack = .ok returnAddress)
    (disjoint : QWordDisjoint result.2.arithmetic.event.address stack 8) :
    readWord (toMemory result.1.legacy.shared.resources.space) stack = .ok returnAddress := by
  apply Eq.trans (readWord_congr _ _ _ ?_) caller
  intro offset bound
  exact (fetchAdd_sound _ _ _ _ _ success).1.frame _ (disjoint offset bound)

theorem fetchAdd_loan_contents (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result)
    (loanId : Nat) (loan : Borrowing.Loan) (live : state.legacy.shared.loans loanId = some loan) :
    ∀ query, loan.region.Contains query →
      result.1.legacy.shared.resources.space.cells query = state.legacy.shared.resources.space.cells query := by
  obtain ⟨_, _, _, _, stored⟩ := fetchAdd_guarded _ _ _ _ _ success
  have history : Borrowing.History state.legacy.shared result.1.legacy.shared :=
    .next (.mutate (legacy_store64_guarded stored)) .refl
  have effect := (fetchAdd_effect _ _ _ _ _ success).shared
  exact (history.loan_stable valid.legacy.shared loanId (valid.legacy.shared.2 _ _ live).1 loan
    ((congrFun effect.loans loanId).trans live)).2

theorem fetchAdd_loan_read (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor identifier delta = .ok result)
    (borrower loanId : Nat) (address value : Word)
    (read : Borrowing.loadWord64 state.legacy.shared borrower loanId address = .ok value) :
    Borrowing.loadWord64 result.1.legacy.shared borrower loanId address = .ok value := by
  obtain ⟨_, _, _, _, stored⟩ := fetchAdd_guarded _ _ _ _ _ success
  have history : Borrowing.History state.legacy.shared result.1.legacy.shared :=
    .next (.mutate (legacy_store64_guarded stored)) .refl
  obtain ⟨loan, authority, _, _⟩ := Borrowing.loadWord64_ok _ _ _ _ _ read
  have live := (Borrowing.authorize_ok _ _ _ _ authority).1
  apply history.loadWord64_stable valid.legacy.shared borrower loanId address value read
  rw [(fetchAdd_effect _ _ _ _ _ success).shared.loans, live]
  rfl

theorem fetchAdd_preserves_other (state : State) (actor : Nat) (handleId : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (valid : WellFormed state)
    (success : fetchAdd state actor handleId delta = .ok result)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell)
    (other : identifier ≠ result.2.cell) :
    Ownership.PreservesAllocation state.legacy.shared.resources result.1.legacy.shared.resources
      cell.ticket.identifier := by
  obtain ⟨handle, target, authorized, eventEq, stored⟩ := fetchAdd_guarded _ _ _ _ _ success
  have targetLive := (authorize_ok _ _ _ _ authorized).2.2.1
  have different : cell.ticket.identifier ≠ target.ticket.identifier := by
    intro sameAllocation
    have sameId := valid.unique identifier cell handle.cell target live targetLive sameAllocation
    apply other
    rw [eventEq]
    exact sameId
  exact Borrowing.store64_preservesAllocation valid.legacy.shared.1 (legacy_store64_guarded stored)
    cell.ticket.identifier different

theorem fetchAdd_advances (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (result : State × FetchAddEvent) (success : fetchAdd state actor identifier delta = .ok result) :
    Advances state result.1 := by
  obtain ⟨_, _, _, _, _, _, _, same⟩ := fetchAdd_ok _ _ _ _ _ success
  rw [same]
  exact legacy_update_advances _ _

/-- Failure carries only a fault, never a partial state/event. Current
authorization failure precedes every read and mutation, including for delta0. -/
theorem fetchAdd_authorize_error (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (fault : Fault) (denied : authorize state actor identifier = .error fault) :
    fetchAdd state actor identifier delta = .error fault := by
  simp [fetchAdd, denied]

theorem fetchAdd_wrongActor (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (handle : Handle) (live : state.handles identifier = some handle) (wrong : handle.actor ≠ actor) :
    fetchAdd state actor identifier delta = .error .wrongActor :=
  fetchAdd_authorize_error _ _ _ _ _ (authorize_wrongActor _ _ _ _ live wrong)

theorem HandleRevoked.fetchAdd_denied {state : State} {identifier : HandleId64}
    (revoked : HandleRevoked state identifier) (actor : Nat) (delta : Word) :
    fetchAdd state actor identifier delta = .error .missingHandle :=
  fetchAdd_authorize_error _ _ _ _ _ (revoked.unauthorized actor)

theorem CellRevoked.fetchAdd_denied {state : State} {identifier : CellId64}
    (revoked : CellRevoked state identifier) (actor : Nat) (handleId : HandleId64) (delta : Word)
    (handle : Handle) (live : state.handles handleId = some handle) (acts : handle.actor = actor)
    (linked : handle.cell = identifier) :
    fetchAdd state actor handleId delta = .error .missingCell := by
  apply fetchAdd_authorize_error
  simp [authorize, live, acts, linked, revoked.unauthorized]

theorem fetchAdd_ownership_denied (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (handle : Handle) (cell : Cell) (fault : Ownership.Fault)
    (live : state.handles identifier = some handle) (acts : handle.actor = actor)
    (linked : state.cells handle.cell = some cell)
    (denied : Ownership.authorize state.legacy.shared.resources cell.owner cell.ticket = .error fault) :
    fetchAdd state actor identifier delta = .error (.ownership fault) := by
  simp [fetchAdd, authorize, live, acts, currentCell, linked, validateCell, denied, Except.mapError]

/-- Every current cell validation error propagates unchanged, regardless of
delta. This includes whole8, address-profile, permission and executable gates. -/
theorem fetchAdd_validation_denied (state : State) (actor : Nat) (identifier : HandleId64) (delta : Word)
    (handle : Handle) (cell : Cell) (fault : Fault)
    (live : state.handles identifier = some handle) (acts : handle.actor = actor)
    (linked : state.cells handle.cell = some cell) (denied : validateCell state cell = .error fault) :
    fetchAdd state actor identifier delta = .error fault := by
  simp [fetchAdd, authorize, live, acts, currentCell, linked, denied]

end EDSL.OS.Atomics64
