/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Model

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- Recheck present owner/epoch, complete allocation containment and all eight
operand bytes. No spawn-time value or future execution is used as authority. -/
def validateCell (state : State) (cell : Cell) : Except Fault Unit := do
  let allocation ← (Ownership.authorize state.legacy.shared.resources cell.owner cell.ticket).mapError Fault.ownership
  if !Ownership.containsQWord allocation cell.address then throw (.ownership .outsideAllocation)
  if !atomicAddressable64 cell.address then throw (.machine (.unsupportedAtomicAddress cell.address))
  if !canStoreQWord (toMemory state.legacy.shared.resources.space) cell.address then
    throw (.machine (.writeDenied cell.address))
  if !dataOnly64 (toMemory state.legacy.shared.resources.space) cell.address then throw .executable
  return ()

def currentCell (state : State) (identifier : CellId64) : Except Fault Cell := do
  match state.cells identifier with
  | none => throw .missingCell
  | some cell =>
    let _ ← validateCell state cell
    return cell

def authorizeCell (state : State) (owner : Nat) (identifier : CellId64) : Except Fault Cell := do
  let cell ← currentCell state identifier
  if cell.owner = owner then return cell else throw .wrongOwner

/-- Enroll one persistent cell, reserving its entire allocation. A legacy32
reservation or any ordinary read loan on any subregion excludes enrollment. -/
def enroll (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word) :
    Except Fault (State × CellId64) := do
  let cell : Cell := ⟨owner, ticket, address⟩
  let _ ← validateCell state cell
  if (state.cells ⟨state.nextCell⟩).isSome then throw .identityCollision
  if reserved state ticket.identifier then throw .reserved
  if Atomics.reserved state.legacy ticket.identifier then throw .legacyReservation
  if !Borrowing.allowed state.legacy.shared (.store64 owner ticket address 0) then throw .borrowed
  return (installCell state cell, ⟨state.nextCell⟩)

def issue (state : State) (owner : Nat) (identifier : CellId64) (actor : Nat) :
    Except Fault (State × HandleId64) := do
  let _ ← authorizeCell state owner identifier
  if (state.handles ⟨state.nextHandle⟩).isSome then throw .identityCollision
  return (installHandle state ⟨actor, identifier⟩, ⟨state.nextHandle⟩)

def authorize (state : State) (actor : Nat) (identifier : HandleId64) : Except Fault (Handle × Cell) := do
  match state.handles identifier with
  | none => throw .missingHandle
  | some handle =>
    if handle.actor ≠ actor then throw .wrongActor
    let cell ← currentCell state handle.cell
    return (handle, cell)

def close (state : State) (actor : Nat) (identifier : HandleId64) : Except Fault State := do
  let _ ← authorize state actor identifier
  return removeHandle state identifier

/-- No handles may remain. This ends managed atomic mode; it does not release
or destroy the allocation, and is not a proof of native C destruction/free. -/
def retire (state : State) (owner : Nat) (identifier : CellId64) : Except Fault State := do
  let _ ← authorizeCell state owner identifier
  if hasHandles state identifier then throw .liveHandles
  return removeCell state identifier

/-- Allocation-wide guard precedes targeted ordinary legacy mutations, including
release/protect/transfer and either store width. Fresh allocation/adoption retain
the existing checked ownership and mapping overlap rules. -/
def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  if !allowed state operation then throw .reserved
  let result ← (Atomics.mutate state.legacy operation).mapError Fault.legacy
  return ({ state with legacy := result.1 }, result.2)

def readBorrow (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) : Except Fault (State × Nat) := do
  if reserved state ticket.identifier then throw .reserved
  let result ← (Atomics.readBorrow state.legacy lender ticket borrower region).mapError Fault.legacy
  return ({ state with legacy := result.1 }, result.2)

/-- Delegation retains the existing stored borrower check. -/
def finishLoan (state : State) (borrower identifier : Nat) : Except Fault State := do
  let result ← (Atomics.finishLoan state.legacy borrower identifier).mapError Fault.legacy
  return { state with legacy := result }

/-- Legacy32 enrollment is admitted only through this reverse reservation
gate. Raw legacy steps are not an admission mechanism for this resource layer. -/
def issue32 (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (address : Word) : Except Fault (State × Nat) := do
  if reserved state ticket.identifier then throw .reserved
  let result ← (Atomics.issue state.legacy owner ticket actor address).mapError Fault.legacy
  return ({ state with legacy := result.1 }, result.2)

def close32 (state : State) (actor identifier : Nat) : Except Fault State := do
  let result ← (Atomics.close state.legacy actor identifier).mapError Fault.legacy
  return { state with legacy := result }

/-- Audit data, not a source/ABI old-word return value. Identity and operands
come from checked stored authority and this operation's mask. -/
structure Event where
  actor : Nat
  handle : HandleId64
  cell : CellId64
  logical : LogicalEvent64
  deriving DecidableEq, Repr

/-- One functional, handle-authorized OR RMW of the current full64 word. The
single checked store64 is private to this operation; no intermediate load/store
state or ordinary-store event is exposed. Its abstract indivisibility requires
the RMW contract below; ordinary store64 alone proves no atomicity. -/
def logicalDiscard (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word) :
    Except Fault (State × Event) := do
  let selected ← authorize state actor identifier
  let cell := selected.2
  let old ← (loadQWord (toMemory state.legacy.shared.resources.space) cell.address).mapError Fault.machine
  let value := Sequential.LogicalOp.eval .bor old mask
  let result ← (Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value)).mapError Fault.legacy
  return ({ state with legacy := result.1 },
    ⟨actor, identifier, selected.1.cell, ⟨.bor, mask, ⟨cell.address, old, value⟩⟩⟩)

theorem validateCell_ok (state : State) (cell : Cell)
    (success : validateCell state cell = .ok ()) : ValidCell state.legacy.shared cell := by
  cases authorized : Ownership.authorize state.legacy.shared.resources cell.owner cell.ticket with
  | error fault => simp [validateCell, authorized, Except.mapError] at success
  | ok allocation =>
    by_cases fits : Ownership.containsQWord allocation cell.address = true
    · by_cases supported : atomicAddressable64 cell.address = true
      · by_cases writable : canStoreQWord (toMemory state.legacy.shared.resources.space) cell.address = true
        · by_cases data : dataOnly64 (toMemory state.legacy.shared.resources.space) cell.address = true
          · obtain ⟨found, owns, epoch⟩ := Ownership.authorize_ok _ _ _ _ authorized
            exact ⟨⟨allocation, found, owns, epoch, fits, writable⟩, supported, data⟩
          · simp [validateCell, authorized, Except.mapError, fits, supported, writable, data] at success
        · simp [validateCell, authorized, Except.mapError, fits, supported, writable] at success
      · simp [validateCell, authorized, Except.mapError, fits, supported] at success
    · simp [validateCell, authorized, Except.mapError, fits] at success

theorem validateCell_success (state : State) (cell : Cell) (valid : ValidCell state.legacy.shared cell) :
    validateCell state cell = .ok () := by
  obtain ⟨allocation, authorized, fits⟩ := valid.1.authorize
  simp [validateCell, authorized, Except.mapError, fits, valid.1.writable, valid.2.1, valid.2.2]

theorem currentCell_ok (state : State) (identifier : CellId64) (cell : Cell)
    (success : currentCell state identifier = .ok cell) :
    state.cells identifier = some cell ∧ ValidCell state.legacy.shared cell := by
  cases found : state.cells identifier with
  | none => simp [currentCell, found] at success
  | some selected =>
    cases checked : validateCell state selected with
    | error fault => simp [currentCell, found, checked] at success
    | ok checkedUnit =>
      cases checkedUnit
      simp [currentCell, found, checked] at success
      cases success
      exact ⟨rfl, validateCell_ok _ _ checked⟩

theorem currentCell_success (state : State) (identifier : CellId64) (cell : Cell)
    (valid : WellFormed state) (live : state.cells identifier = some cell) :
    currentCell state identifier = .ok cell := by
  simp [currentCell, live, validateCell_success _ _ (valid.cells _ _ live).2]

theorem authorizeCell_ok (state : State) (owner : Nat) (identifier : CellId64) (cell : Cell)
    (success : authorizeCell state owner identifier = .ok cell) :
    state.cells identifier = some cell ∧ cell.owner = owner ∧ ValidCell state.legacy.shared cell := by
  cases selected : currentCell state identifier with
  | error fault => simp [authorizeCell, selected] at success
  | ok current =>
    by_cases owns : current.owner = owner
    · simp [authorizeCell, selected, owns] at success
      cases success
      have checked := currentCell_ok _ _ _ selected
      exact ⟨checked.1, owns, checked.2⟩
    · simp [authorizeCell, selected, owns] at success

theorem authorizeCell_success (state : State) (owner : Nat) (identifier : CellId64) (cell : Cell)
    (valid : WellFormed state) (live : state.cells identifier = some cell) (owns : cell.owner = owner) :
    authorizeCell state owner identifier = .ok cell := by
  simp [authorizeCell, currentCell_success _ _ _ valid live, owns]

theorem authorize_ok (state : State) (actor : Nat) (identifier : HandleId64) (selected : Handle × Cell)
    (success : authorize state actor identifier = .ok selected) :
    state.handles identifier = some selected.1 ∧ selected.1.actor = actor ∧
    state.cells selected.1.cell = some selected.2 ∧ ValidCell state.legacy.shared selected.2 := by
  cases found : state.handles identifier with
  | none => simp [authorize, found] at success
  | some handle =>
    by_cases acts : handle.actor = actor
    · cases current : currentCell state handle.cell with
      | error fault => simp [authorize, found, acts, current] at success
      | ok cell =>
        simp [authorize, found, acts, current] at success
        subst selected
        have checked := currentCell_ok _ _ _ current
        exact ⟨rfl, acts, checked⟩
    · simp [authorize, found, acts] at success

theorem authorize_success (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (valid : WellFormed state)
    (live : state.handles identifier = some handle) (acts : handle.actor = actor)
    (linked : state.cells handle.cell = some cell) :
    authorize state actor identifier = .ok (handle, cell) := by
  simp [authorize, live, acts, currentCell_success _ _ _ valid linked]

theorem enroll_ok (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (result : State × CellId64) (success : enroll state owner ticket address = .ok result) :
    ValidCell state.legacy.shared ⟨owner, ticket, address⟩ ∧
    reserved state ticket.identifier = false ∧ Atomics.reserved state.legacy ticket.identifier = false ∧
    Borrowing.allowed state.legacy.shared (.store64 owner ticket address 0) = true ∧
    result = (installCell state ⟨owner, ticket, address⟩, ⟨state.nextCell⟩) := by
  cases checked : validateCell state ⟨owner, ticket, address⟩ with
  | error fault => simp [enroll, checked] at success
  | ok checkedUnit =>
    cases checkedUnit
    by_cases collision : (state.cells ⟨state.nextCell⟩).isSome = true
    · simp [enroll, checked, collision] at success
    · cases pinned : reserved state ticket.identifier with
      | true => simp [enroll, checked, collision, pinned] at success
      | false =>
        cases legacy : Atomics.reserved state.legacy ticket.identifier with
        | true => simp [enroll, checked, collision, pinned, legacy] at success
        | false =>
          by_cases readers : Borrowing.allowed state.legacy.shared (.store64 owner ticket address 0) = true
          · simp only [BitVec.ofNat_eq_ofNat] at readers
            simp [enroll, checked, collision, pinned, legacy, readers] at success
            exact ⟨validateCell_ok _ _ checked, rfl, rfl, readers, success.symm⟩
          · simp only [BitVec.ofNat_eq_ofNat] at readers
            simp [enroll, checked, collision, pinned, legacy, readers] at success

theorem enroll_success (state : State) (owner : Nat) (ticket : Ownership.Ticket) (address : Word)
    (valid : WellFormed state) (cellValid : ValidCell state.legacy.shared ⟨owner, ticket, address⟩)
    (unreserved : reserved state ticket.identifier = false)
    (legacy : Atomics.reserved state.legacy ticket.identifier = false)
    (readers : Borrowing.allowed state.legacy.shared (.store64 owner ticket address 0) = true) :
    enroll state owner ticket address = .ok (installCell state ⟨owner, ticket, address⟩, ⟨state.nextCell⟩) := by
  simp only [BitVec.ofNat_eq_ofNat] at readers
  simp [enroll, validateCell_success _ _ cellValid, fresh_cell _ valid, unreserved, legacy, readers]

theorem issue_ok (state : State) (owner : Nat) (identifier : CellId64) (actor : Nat)
    (result : State × HandleId64) (success : issue state owner identifier actor = .ok result) :
    ∃ cell, authorizeCell state owner identifier = .ok cell ∧
      result = (installHandle state ⟨actor, identifier⟩, ⟨state.nextHandle⟩) := by
  cases selected : authorizeCell state owner identifier with
  | error fault => simp [issue, selected] at success
  | ok cell =>
    by_cases collision : (state.handles ⟨state.nextHandle⟩).isSome = true
    · simp [issue, selected, collision] at success
    · simp [issue, selected, collision] at success
      exact ⟨cell, rfl, success.symm⟩

theorem issue_success (state : State) (owner : Nat) (identifier : CellId64) (actor : Nat)
    (cell : Cell) (valid : WellFormed state) (live : state.cells identifier = some cell)
    (owns : cell.owner = owner) :
    issue state owner identifier actor = .ok (installHandle state ⟨actor, identifier⟩, ⟨state.nextHandle⟩) := by
  simp [issue, authorizeCell_success _ _ _ _ valid live owns, fresh_handle _ valid]

theorem close_ok (state : State) (actor : Nat) (identifier : HandleId64) (after : State)
    (success : close state actor identifier = .ok after) :
    ∃ selected, authorize state actor identifier = .ok selected ∧ after = removeHandle state identifier := by
  cases selected : authorize state actor identifier with
  | error fault => simp [close, selected] at success
  | ok current =>
    simp [close, selected] at success
    exact ⟨current, rfl, success.symm⟩

theorem retire_ok (state : State) (owner : Nat) (identifier : CellId64) (after : State)
    (success : retire state owner identifier = .ok after) :
    ∃ cell, authorizeCell state owner identifier = .ok cell ∧ hasHandles state identifier = false ∧
      after = removeCell state identifier := by
  cases selected : authorizeCell state owner identifier with
  | error fault => simp [retire, selected] at success
  | ok cell =>
    cases busy : hasHandles state identifier with
    | true => simp [retire, selected, busy] at success
    | false =>
      simp [retire, selected, busy] at success
      exact ⟨cell, rfl, rfl, success.symm⟩

theorem mutate_ok (state : State) (operation : Ownership.Mutation)
    (result : State × Option Ownership.Ticket) (success : mutate state operation = .ok result) :
    allowed state operation = true ∧ ∃ legacy,
      Atomics.mutate state.legacy operation = .ok legacy ∧
      result = ({ state with legacy := legacy.1 }, legacy.2) := by
  by_cases checked : allowed state operation = true
  · cases changed : Atomics.mutate state.legacy operation with
    | error fault => simp [mutate, checked, changed, Except.mapError] at success
    | ok legacy =>
      simp [mutate, checked, changed, Except.mapError] at success
      exact ⟨checked, legacy, rfl, success.symm⟩
  · simp [mutate, checked] at success

theorem readBorrow_ok (state : State) (lender : Nat) (ticket : Ownership.Ticket)
    (borrower : Nat) (region : Region) (result : State × Nat)
    (success : readBorrow state lender ticket borrower region = .ok result) :
    reserved state ticket.identifier = false ∧ ∃ legacy,
      Atomics.readBorrow state.legacy lender ticket borrower region = .ok legacy ∧
      result = ({ state with legacy := legacy.1 }, legacy.2) := by
  cases checked : reserved state ticket.identifier with
  | true => simp [readBorrow, checked] at success
  | false =>
    cases borrowed : Atomics.readBorrow state.legacy lender ticket borrower region with
    | error fault => simp [readBorrow, checked, borrowed, Except.mapError] at success
    | ok legacy =>
      simp [readBorrow, checked, borrowed, Except.mapError] at success
      exact ⟨rfl, legacy, rfl, success.symm⟩

theorem finishLoan_ok (state : State) (borrower identifier : Nat) (after : State)
    (success : finishLoan state borrower identifier = .ok after) :
    ∃ legacy, Atomics.finishLoan state.legacy borrower identifier = .ok legacy ∧
      after = { state with legacy := legacy } := by
  cases finished : Atomics.finishLoan state.legacy borrower identifier with
  | error fault => simp [finishLoan, finished, Except.mapError] at success
  | ok legacy =>
    simp [finishLoan, finished, Except.mapError] at success
    exact ⟨legacy, rfl, success.symm⟩

theorem issue32_ok (state : State) (owner : Nat) (ticket : Ownership.Ticket)
    (actor : Nat) (address : Word) (result : State × Nat)
    (success : issue32 state owner ticket actor address = .ok result) :
    reserved state ticket.identifier = false ∧ ∃ legacy,
      Atomics.issue state.legacy owner ticket actor address = .ok legacy ∧
      result = ({ state with legacy := legacy.1 }, legacy.2) := by
  cases checked : reserved state ticket.identifier with
  | true => simp [issue32, checked] at success
  | false =>
    cases issued : Atomics.issue state.legacy owner ticket actor address with
    | error fault => simp [issue32, checked, issued, Except.mapError] at success
    | ok legacy =>
      simp [issue32, checked, issued, Except.mapError] at success
      exact ⟨rfl, legacy, rfl, success.symm⟩

theorem close32_ok (state : State) (actor identifier : Nat) (after : State)
    (success : close32 state actor identifier = .ok after) :
    ∃ legacy, Atomics.close state.legacy actor identifier = .ok legacy ∧
      after = { state with legacy := legacy } := by
  cases closed : Atomics.close state.legacy actor identifier with
  | error fault => simp [close32, closed, Except.mapError] at success
  | ok legacy =>
    simp [close32, closed, Except.mapError] at success
    exact ⟨legacy, rfl, success.symm⟩

theorem logicalDiscard_ok (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word)
    (result : State × Event) (success : logicalDiscard state actor identifier mask = .ok result) :
    ∃ handle cell old legacy,
      authorize state actor identifier = .ok (handle, cell) ∧
      loadQWord (toMemory state.legacy.shared.resources.space) cell.address = .ok old ∧
      Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address (Sequential.LogicalOp.eval .bor old mask)) = .ok legacy ∧
      result = ({ state with legacy := legacy.1 },
        ⟨actor, identifier, handle.cell, ⟨.bor, mask, ⟨cell.address, old, Sequential.LogicalOp.eval .bor old mask⟩⟩⟩) := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [logicalDiscard, authorized] at success
  | ok selected =>
    cases read : loadQWord (toMemory state.legacy.shared.resources.space) selected.2.address with
    | error fault => simp [logicalDiscard, authorized, read, Except.mapError] at success
    | ok old =>
      cases stored : Atomics.mutate state.legacy
          (.store64 selected.2.owner selected.2.ticket selected.2.address (Sequential.LogicalOp.eval .bor old mask)) with
      | error fault => simp [logicalDiscard, authorized, read, stored, Except.mapError] at success
      | ok legacy =>
        simp [logicalDiscard, authorized, read, stored, Except.mapError] at success
        exact ⟨selected.1, selected.2, old, legacy, rfl, read, stored, success.symm⟩

end EDSL.OS.Atomics64
