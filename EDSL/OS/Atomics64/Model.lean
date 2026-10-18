/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics.Preservation
import EDSL.OS.WordResources64
import EDSL.OS.Borrowing.Read64
import EDSL.X86.AtomicMemory64

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- Monotone logical identities, distinct from each other and from legacy IDs. -/
structure CellId64 where
  index : Nat
  deriving DecidableEq, Repr

structure HandleId64 where
  index : Nat
  deriving DecidableEq, Repr

/-- One registration reserves its entire allocation until explicit retirement.
Registration describes current managed atomic mode, not native C object creation. -/
structure Cell where
  owner : Nat
  ticket : Ownership.Ticket
  address : Word
  deriving DecidableEq, Repr

/-- Actor labels are logical principals, not native authentication. A handle
references a persistent cell; it does not contain a snapshot of its value. -/
structure Handle where
  actor : Nat
  cell : CellId64
  deriving DecidableEq, Repr

structure State where
  legacy : Atomics.State
  nextCell : Nat
  cells : CellId64 → Option Cell
  nextHandle : Nat
  handles : HandleId64 → Option Handle

def empty (legacy : Atomics.State) : State :=
  ⟨legacy, 0, fun _ => none, 0, fun _ => none⟩

def ValidCell (shared : Borrowing.State) (cell : Cell) : Prop :=
  WordResources64.WordValid shared cell.owner cell.ticket cell.address ∧
    atomicAddressable64 cell.address = true ∧
    dataOnly64 (toMemory shared.resources.space) cell.address = true

/-- One complete allocation per registration, with current owner/epoch, whole8
containment, full read/write permission and nonexecutable operand bytes. All
ordinary loans and legacy32 reservations on that allocation are excluded. -/
structure WellFormed (state : State) : Prop where
  legacy : Atomics.WellFormed state.legacy
  cells : ∀ identifier cell, state.cells identifier = some cell →
    identifier.index < state.nextCell ∧ ValidCell state.legacy.shared cell
  handles : ∀ identifier handle, state.handles identifier = some handle →
    identifier.index < state.nextHandle ∧ ∃ cell, state.cells handle.cell = some cell
  noReaders : ∀ identifier cell, state.cells identifier = some cell →
    ∀ loanId loan, state.legacy.shared.loans loanId = some loan →
      loan.ticket.identifier ≠ cell.ticket.identifier
  noLegacy : ∀ identifier cell, state.cells identifier = some cell →
    ∀ handleId handle, state.legacy.handles handleId = some handle →
      handle.ticket.identifier ≠ cell.ticket.identifier
  unique : ∀ left a right b, state.cells left = some a → state.cells right = some b →
    a.ticket.identifier = b.ticket.identifier → left = right

inductive Fault where
  | legacy (fault : Atomics.Fault)
  | ownership (fault : Ownership.Fault)
  | machine (fault : X86.Error)
  | reserved
  | legacyReservation
  | borrowed
  | missingCell
  | missingHandle
  | wrongOwner
  | wrongActor
  | identityCollision
  | liveHandles
  | executable
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) :
    (throw fault : Except Fault α) = .error fault := rfl

def reserved (state : State) (allocation : Nat) : Bool :=
  (List.range state.nextCell).any fun index =>
    match state.cells ⟨index⟩ with
    | none => false
    | some cell => decide (cell.ticket.identifier = allocation)

def allowed (state : State) (operation : Ownership.Mutation) : Bool :=
  match operation.target with
  | none => true
  | some allocation => !reserved state allocation

def hasHandles (state : State) (cell : CellId64) : Bool :=
  (List.range state.nextHandle).any fun index =>
    match state.handles ⟨index⟩ with
    | none => false
    | some handle => decide (handle.cell = cell)

def installCell (state : State) (cell : Cell) : State :=
  { state with
    nextCell := state.nextCell + 1
    cells := fun query => if query = ⟨state.nextCell⟩ then some cell else state.cells query }

def installHandle (state : State) (handle : Handle) : State :=
  { state with
    nextHandle := state.nextHandle + 1
    handles := fun query => if query = ⟨state.nextHandle⟩ then some handle else state.handles query }

def removeHandle (state : State) (identifier : HandleId64) : State :=
  { state with handles := fun query => if query = identifier then none else state.handles query }

def removeCell (state : State) (identifier : CellId64) : State :=
  { state with cells := fun query => if query = identifier then none else state.cells query }

theorem empty_wellFormed (legacy : Atomics.State) (valid : Atomics.WellFormed legacy) :
    WellFormed (empty legacy) :=
  ⟨valid, by simp [empty], by simp [empty], by simp [empty], by simp [empty], by simp [empty]⟩

theorem fresh_cell (state : State) (valid : WellFormed state) :
    state.cells ⟨state.nextCell⟩ = none := by
  cases found : state.cells ⟨state.nextCell⟩ with
  | none => rfl
  | some cell => exact False.elim (Nat.lt_irrefl _ (valid.cells _ _ found).1)

theorem fresh_handle (state : State) (valid : WellFormed state) :
    state.handles ⟨state.nextHandle⟩ = none := by
  cases found : state.handles ⟨state.nextHandle⟩ with
  | none => rfl
  | some handle => exact False.elim (Nat.lt_irrefl _ (valid.handles _ _ found).1)

theorem reserved_of_live (state : State) (valid : WellFormed state)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell) :
    reserved state cell.ticket.identifier = true := by
  apply List.any_eq_true.mpr
  refine ⟨identifier.index, List.mem_range.mpr (valid.cells _ _ live).1, ?_⟩
  simp [live]

theorem unreserved_sound (state : State) (valid : WellFormed state) (allocation : Nat)
    (checked : reserved state allocation = false)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell) :
    cell.ticket.identifier ≠ allocation := by
  intro same
  have pinned := reserved_of_live state valid identifier cell live
  rw [same, checked] at pinned
  cases pinned

theorem reserved_false (state : State) (allocation : Nat)
    (absent : ∀ identifier cell, state.cells identifier = some cell →
      cell.ticket.identifier ≠ allocation) : reserved state allocation = false := by
  apply Bool.eq_false_iff.mpr
  intro positive
  obtain ⟨index, _, observed⟩ := List.any_eq_true.mp positive
  cases found : state.cells ⟨index⟩ with
  | none => simp [found] at observed
  | some cell =>
    have same : cell.ticket.identifier = allocation := by simpa [found] using observed
    exact absent _ _ found same

theorem allowed_sound (state : State) (operation : Ownership.Mutation)
    (valid : WellFormed state) (checked : allowed state operation = true)
    (identifier : CellId64) (cell : Cell) (live : state.cells identifier = some cell) :
    operation.target ≠ some cell.ticket.identifier := by
  intro target
  have pinned := reserved_of_live state valid identifier cell live
  simp [allowed, target, pinned] at checked

theorem no_handles_sound (state : State) (valid : WellFormed state) (cell : CellId64)
    (checked : hasHandles state cell = false)
    (identifier : HandleId64) (handle : Handle) (live : state.handles identifier = some handle) :
    handle.cell ≠ cell := by
  intro same
  have positive : hasHandles state cell = true := by
    apply List.any_eq_true.mpr
    exact ⟨identifier.index, List.mem_range.mpr (valid.handles _ _ live).1, by simp [live, same]⟩
  rw [checked] at positive
  cases positive

theorem removeHandle_live {state : State} {identifier query : HandleId64} {handle : Handle}
    (live : (removeHandle state identifier).handles query = some handle) :
    state.handles query = some handle := by
  by_cases same : query = identifier
  · simp [removeHandle, same] at live
  · simpa [removeHandle, same] using live

theorem removeCell_live {state : State} {identifier query : CellId64} {cell : Cell}
    (live : (removeCell state identifier).cells query = some cell) :
    state.cells query = some cell := by
  by_cases same : query = identifier
  · simp [removeCell, same] at live
  · simpa [removeCell, same] using live

/-- Byte values do not affect the nonexecutable support gate. -/
theorem dataOnly64_permissions {before after : Space}
    (permissions : ∀ query, (after.cells query).map AddressSpace.Cell.permissions =
      (before.cells query).map AddressSpace.Cell.permissions) (address : Word) :
    dataOnly64 (toMemory after) address = dataOnly64 (toMemory before) address := by
  have point (query : Word) : (toMemory after).executable query = (toMemory before).executable query := by
    have same := permissions query
    cases afterAt : after.cells query <;> cases beforeAt : before.cells query <;>
      simp_all [toMemory]
  simp only [dataOnly64, point]

theorem ValidCell.permissions {before after : Borrowing.State} {cell : Cell}
    (valid : ValidCell before cell)
    (allocations : after.resources.allocations = before.resources.allocations)
    (permissions : ∀ query, (after.resources.space.cells query).map AddressSpace.Cell.permissions =
      (before.resources.space.cells query).map AddressSpace.Cell.permissions) : ValidCell after cell :=
  ⟨valid.1.permissions allocations permissions, valid.2.1,
    (dataOnly64_permissions permissions cell.address).trans valid.2.2⟩

/-- A checked operation on another allocation preserves complete current64
resource validity, including the last operand byte and every executable bit. -/
theorem ValidCell.frame {before after : Ownership.World} {cell : Cell}
    (world : Ownership.WellFormed before)
    (valid : ValidCell ⟨before, 0, fun _ => none⟩ cell)
    (frame : Ownership.PreservesAllocation before after cell.ticket.identifier) :
    ValidCell ⟨after, 0, fun _ => none⟩ cell := by
  obtain ⟨⟨allocation, found, owns, epoch, fits, writable⟩, supported, data⟩ := valid
  obtain ⟨preserved, cells⟩ := frame allocation found
  let loan : Borrowing.Loan := ⟨cell.ticket, cell.owner, cell.owner, allocation.region⟩
  have regionValid := (world.1 _ _ found).2.1
  have subregion : Borrowing.Subregion (qwordRegion cell.address) loan.region := of_decide_eq_true fits
  have point (offset : Nat) (bound : offset < 8) :
      after.space.cells (cell.address + BitVec.ofNat 64 offset) =
        before.space.cells (cell.address + BitVec.ofNat 64 offset) :=
    cells _ (Borrowing.qword_inside loan regionValid cell.address subregion offset bound)
  have c0 := point 0 (by decide)
  have c1 := point 1 (by decide)
  have c2 := point 2 (by decide)
  have c3 := point 3 (by decide)
  have c4 := point 4 (by decide)
  have c5 := point 5 (by decide)
  have c6 := point 6 (by decide)
  have c7 := point 7 (by decide)
  simp only [BitVec.add_zero] at c0
  change after.space.cells (cell.address + 1) = before.space.cells (cell.address + 1) at c1
  change after.space.cells (cell.address + 2) = before.space.cells (cell.address + 2) at c2
  change after.space.cells (cell.address + 3) = before.space.cells (cell.address + 3) at c3
  change after.space.cells (cell.address + 4) = before.space.cells (cell.address + 4) at c4
  change after.space.cells (cell.address + 5) = before.space.cells (cell.address + 5) at c5
  change after.space.cells (cell.address + 6) = before.space.cells (cell.address + 6) at c6
  change after.space.cells (cell.address + 7) = before.space.cells (cell.address + 7) at c7
  refine ⟨⟨allocation, preserved, owns, epoch, fits, ?_⟩, supported, ?_⟩
  · simpa only [canStoreQWord, qwordWritable, toMemory, c0, c1, c2, c3, c4, c5, c6, c7] using writable
  · simpa only [dataOnly64, toMemory, c0, c1, c2, c3, c4, c5, c6, c7] using data

end EDSL.OS.Atomics64
