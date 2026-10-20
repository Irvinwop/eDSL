/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalPreservation
import EDSL.Logical64.SetHistory

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- A persistent-cell modification order of actual checked operations. Tags,
actors, handles and masks may vary, and unchanged events remain in the list.
Retirement, re-enrollment and unrelated writers require a wider history model. -/
inductive LogicalTrace (identifier : CellId64) (cell : Cell) : State → List Event → State → Prop where
  | refl {state} (live : state.cells identifier = some cell) : LogicalTrace identifier cell state [] state
  | next {op before result actor handle mask events after}
      (success : logicalUpdate op before actor handle mask = .ok result)
      (selected : result.2.cell = identifier)
      (tail : LogicalTrace identifier cell result.1 events after) :
      LogicalTrace identifier cell before (result.2 :: events) after

theorem LogicalTrace.cells {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) : after.cells = before.cells := by
  induction trace with
  | refl _ => rfl
  | next success _ _ induction => exact induction.trans (logicalUpdate_effect _ _ _ _ _ _ success).cells

theorem LogicalTrace.final_cell {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) : after.cells identifier = some cell := by
  induction trace with
  | refl live => exact live
  | next _ _ _ induction => exact induction

theorem LogicalTrace.initial_cell {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) : before.cells identifier = some cell := by
  rw [← trace.cells]
  exact trace.final_cell

theorem LogicalTrace.wellFormed {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) (valid : WellFormed before) : WellFormed after := by
  induction trace with
  | refl _ => exact valid
  | next success _ _ induction => exact induction (logicalUpdate_wellFormed _ _ _ _ _ _ valid success)

/-- The fixed address is recovered from the current authorized registry. -/
theorem logicalUpdate_registered (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (handle : HandleId64) (mask : Word) (result : State × Event) (identifier : CellId64) (cell : Cell)
    (success : logicalUpdate op state actor handle mask = .ok result)
    (live : state.cells identifier = some cell) (selected : result.2.cell = identifier) :
    result.2.logical.event.address = cell.address := by
  obtain ⟨storedHandle, storedCell, authorized, shape, _⟩ := logicalUpdate_guarded _ _ _ _ _ _ success
  have linked := (authorize_ok _ _ _ _ authorized).2.2.1
  have identity : storedHandle.cell = identifier := (congrArg Event.cell shape).symm.trans selected
  rw [identity, live] at linked
  have sameCell := Option.some.inj linked
  exact (congrArg (fun event : Event => event.logical.event.address) shape).trans
    (congrArg Cell.address sameCell.symm)

/-- Value coherence is separate from authority and atomicity. Each event reads
the preceding value, with its own retained operation and mask. -/
inductive LogicalChain : Word → List Event → Word → Prop where
  | nil {value} : LogicalChain value [] value
  | cons {initial event rest final}
      (read : event.logical.event.before = initial)
      (write : event.logical.event.after = event.logical.op.eval initial event.logical.mask)
      (tail : LogicalChain event.logical.event.after rest final) :
      LogicalChain initial (event :: rest) final

theorem LogicalChain.value {initial final : Word} {events : List Event}
    (chain : LogicalChain initial events final) :
    final = Logical64.applyUpdates initial (events.map (fun event => (event.logical.op, event.logical.mask))) := by
  induction chain with
  | nil => rfl
  | cons _ write _ induction =>
    simpa only [List.map_cons, Logical64.applyUpdates, write] using induction

theorem eventUpdates_uniform (op : Sequential.LogicalOp) (events : List Event)
    (uniform : ∀ event ∈ events, event.logical.op = op) :
    events.map (fun event => (event.logical.op, event.logical.mask)) =
      (events.map (fun event => event.logical.mask)).map (fun mask => (op, mask)) := by
  induction events with
  | nil => rfl
  | cons event rest induction =>
    simp only [List.map_cons, uniform event (by simp),
      induction (fun next member => uniform next (List.mem_cons_of_mem _ member))]

theorem LogicalChain.intersection {initial final : Word} {events : List Event}
    (chain : LogicalChain initial events final)
    (uniform : ∀ event ∈ events, event.logical.op = .band) (index : Fin 64) :
    Logical64.HasBit final index ↔ Logical64.HasBit initial index ∧
      ∀ event ∈ events, Logical64.HasBit event.logical.mask index := by
  rw [chain.value, eventUpdates_uniform .band events uniform,
    Logical64.applyUpdates_intersection, Logical64.intersectMasks_membership]
  simp only [List.forall_mem_map]

theorem LogicalChain.union {initial final : Word} {events : List Event}
    (chain : LogicalChain initial events final)
    (uniform : ∀ event ∈ events, event.logical.op = .bor) (index : Fin 64) :
    Logical64.HasBit final index ↔ Logical64.HasBit initial index ∨
      ∃ event ∈ events, Logical64.HasBit event.logical.mask index := by
  rw [chain.value, eventUpdates_uniform .bor events uniform,
    Logical64.applyUpdates_union, Logical64.unionMasks_membership]
  simp only [List.mem_map]
  constructor
  · rintro (initialBit | ⟨mask, ⟨event, member, same⟩, bit⟩)
    · exact Or.inl initialBit
    · exact Or.inr ⟨event, member, same ▸ bit⟩
  · rintro (initialBit | ⟨event, member, bit⟩)
    · exact Or.inl initialBit
    · exact Or.inr ⟨event.logical.mask, ⟨event, member, rfl⟩, bit⟩

theorem LogicalChain.symmetricDifference {initial final : Word} {events : List Event}
    (chain : LogicalChain initial events final)
    (uniform : ∀ event ∈ events, event.logical.op = .bxor) (index : Fin 64) :
    Logical64.HasBit final index ↔
      ((if initial.toNat.testBit index then 1 else 0) +
        Logical64.bitOccurrences (events.map (fun event => event.logical.mask)) index) % 2 = 1 := by
  rw [chain.value, eventUpdates_uniform .bxor events uniform,
    Logical64.applyUpdates_symmetricDifference, Logical64.xorMasks_membership]
  rfl

/-- An arbitrary mixed checked schedule produces one actual current-before
chain and final full64 readback. No spawn-time old value is admitted. -/
theorem LogicalTrace.chain {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ final, loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final ∧
      LogicalChain initial events final := by
  induction trace generalizing initial with
  | refl _ => exact ⟨initial, read, .nil⟩
  | @next op before result actor handle mask events after success selected tail induction =>
    have effect := logicalUpdate_sound op _ _ _ _ _ success
    have live : before.cells identifier = some cell := by
      rw [← (logicalUpdate_effect op _ _ _ _ _ success).cells]
      exact tail.initial_cell
    have address := logicalUpdate_registered op _ _ _ _ _ identifier cell success live selected
    have current := effect.1.2.2.1
    rw [address, read] at current
    have same : result.2.logical.event.before = initial := (Except.ok.inj current).symm
    have readback := effect.1.readback
    rw [address] at readback
    obtain ⟨final, finalRead, chained⟩ := induction result.2.logical.event.after readback
    refine ⟨final, finalRead, .cons same ?_ chained⟩
    simpa only [same, effect.2.1, effect.2.2.1] using effect.2.2.2.1

theorem LogicalTrace.readback {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : LogicalTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    loadQWord (toMemory after.legacy.shared.resources.space) cell.address =
      .ok (Logical64.applyUpdates initial (events.map (fun event => (event.logical.op, event.logical.mask)))) := by
  obtain ⟨final, finalRead, chain⟩ := trace.chain initial read
  rwa [chain.value] at finalRead

/-- Every original loan survives with its exact cells; the operand allocation
cannot carry a conflicting ordinary read loan while registered. -/
theorem LogicalTrace.loan_contents {identifier : CellId64} {cell : Cell} {before after : State}
    {events : List Event} (trace : LogicalTrace identifier cell before events after)
    (valid : WellFormed before) (loanId : Nat) (loan : Borrowing.Loan)
    (live : before.legacy.shared.loans loanId = some loan) :
    after.legacy.shared.loans loanId = some loan ∧
      ∀ query, loan.region.Contains query →
        after.legacy.shared.resources.space.cells query = before.legacy.shared.resources.space.cells query := by
  induction trace with
  | refl _ => exact ⟨live, fun _ _ => rfl⟩
  | next success _ _ induction =>
    have first := logicalUpdate_loan_contents _ _ _ _ _ _ valid success loanId loan live
    have nextLive := (congrFun (logicalUpdate_effect _ _ _ _ _ _ success).shared.loans loanId).trans live
    have last := induction (logicalUpdate_wellFormed _ _ _ _ _ _ valid success) nextLive
    exact ⟨last.1, fun query inside => (last.2 query inside).trans (first query inside)⟩

structure UpdateRequest where
  op : Sequential.LogicalOp
  actor : Nat
  handle : HandleId64
  mask : Word
  deriving DecidableEq, Repr

def Event.updateRequest (event : Event) : UpdateRequest :=
  ⟨event.logical.op, event.actor, event.handle, event.logical.mask⟩

def UpdateRequest.Authorized (request : UpdateRequest) (state : State) (identifier : CellId64) : Prop :=
  ∃ handle, state.handles request.handle = some handle ∧ handle.actor = request.actor ∧
    handle.cell = identifier

/-- Every finite list of currently authorized mixed requests can run, retaining
the exact requested operations, actors, handles and masks. This derives each
successful transition from present resources. -/
theorem LogicalTrace.enabled (state : State) (identifier : CellId64) (cell : Cell)
    (requests : List UpdateRequest) (valid : WellFormed state) (live : state.cells identifier = some cell)
    (authorized : ∀ request ∈ requests, request.Authorized state identifier) :
    ∃ after events, LogicalTrace identifier cell state events after ∧
      events.map Event.updateRequest = requests := by
  induction requests generalizing state with
  | nil => exact ⟨state, [], .refl live, rfl⟩
  | cons request rest induction =>
    obtain ⟨handle, stored, actor, selected⟩ := authorized request (by simp)
    have linked : state.cells handle.cell = some cell := by rw [selected]; exact live
    have permission := authorize_success _ request.actor request.handle handle cell valid stored actor linked
    obtain ⟨result, success⟩ := logicalUpdate_enabled request.op _ _ _ request.mask handle cell valid permission
    have effect := logicalUpdate_effect request.op _ _ _ _ _ success
    have nextValid := logicalUpdate_wellFormed request.op _ _ _ _ _ valid success
    have nextLive : result.1.cells identifier = some cell := by rw [effect.cells]; exact live
    have sound := logicalUpdate_sound request.op _ _ _ _ _ success
    have shape : result.2.updateRequest = request := by
      cases request
      simp only [Event.updateRequest, UpdateRequest.mk.injEq]
      exact ⟨sound.2.1, sound.2.2.2.2.1, sound.2.2.2.2.2, sound.2.2.1⟩
    have selectedEvent : result.2.cell = identifier := by
      obtain ⟨actualHandle, _, actualAuth, eventShape, _⟩ := logicalUpdate_guarded _ _ _ _ _ _ success
      rw [permission] at actualAuth
      have same := Prod.mk.inj (Except.ok.inj actualAuth)
      exact (congrArg Event.cell eventShape).trans ((congrArg Handle.cell same.1.symm).trans selected)
    have remaining : ∀ next ∈ rest, next.Authorized result.1 identifier := by
      intro next member
      obtain ⟨nextHandle, nextStored, nextActor, nextCell⟩ := authorized next (List.mem_cons_of_mem _ member)
      exact ⟨nextHandle, by rw [effect.handles]; exact nextStored, nextActor, nextCell⟩
    obtain ⟨after, events, trace, requestsEq⟩ := induction result.1 nextValid nextLive remaining
    refine ⟨after, result.2 :: events, .next success selectedEvent trace, ?_⟩
    simp only [List.map_cons, shape, requestsEq]

end EDSL.OS.Atomics64
