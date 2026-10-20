/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.History
import EDSL.Logical64.Algebra

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- A deliberately restricted modification order: arbitrary actors and masks,
including duplicates and unchanged-value events, on one persistent registered
cell. Every event is an actual checked operation output. Administrative lifetime
changes and other memory writers belong to `History`, not this OR-only trace. -/
inductive OrTrace (identifier : CellId64) (cell : Cell) : State → List Event → State → Prop where
  | refl {state} (live : state.cells identifier = some cell) : OrTrace identifier cell state [] state
  | next {before result actor handle mask events after}
      (success : logicalDiscard before actor handle mask = .ok result)
      (selected : result.2.cell = identifier)
      (tail : OrTrace identifier cell result.1 events after) :
      OrTrace identifier cell before (result.2 :: events) after
  | idle {before events after} (tail : OrTrace identifier cell before events after) :
      OrTrace identifier cell before events after

theorem OrTrace.cells {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) : after.cells = before.cells := by
  induction trace with
  | refl _ => rfl
  | next success _ _ induction => exact induction.trans (logicalDiscard_effect _ _ _ _ _ success).cells
  | idle _ induction => exact induction

theorem OrTrace.final_cell {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) : after.cells identifier = some cell := by
  induction trace with
  | refl live => exact live
  | next _ _ _ induction => exact induction
  | idle _ induction => exact induction

theorem OrTrace.initial_cell {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) : before.cells identifier = some cell := by
  rw [← trace.cells]
  exact trace.final_cell

theorem OrTrace.history {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) : History before (events.map some) after := by
  induction trace with
  | refl _ => exact .refl
  | next success _ _ induction => exact .next (.logicalDiscard success) induction
  | idle _ induction => exact induction

theorem OrTrace.wellFormed {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) (valid : WellFormed before) : WellFormed after :=
  trace.history.wellFormed valid

/-- The fixed address comes from the authorized stored cell, rather than an
unverified label attached to a write. -/
theorem logicalDiscard_registered (state : State) (actor : Nat) (handle : HandleId64) (mask : Word)
    (result : State × Event) (identifier : CellId64) (cell : Cell)
    (success : logicalDiscard state actor handle mask = .ok result)
    (live : state.cells identifier = some cell) (selected : result.2.cell = identifier) :
    result.2.logical.event.address = cell.address := by
  obtain ⟨storedHandle, storedCell, authorized, shape, _⟩ := logicalDiscard_guarded _ _ _ _ _ success
  have linked := (authorize_ok _ _ _ _ authorized).2.2.1
  have identity : storedHandle.cell = identifier := (congrArg Event.cell shape).symm.trans selected
  rw [identity, live] at linked
  have sameCell := Option.some.inj linked
  exact (congrArg (fun event : Event => event.logical.event.address) shape).trans
    (congrArg Cell.address sameCell.symm)

/-- Independent value-chain specification. Every step reads the preceding
value and applies its retained actual mask; operation tags must also be OR. -/
inductive OrChain : Word → List Event → Word → Prop where
  | nil {value} : OrChain value [] value
  | cons {initial event rest final}
      (op : event.logical.op = .bor)
      (read : event.logical.event.before = initial)
      (write : event.logical.event.after = initial ||| event.logical.mask)
      (tail : OrChain event.logical.event.after rest final) :
      OrChain initial (event :: rest) final

theorem OrChain.value {initial final : Word} {events : List Event}
    (chain : OrChain initial events final) :
    final = Logical64.unionMasks initial (events.map (fun event => event.logical.mask)) := by
  induction chain with
  | nil => rfl
  | cons _ _ write _ induction =>
    simpa only [List.map_cons, Logical64.unionMasks, write] using induction

theorem OrChain.membership {initial final : Word} {events : List Event}
    (chain : OrChain initial events final) (index : Fin 64) :
    Logical64.HasBit final index ↔ Logical64.HasBit initial index ∨
      ∃ event ∈ events, Logical64.HasBit event.logical.mask index := by
  rw [chain.value, Logical64.unionMasks_membership]
  simp only [List.mem_map]
  constructor
  · rintro (initialBit | ⟨mask, ⟨event, member, same⟩, bit⟩)
    · exact Or.inl initialBit
    · exact Or.inr ⟨event, member, same ▸ bit⟩
  · rintro (initialBit | ⟨event, member, bit⟩)
    · exact Or.inl initialBit
    · exact Or.inr ⟨event.logical.mask, ⟨event, member, rfl⟩, bit⟩

/-- Current-before chaining and final readback for any finite checked schedule.
No spawn-time snapshot, pair of ordinary writes, or assumed future execution
can establish this statement. -/
theorem OrTrace.chain {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ final, loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final ∧
      OrChain initial events final := by
  induction trace generalizing initial with
  | refl _ => exact ⟨initial, read, .nil⟩
  | @next before result actor handle mask events after success selected tail induction =>
    have effect := logicalDiscard_sound _ _ _ _ _ success
    have live : before.cells identifier = some cell := by
      rw [← (logicalDiscard_effect _ _ _ _ _ success).cells]
      exact tail.initial_cell
    have address := logicalDiscard_registered _ _ _ _ _ identifier cell success live selected
    have current := effect.1.2.2.1
    rw [address, read] at current
    have same : result.2.logical.event.before = initial := (Except.ok.inj current).symm
    have readback := effect.1.readback
    rw [address] at readback
    obtain ⟨final, finalRead, chained⟩ := induction result.2.logical.event.after readback
    refine ⟨final, finalRead, .cons effect.2.1 same ?_ chained⟩
    have value := effect.2.2.2.1
    simpa only [Sequential.LogicalOp.eval, same, effect.2.2.1] using value
  | idle _ induction => exact induction initial read

theorem OrTrace.readback {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    loadQWord (toMemory after.legacy.shared.resources.space) cell.address =
      .ok (Logical64.unionMasks initial (events.map (fun event => event.logical.mask))) := by
  obtain ⟨final, finalRead, chain⟩ := trace.chain initial read
  rwa [chain.value] at finalRead

/-- Each final bit is characterized independently by natural-number bit
membership in the initial value or an actual event mask. -/
theorem OrTrace.membership {identifier : CellId64} {cell : Cell} {before after : State} {events : List Event}
    (trace : OrTrace identifier cell before events after) (initial : Word)
    (read : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok initial) :
    ∃ final, loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final ∧
      ∀ index, Logical64.HasBit final index ↔ Logical64.HasBit initial index ∨
        ∃ event ∈ events, Logical64.HasBit event.logical.mask index := by
  obtain ⟨final, finalRead, chain⟩ := trace.chain initial read
  exact ⟨final, finalRead, chain.membership⟩

/-- A finite scheduler request carries current logical authority, not a
prediction about a future execution. Actors may alternate and masks may repeat. -/
structure Request where
  actor : Nat
  handle : HandleId64
  mask : Word
  deriving DecidableEq, Repr

def Event.request (event : Event) : Request :=
  ⟨event.actor, event.handle, event.logical.mask⟩

def Request.Authorized (request : Request) (state : State) (identifier : CellId64) : Prop :=
  ∃ handle, state.handles request.handle = some handle ∧ handle.actor = request.actor ∧
    handle.cell = identifier

/-- Every finite list of currently authorized requests can run. The theorem
constructs real successful operations and retains exactly their outputs; it
assumes neither a future admission oracle nor pairwise distinct masks. -/
theorem OrTrace.enabled (state : State) (identifier : CellId64) (cell : Cell)
    (requests : List Request) (valid : WellFormed state) (live : state.cells identifier = some cell)
    (authorized : ∀ request ∈ requests, request.Authorized state identifier) :
    ∃ after events, OrTrace identifier cell state events after ∧ events.map Event.request = requests := by
  induction requests generalizing state with
  | nil => exact ⟨state, [], .refl live, rfl⟩
  | cons request rest induction =>
    obtain ⟨handle, stored, actor, selected⟩ := authorized request (by simp)
    have linked : state.cells handle.cell = some cell := by rw [selected]; exact live
    have permission := authorize_success _ request.actor request.handle handle cell valid stored actor linked
    obtain ⟨result, success⟩ := logicalDiscard_enabled _ _ _ request.mask handle cell valid permission
    have effect := logicalDiscard_effect _ _ _ _ _ success
    have nextValid := logicalDiscard_wellFormed _ _ _ _ _ valid success
    have nextLive : result.1.cells identifier = some cell := by rw [effect.cells]; exact live
    have sound := logicalDiscard_sound _ _ _ _ _ success
    have shape : result.2.request = request := by
      cases request
      simp only [Event.request, Request.mk.injEq]
      exact ⟨sound.2.2.2.2.1, sound.2.2.2.2.2, sound.2.2.1⟩
    have selectedEvent : result.2.cell = identifier := by
      obtain ⟨actualHandle, _, actualAuth, eventShape, _⟩ := logicalDiscard_guarded _ _ _ _ _ success
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
