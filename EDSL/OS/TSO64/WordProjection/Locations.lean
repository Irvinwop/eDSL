/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.PublishedHistory

set_option autoImplicit false

namespace EDSL.OS.TSO64.WordProjection
open X86

/-- Stable symbolic locations denote distinct physical qword starts in the
registered-cell profile. This follows from current allocation separation,
not from comparing values or assuming handles are injective. -/
theorem address_injective {world : World} {first second : Atomics64.CellId64}
    {left right : Atomics64.Cell} (valid : Atomics64.WellFormed world)
    (liveLeft : world.cells first = some left) (liveRight : world.cells second = some right)
    (same : left.address = right.address) : first = second := by
  by_cases different : first = second
  · exact different
  · apply False.elim
    have allocationDifferent : left.ticket.identifier ≠ right.ticket.identifier := by
      intro equal
      exact different (valid.unique first left second right liveLeft liveRight equal)
    obtain ⟨a, foundA, _, _, fitsA, _⟩ := (valid.cells first left liveLeft).2.1
    obtain ⟨b, foundB, _, _, fitsB, _⟩ := (valid.cells second right liveRight).2.1
    have boundsA : a.region.base.toNat ≤ left.address.toNat ∧
        left.address.toNat + 8 ≤ a.region.base.toNat + a.region.length := of_decide_eq_true fitsA
    have boundsB : b.region.base.toNat ≤ right.address.toNat ∧
        right.address.toNat + 8 ≤ b.region.base.toNat + b.region.length := of_decide_eq_true fitsB
    have separated := valid.legacy.shared.1.2 _ _ _ _ foundA foundB allocationDifferent
    rw [same] at boundsA
    rcases separated with before | after <;> omega

/-- An actually live registered cell has a complete current data read, even
when no particular actor handle is selected by this theorem. -/
theorem read_exists {world : World} {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    (valid : Atomics64.WellFormed world) (live : world.cells identifier = some cell) :
    ∃ value, loadQWord (published world) cell.address = .ok value :=
  (valid.cells identifier cell live).2.1.load_exists

/-- Only current registered qwords are reference-memory locations. Other RAM,
including ordinary data/code/caller slots, is outside this projection. -/
def memory (world : World) (identifier : Atomics64.CellId64) : Option Word :=
  match world.cells identifier with
  | none => none
  | some cell => (loadQWord (published world) cell.address).toOption

/-- Managed entries in actual oldest-first FIFO order. Ordinary stores
are erased only after their actual resource frame has been proved. -/
def managed : List Pending → List (Atomics64.CellId64 × Word)
  | [] => []
  | .ordinary _ _ :: entries => managed entries
  | .managed reference value _ :: entries => (reference.handle.cell, value) :: managed entries

/-- The reference presentation uses newest-first buffers, so the actual FIFO
projection is reversed. Missing threads have no reference pending writes. -/
def buffers (state : State) (tid : Nat) : List (Atomics64.CellId64 × Word) :=
  match state.workers[tid]? with
  | none => []
  | some worker => (managed worker.pending).reverse

theorem memory_read {world : World} {identifier : Atomics64.CellId64} {cell : Atomics64.Cell}
    {value : Word} (live : world.cells identifier = some cell)
    (read : loadQWord (published world) cell.address = .ok value) :
    memory world identifier = some value := by simp only [memory, live, read, Except.toOption]

private theorem write_live {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {cause : PublishedHistory.WriteCause}
    (success : step state action profile = .ok result)
    (written : PublishedHistory.writeOf result.2 = some cause) :
    ∃ cell, state.world.cells cause.cell = some cell := by
  cases step_origin success with
  | ordinary liveWorker running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> simp [PublishedHistory.writeOf] at written
  | blocked => simp [PublishedHistory.writeOf] at written
  | rmw liveWorker running code caller fetched bounds empty grant effect =>
    have equal := Option.some.inj written
    subst cause
    obtain ⟨handle, cell, _, _, linked, _, identifier, _⟩ :=
      Atomics64.fetchAdd_context _ _ _ _ _ effect.checked
    exact ⟨cell, by simpa only [PublishedHistory.WriteCause.cell, identifier] using linked⟩
  | drained liveWorker fifo gate changed effect =>
    cases changed with
    | ordinary => simp [PublishedHistory.writeOf] at written
    | managed current changed =>
      have equal := Option.some.inj written
      subst cause
      exact ⟨_, current.cell⟩

theorem memory_step {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (valid : WellFormed state profile)
    (success : step state action profile = .ok result) (query : Atomics64.CellId64) :
    memory result.1.world query =
      match PublishedHistory.writeOf result.2 with
      | none => memory state.world query
      | some cause => if cause.cell = query then some cause.value else memory state.world query := by
  have stable := (step_stable success).cells
  cases live : state.world.cells query with
  | none =>
    have nextLive : result.1.world.cells query = none := (congrFun stable query).trans live
    cases written : PublishedHistory.writeOf result.2 with
    | none => simp only [memory, live, nextLive]
    | some cause =>
      by_cases selected : cause.cell = query
      · obtain ⟨cell, linked⟩ := write_live success written
        rw [selected, live] at linked
        cases linked
      · simp only [memory, nextLive, live, ite_eq_right selected]
  | some cell =>
    obtain ⟨prior, readBefore⟩ := read_exists valid.1 live
    have readAfter := PublishedHistory.step_read valid success query cell live prior readBefore
    have nextLive : result.1.world.cells query = some cell := (congrFun stable query).trans live
    cases written : PublishedHistory.writeOf result.2 with
    | none =>
      simp only [written] at readAfter
      exact (memory_read nextLive readAfter).trans (memory_read live readBefore).symm
    | some cause =>
      rw [written] at readAfter
      by_cases selected : cause.cell = query
      · simp only [selected, ↓reduceIte] at readAfter
        simpa only [selected, ↓reduceIte] using memory_read nextLive readAfter
      · simp only [selected, ↓reduceIte] at readAfter
        simpa only [selected, ↓reduceIte] using
          (memory_read nextLive readAfter).trans (memory_read live readBefore).symm

end EDSL.OS.TSO64.WordProjection
