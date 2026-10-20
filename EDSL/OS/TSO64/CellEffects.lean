/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.WriterMap
import EDSL.OS.TSO64.Run
import EDSL.OS.AtomicFetchAddHistory64
import EDSL.OS.AtomicAccess64

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedHistory
open X86 AddressSpace

/-- A checked managed publication writes the selected whole word and frames
every other registered cell. The original complete reference is reauthorized;
neither its address nor an equality of values substitutes for that check. -/
theorem managed_publication_read {before : World} {resources : Resources}
    {reference : Queue.ManagedRef} {value : Word}
    {result : World × Atomics64.StoreEvent64}
    (valid : Atomics64.WellFormed before)
    (current : Queue.Current before resources reference)
    (success : Atomics64.publishStore before resources.actor reference.identifier value = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : before.cells target = some cell) (prior : Word)
    (readBefore : loadQWord (published before) cell.address = .ok prior) :
    loadQWord (published result.1) cell.address =
      .ok (if reference.handle.cell = target then value else prior) := by
  obtain ⟨handle, actual, found, _, linked, _, eventEq⟩ :=
    Atomics64.publishStore_context _ _ _ _ _ success
  have sameHandle : handle = reference.handle :=
    Option.some.inj (found.symm.trans (Atomics64.authorize_ok _ _ _ _ current.2).1)
  subst handle
  have sameCell : actual = reference.cell :=
    Option.some.inj (linked.symm.trans current.cell)
  subst actual
  by_cases selected : reference.handle.cell = target
  · have linkedTarget : before.cells target = some reference.cell := by
      simpa only [selected] using current.cell
    have sameTarget : reference.cell = cell :=
      Option.some.inj (linkedTarget.symm.trans live)
    have address : result.2.address = cell.address := by
      rw [eventEq, sameTarget]
    have final := Atomics64.publishStore_readback _ _ _ _ _ success
    rw [address] at final
    simpa only [published, selected, ↓reduceIte] using final
  · have different : target ≠ result.2.cell := by
      rw [eventEq]
      exact Ne.symm selected
    have frame := Atomics64.publishStore_preserves_other _ _ _ _ _ valid success
      target cell live different
    have quiet : loadQWord (published result.1) cell.address =
        loadQWord (published before) cell.address :=
      AtomicFetchAddHistory64.load_frame valid.legacy.shared.1 (valid.cells _ _ live).2 frame
    simpa only [selected, ↓reduceIte] using quiet.trans readBefore

/-- The actual OS RMW supplies the target readback and preserves the actual
load of every other registered cell. No old or new value is taken from cell
metadata. In particular an unchanged result remains a real RMW. -/
theorem rmw_read {before : World} {actor : Nat} {identifier : Atomics64.HandleId64}
    {delta : Word} {result : World × Atomics64.FetchAddEvent}
    (valid : Atomics64.WellFormed before)
    (success : Atomics64.fetchAdd before actor identifier delta = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : before.cells target = some cell) (prior : Word)
    (readBefore : loadQWord (published before) cell.address = .ok prior) :
    loadQWord (published result.1) cell.address =
      .ok (if result.2.cell = target then result.2.arithmetic.event.after else prior) := by
  by_cases selected : result.2.cell = target
  · obtain ⟨handle, actual, _, _, linked, _, identity, address⟩ :=
      Atomics64.fetchAdd_context _ _ _ _ _ success
    have sameId : handle.cell = target := identity.symm.trans selected
    rw [sameId, live] at linked
    have sameCell := Option.some.inj linked
    subst actual
    have final := Atomics64.fetchAdd_readback _ _ _ _ _ success
    rw [address] at final
    simpa only [published, selected, ↓reduceIte] using final
  · have quiet := AtomicFetchAddHistory64.fetchAdd_other_load valid success
      target cell live (Ne.symm selected)
    simpa only [published, selected, ↓reduceIte] using quiet.trans readBefore

/-- Exact published-memory effect of an actual successful scheduler action.
Ordinary issue, return and blocking retain published RAM; ordinary drains
frame every managed cell. Managed drains and RMWs count as writes even when
their full word equals the prior word. The write is selected by persistent
cell identity from the actual observation. -/
theorem step_read {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (valid : TSO64.WellFormed state profile)
    (success : step state action profile = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : state.world.cells target = some cell) (prior : Word)
    (readBefore : loadQWord (published state.world) cell.address = .ok prior) :
    loadQWord (published result.1.world) cell.address =
      .ok (match writeOf result.2 with
        | none => prior
        | some cause => if cause.cell = target then cause.value else prior) := by
  cases step_origin (profile := profile) success with
  | ordinary liveWorker running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> exact readBefore
  | blocked => exact readBefore
  | rmw liveWorker running code caller fetched bounds empty grant effect =>
    exact rmw_read valid.1 effect.checked target cell live prior readBefore
  | drained liveWorker fifo gate changed effect =>
    cases changed with
    | ordinary changed =>
      exact (AtomicFetchAddHistory64.mutate_load valid.1 changed target cell live).trans readBefore
    | managed current changed =>
      exact managed_publication_read valid.1 current changed target cell live prior readBefore

end EDSL.OS.TSO64.PublishedHistory
