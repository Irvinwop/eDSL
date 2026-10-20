/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Publication
import EDSL.OS.AtomicAccess64

/-!
Managed qword publication satisfies the same complete-memory publication
contract used by the existing mixed FIFO. These adapters do not extend the
scheduler's admission rules or its fetch-add-only history projection.
-/

namespace EDSL.OS.TSO64
open X86 AddressSpace

theorem publishStore_stable {world : World} {actor : Nat}
    {identifier : Atomics64.HandleId64} {value : Word}
    {result : World × Atomics64.StoreEvent64}
    (success : Atomics64.publishStore world actor identifier value = .ok result) :
    Stable world result.1 := by
  have effect := Atomics64.publishStore_effect _ _ _ _ _ success
  exact ⟨effect.shared.allocations, effect.shared.frontier, effect.shared.loans,
    effect.shared.nextLoan, effect.cells, effect.nextCell, effect.handles,
    effect.nextHandle, effect.legacyHandles, effect.legacyNextHandle,
    effect.shared.permissions⟩

/-- Publication retains the actual checked event's address and full64 value,
and equates the entire resulting memory with the existing Mixed byte update. -/
theorem publishStore_publication {world : World} {actor : Nat}
    {identifier : Atomics64.HandleId64} {value : Word}
    {result : World × Atomics64.StoreEvent64}
    (success : Atomics64.publishStore world actor identifier value = .ok result) :
    Publication world result.1 ⟨result.2.address, .qword result.2.value⟩ :=
  ⟨publishStore_stable success, Atomics64.publishStore_projection _ _ _ _ _ success⟩

/-- The original authorized descriptor determines the complete publication
footprint. An unrelated valid handle at the same address is not substituted. -/
theorem publishStore_publication_of_authorized {world : World} {actor : Nat}
    {identifier : Atomics64.HandleId64} {value : Word}
    {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    {result : World × Atomics64.StoreEvent64}
    (success : Atomics64.publishStore world actor identifier value = .ok result)
    (authorized : Atomics64.authorize world actor identifier = .ok (handle, cell)) :
    Publication world result.1 ⟨cell.address, .qword value⟩ := by
  obtain ⟨_, _, current, eventEq, _⟩ := Atomics64.publishStore_guarded _ _ _ _ _ success
  have same := Except.ok.inj (current.symm.trans authorized)
  cases same
  have effect := publishStore_publication success
  simpa only [eventEq] using effect

/-- Present world invariants and current authorization derive publication
enabledness; no future successful store or desired successor is a premise. -/
theorem publishStore_publication_enabled {world : World} {actor : Nat}
    {identifier : Atomics64.HandleId64} {value : Word}
    {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    (valid : Atomics64.WellFormed world)
    (authorized : Atomics64.authorize world actor identifier = .ok (handle, cell)) :
    ∃ result, Atomics64.publishStore world actor identifier value = .ok result ∧
      Publication world result.1 ⟨cell.address, .qword value⟩ := by
  obtain ⟨result, success⟩ := Atomics64.publishStore_enabled _ _ _ _ _ _ valid authorized
  exact ⟨result, success, publishStore_publication_of_authorized success authorized⟩

end EDSL.OS.TSO64
