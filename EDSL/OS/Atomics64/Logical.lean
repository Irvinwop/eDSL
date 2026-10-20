/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Operations

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- One current-handle-authorized full64 logical RMW. Registration reserves
the complete allocation, and authorization rechecks its owner, epoch, complete
operand, permissions and nonexecutable bytes on every operation. The checked
load/store implementation is one functional transition; interpreting it as a
physical atomic RMW still requires the external machine refinement contract.
Its old value is audit data rather than a source-language return value. -/
def logicalUpdate (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) : Except Fault (State × Event) := do
  let selected ← authorize state actor identifier
  let cell := selected.2
  let old ← (loadQWord (toMemory state.legacy.shared.resources.space) cell.address).mapError Fault.machine
  let value := Sequential.LogicalOp.eval op old mask
  let result ← (Atomics.mutate state.legacy (.store64 cell.owner cell.ticket cell.address value)).mapError Fault.legacy
  return ({ state with legacy := result.1 },
    ⟨actor, identifier, selected.1.cell, ⟨op, mask, ⟨cell.address, old, value⟩⟩⟩)

/-- The additive API preserves the existing OR-only operation exactly. -/
theorem logicalUpdate_bor (state : State) (actor : Nat) (identifier : HandleId64) (mask : Word) :
    logicalUpdate .bor state actor identifier mask = logicalDiscard state actor identifier mask := rfl

theorem logicalUpdate_ok (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (result : State × Event)
    (success : logicalUpdate op state actor identifier mask = .ok result) :
    ∃ handle cell old legacy,
      authorize state actor identifier = .ok (handle, cell) ∧
      loadQWord (toMemory state.legacy.shared.resources.space) cell.address = .ok old ∧
      Atomics.mutate state.legacy
        (.store64 cell.owner cell.ticket cell.address (Sequential.LogicalOp.eval op old mask)) = .ok legacy ∧
      result = ({ state with legacy := legacy.1 },
        ⟨actor, identifier, handle.cell, ⟨op, mask, ⟨cell.address, old, Sequential.LogicalOp.eval op old mask⟩⟩⟩) := by
  cases authorized : authorize state actor identifier with
  | error fault => simp [logicalUpdate, authorized] at success
  | ok selected =>
    cases read : loadQWord (toMemory state.legacy.shared.resources.space) selected.2.address with
    | error fault => simp [logicalUpdate, authorized, read, Except.mapError] at success
    | ok old =>
      cases stored : Atomics.mutate state.legacy
          (.store64 selected.2.owner selected.2.ticket selected.2.address (Sequential.LogicalOp.eval op old mask)) with
      | error fault => simp [logicalUpdate, authorized, read, stored, Except.mapError] at success
      | ok legacy =>
        simp [logicalUpdate, authorized, read, stored, Except.mapError] at success
        exact ⟨selected.1, selected.2, old, legacy, rfl, read, stored, success.symm⟩

end EDSL.OS.Atomics64
