/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Preservation
import EDSL.X86.LockedLogical64.Machine

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- The event's cell and address come from the currently authorized handle.
They are not labels attached to an unrelated memory replacement. -/
theorem logicalDiscard_identity (state : State) (actor : Nat) (identifier : HandleId64)
    (mask : Word) (result : State × Event) (handle : Handle) (cell : Cell)
    (success : logicalDiscard state actor identifier mask = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell)) :
    result.2.cell = handle.cell ∧ result.2.logical.event.address = cell.address := by
  obtain ⟨selected, target, observed, eventEq, _⟩ := logicalDiscard_guarded _ _ _ _ _ success
  have same := Except.ok.inj (authorized.symm.trans observed)
  cases same
  rw [eventEq]
  exact ⟨rfl, rfl⟩

/-- Actual LOCK OR dispatch and the checked OS operation produce the same
full64 event and complete RAM. The incoming memory and operands are current;
the undefined AF choice is arbitrary. Physical LOCK refinement remains an
external obligation under the documented WB/translation/no-alias profile. -/
theorem logicalDiscard_step (state : State) (actor : Nat) (identifier : HandleId64)
    (mask : Word) (result : State × Event) (handle : Handle) (cell : Cell)
    (initial : X86.State) (af : Bool)
    (success : logicalDiscard state actor identifier mask = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (replacement : initial.registers .rsi = mask)
    (decoded : LockedLogical64.decodeAt initial = .ok .orRdiRsi) :
    LockedLogical64.step af initial = .ok ⟨.atomic64 result.2.logical
      (LockedLogical64.afterOr initial (toMemory result.1.legacy.shared.resources.space)
        result.2.logical.event.after af), [.rmw8 cell.address]⟩ := by
  have identity := logicalDiscard_identity _ _ _ _ _ _ _ success authorized
  have data := (authorize_ok _ _ _ _ authorized).2.2.2.2.2
  have primitive := logicalDiscard_primitive _ _ _ _ _ success
  rw [identity.2] at primitive
  rw [LockedLogical64.step_eq_execute af decoded]
  simp [LockedLogical64.execute, memory, operand, replacement, data, primitive,
    LockedLogical64.Instruction.accesses]

/-- Present resource authority, actual operands and a successful decode suffice
for dispatch. No successful future OS mutation is an admission hypothesis. -/
theorem logicalDiscard_step_enabled (state : State) (actor : Nat) (identifier : HandleId64)
    (mask : Word) (handle : Handle) (cell : Cell) (initial : X86.State) (af : Bool)
    (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (replacement : initial.registers .rsi = mask)
    (decoded : LockedLogical64.decodeAt initial = .ok .orRdiRsi) :
    ∃ result, logicalDiscard state actor identifier mask = .ok result ∧
      LockedLogical64.step af initial = .ok ⟨.atomic64 result.2.logical
        (LockedLogical64.afterOr initial (toMemory result.1.legacy.shared.resources.space)
          result.2.logical.event.after af), [.rmw8 cell.address]⟩ := by
  obtain ⟨result, success⟩ := logicalDiscard_enabled _ _ _ _ _ _ valid authorized
  exact ⟨result, success, logicalDiscard_step _ _ _ _ _ _ _ _ _ success authorized
    memory operand replacement decoded⟩

/-- Conversely, an authorized actual atomic dispatch projects to the checked
OS transition with exactly its emitted label, access and final CPU state. -/
theorem step_logicalDiscard (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial final : X86.State) (af : Bool)
    (label : LogicalEvent64) (accesses : List LockedLogical64.Access)
    (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (success : LockedLogical64.step af initial = .ok ⟨.atomic64 label final, accesses⟩) :
    ∃ result, logicalDiscard state actor identifier (initial.registers .rsi) = .ok result ∧
      result.2.logical = label ∧ accesses = [.rmw8 cell.address] ∧
      final = LockedLogical64.afterOr initial (toMemory result.1.legacy.shared.resources.space)
        label.event.after af := by
  have decoded := (LockedLogical64.step_atomic64_sound success).1
  obtain ⟨result, changed, dispatch⟩ := logicalDiscard_step_enabled state actor identifier
    (initial.registers .rsi) handle cell initial af valid authorized memory operand rfl decoded
  have same := Except.ok.inj (dispatch.symm.trans success)
  have labels : result.2.logical = label := by
    cases same
    rfl
  have finalEq : final = LockedLogical64.afterOr initial
      (toMemory result.1.legacy.shared.resources.space) label.event.after af := by
    cases same
    rfl
  have footprint : accesses = [.rmw8 cell.address] := by
    cases same
    rfl
  exact ⟨result, changed, labels, footprint, finalEq⟩

end EDSL.OS.Atomics64
