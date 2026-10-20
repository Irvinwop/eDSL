/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalPreservation
import EDSL.X86.LockedSet64.Machine

namespace EDSL.OS.Atomics64
open X86 AddressSpace

/-- Actual instruction dispatch and the current checked OS operation agree on
the full event, complete RAM and operand footprint for each supported operation.
Physical LOCK refinement is an external obligation of the machine profile. -/
theorem logicalUpdate_step (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (result : State × Event)
    (handle : Handle) (cell : Cell) (initial : X86.State) (af : Bool)
    (success : logicalUpdate op state actor identifier mask = .ok result)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (replacement : initial.registers .rsi = mask)
    (decoded : LockedSet64.decodeAt initial = .ok (.logicalRdiRsi op)) :
    LockedSet64.step af initial = .ok ⟨.atomic64 result.2.logical
      (LockedSet64.afterLogical initial (toMemory result.1.legacy.shared.resources.space)
        result.2.logical.event.after af), [.rmw8 cell.address]⟩ := by
  have identity := logicalUpdate_identity op _ _ _ _ _ _ _ success authorized
  have data := (authorize_ok _ _ _ _ authorized).2.2.2.2.2
  have primitive := logicalUpdate_primitive op _ _ _ _ _ success
  rw [identity.2] at primitive
  rw [LockedSet64.step_eq_execute af decoded]
  simp [LockedSet64.execute, memory, operand, replacement, data, primitive,
    LockedSet64.Instruction.accesses]

/-- Present authority derives the checked mutation; a future-success oracle
is not an input. The current instruction chooses the actual operation. -/
theorem logicalUpdate_step_enabled (op : Sequential.LogicalOp) (state : State) (actor : Nat)
    (identifier : HandleId64) (mask : Word) (handle : Handle) (cell : Cell)
    (initial : X86.State) (af : Bool) (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (replacement : initial.registers .rsi = mask)
    (decoded : LockedSet64.decodeAt initial = .ok (.logicalRdiRsi op)) :
    ∃ result, logicalUpdate op state actor identifier mask = .ok result ∧
      LockedSet64.step af initial = .ok ⟨.atomic64 result.2.logical
        (LockedSet64.afterLogical initial (toMemory result.1.legacy.shared.resources.space)
          result.2.logical.event.after af), [.rmw8 cell.address]⟩ := by
  obtain ⟨result, success⟩ := logicalUpdate_enabled op _ _ _ _ _ _ valid authorized
  exact ⟨result, success, logicalUpdate_step op _ _ _ _ _ _ _ _ _ success authorized
    memory operand replacement decoded⟩

/-- Every authorized actual atomic step projects to its checked OS update.
The operation is recovered from decoding; it is not supplied by the caller. -/
theorem step_logicalUpdate (state : State) (actor : Nat) (identifier : HandleId64)
    (handle : Handle) (cell : Cell) (initial final : X86.State) (af : Bool)
    (label : LogicalEvent64) (accesses : List LockedSet64.Access)
    (valid : WellFormed state)
    (authorized : authorize state actor identifier = .ok (handle, cell))
    (memory : initial.memory = toMemory state.legacy.shared.resources.space)
    (operand : initial.registers .rdi = cell.address)
    (success : LockedSet64.step af initial = .ok ⟨.atomic64 label final, accesses⟩) :
    ∃ op result,
      LockedSet64.decodeAt initial = .ok (.logicalRdiRsi op) ∧
      logicalUpdate op state actor identifier (initial.registers .rsi) = .ok result ∧
      result.2.logical = label ∧ accesses = [.rmw8 cell.address] ∧
      final = LockedSet64.afterLogical initial (toMemory result.1.legacy.shared.resources.space)
        label.event.after af := by
  obtain ⟨op, decoded, _, _⟩ := LockedSet64.step_atomic64_sound success
  obtain ⟨result, changed, dispatch⟩ := logicalUpdate_step_enabled op state actor identifier
    (initial.registers .rsi) handle cell initial af valid authorized memory operand rfl decoded
  have same := Except.ok.inj (dispatch.symm.trans success)
  have labels : result.2.logical = label := by cases same; rfl
  have finalEq : final = LockedSet64.afterLogical initial
      (toMemory result.1.legacy.shared.resources.space) label.event.after af := by cases same; rfl
  have footprint : accesses = [.rmw8 cell.address] := by cases same; rfl
  exact ⟨op, result, decoded, changed, labels, footprint, finalEq⟩

end EDSL.OS.Atomics64
