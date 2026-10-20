/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Model

namespace EDSL.Grading.AtomicLogical64
open X86 OS.AddressSpace

/-- Proof-only registered CPU/OS coupling. A real machine atomic event must
be exactly a current `logicalDiscard` output. RET stutters the current world
and reads the original caller slot. No OS-only/admin history hop is admitted. -/
inductive Step (descriptor : Frame) : Shared → Shared → X86.State → Bool →
    LockedLogical64.Observation → Prop where
  | atomic64 {shared evolved before after af event accesses}
      (actual : LockedLogical64.step af before = .ok ⟨.atomic64 event.logical after, accesses⟩)
      (operation : OS.Atomics64.logicalDiscard shared descriptor.input.actor descriptor.input.handle
        (before.registers .rsi) = .ok (evolved, event)) :
      Step descriptor shared evolved before af ⟨.atomic64 event.logical after, accesses⟩
  | ret {shared before after af accesses}
      (actual : LockedLogical64.step af before = .ok ⟨.returned after, accesses⟩)
      (original : before.registers .rsp = descriptor.stack) :
      Step descriptor shared shared before af ⟨.returned after, accesses⟩

theorem Step.machine {descriptor shared evolved before af observation}
    (step : Step descriptor shared evolved before af observation) :
    LockedLogical64.step af before = .ok observation := by
  cases step with
  | atomic64 actual _ | ret actual _ => exact actual

theorem Step.atomic_operation {descriptor shared evolved before after af label accesses}
    (step : Step descriptor shared evolved before af ⟨.atomic64 label after, accesses⟩) :
    ∃ event, OS.Atomics64.logicalDiscard shared descriptor.input.actor descriptor.input.handle
      (before.registers .rsi) = .ok (evolved, event) ∧ event.logical = label := by
  cases step with
  | atomic64 _ operation => exact ⟨_, operation, rfl⟩

theorem Step.ret_world {descriptor shared evolved before after af accesses}
    (step : Step descriptor shared evolved before af ⟨.returned after, accesses⟩) : evolved = shared := by
  cases step
  rfl

theorem Step.ret_original {descriptor shared evolved before after af accesses}
    (step : Step descriptor shared evolved before af ⟨.returned after, accesses⟩) :
    before.registers .rsp = descriptor.stack := by
  cases step with
  | ret _ original => exact original

/-- A successful actual atomic step derives its checked OS successor from
current authority, rather than requiring successful future OS execution. -/
theorem Step.of_atomic {descriptor shared before after af label accesses}
    (current : Current descriptor shared before)
    (operand : before.registers .rdi = descriptor.target)
    (actual : LockedLogical64.step af before = .ok ⟨.atomic64 label after, accesses⟩) :
    ∃ evolved, Step descriptor shared evolved before af ⟨.atomic64 label after, accesses⟩ := by
  obtain ⟨handle, cell, authorized, _, address⟩ := current.authority
  obtain ⟨result, operation, event, _, _⟩ := OS.Atomics64.step_logicalDiscard shared
    descriptor.input.actor descriptor.input.handle handle cell before after af label accesses
    current.valid authorized current.coupled (operand.trans address.symm) actual
  exact ⟨result.1, by rw [←event] at actual ⊢; exact .atomic64 actual operation⟩

theorem Step.current {descriptor shared evolved before af observation}
    (step : Step descriptor shared evolved before af observation)
    (current : Current descriptor shared before) :
    Current descriptor evolved observation.result.state := by
  cases step with
  | ret actual original => exact current.sameMemory (LockedLogical64.step_returned_sound actual).2.1.memory
  | @atomic64 evolved before after af event accesses actual operation =>
    have machine := (LockedLogical64.step_atomic64_sound actual).2.1
    have sound := OS.Atomics64.logicalDiscard_sound _ _ _ _ _ operation
    have effect := OS.Atomics64.logicalDiscard_effect _ _ _ _ _ operation
    obtain ⟨handle, cell, authorized, linked, address⟩ := current.authority
    have identity := OS.Atomics64.logicalDiscard_identity _ _ _ _ _ _ _ operation authorized
    have disjoint := current.disjoint handle cell authorized
    have nextValid := OS.Atomics64.logicalDiscard_wellFormed _ _ _ _ _ current.valid operation
    have authorizedFacts := OS.Atomics64.authorize_ok _ _ _ _ authorized
    have nextAuthorized := OS.Atomics64.authorize_success evolved descriptor.input.actor descriptor.input.handle
      handle cell nextValid (by rw [effect.handles]; exact authorizedFacts.1)
      authorizedFacts.2.1 (by rw [effect.cells]; exact authorizedFacts.2.2.1)
    have memory : after.memory = toMemory evolved.legacy.shared.resources.space := by
      calc
        after.memory = writeQWordUnchecked before.memory event.logical.event.address event.logical.event.after :=
          machine.transition.2.2.2
        _ = toMemory evolved.legacy.shared.resources.space := by
          rw [current.coupled]
          exact sound.1.2.2.2.symm
    refine ⟨nextValid, ⟨handle, cell, nextAuthorized, linked, address⟩, memory, ?_, ?_,
      machine.preserves_code _ _ current.code (by rw [identity.2]; exact disjoint.1),
      (machine.stack_frame descriptor.stack (by rw [identity.2]; exact disjoint.2)).trans current.stack,
      current.returnCanonical, current.stackBound, current.postStackCanonical⟩
    · obtain ⟨loan, live, borrower, region⟩ := current.codeLoan
      exact ⟨loan, (congrFun effect.shared.loans _).trans live, borrower, region⟩
    · obtain ⟨loan, live, borrower, region⟩ := current.stackLoan
      exact ⟨loan, (congrFun effect.shared.loans _).trans live, borrower, region⟩

theorem Step.preserves {descriptor shared evolved before af observation}
    (step : Step descriptor shared evolved before af observation)
    (current : Current descriptor shared before) : Preservation shared evolved := by
  cases step with
  | ret _ _ => exact .refl _
  | atomic64 _ operation =>
    have effect := OS.Atomics64.logicalDiscard_effect _ _ _ _ _ operation
    exact ⟨effect.shared.allocations, effect.shared.frontier, effect.cells, effect.nextCell,
      effect.handles, effect.nextHandle, effect.legacyHandles, effect.legacyNextHandle,
      effect.shared.loans, effect.shared.nextLoan,
      OS.Atomics64.logicalDiscard_loan_contents _ _ _ _ _ current.valid operation⟩

theorem Step.memory_frame {descriptor shared evolved before af observation}
    (step : Step descriptor shared evolved before af observation)
    (current : Current descriptor shared before) :
    (∀ query, 8 ≤ (query - descriptor.target).toNat →
      observation.result.state.memory.read query = before.memory.read query) ∧
    observation.result.state.memory.executable = before.memory.executable ∧
    observation.result.state.memory.writable = before.memory.writable := by
  cases step with
  | ret actual _ =>
    have memory := (LockedLogical64.step_returned_sound actual).2.1.memory
    refine ⟨?_, congrArg Memory.executable memory, congrArg Memory.writable memory⟩
    intro query outside
    exact congrArg (fun ram : Memory => ram.read query) memory
  | atomic64 actual operation =>
    have effect := (LockedLogical64.step_atomic64_sound actual).2.1
    obtain ⟨handle, cell, authorized, _, address⟩ := current.authority
    have identity := OS.Atomics64.logicalDiscard_identity _ _ _ _ _ _ _ operation authorized
    refine ⟨fun query outside => effect.frame query ?_, effect.permissions⟩
    rw [identity.2, address]
    exact outside

end EDSL.Grading.AtomicLogical64
