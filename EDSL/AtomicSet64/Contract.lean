/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicLogical64.Contract
import EDSL.OS.Atomics64.LogicalRoutine

namespace EDSL.AtomicSet64
open X86 OS.AddressSpace

abbrev Shared := AtomicLogical64.Shared
abbrev Event := AtomicLogical64.Event
abbrev Result := LockedSet64.Result
abbrev Choices := LockedSet64.Choices
abbrev Input := AtomicLogical64.Input
abbrev LoanAt := AtomicLogical64.LoanAt
abbrev Resources := AtomicLogical64.Resources
abbrev Pre := AtomicLogical64.Pre

/-- Instruction selection follows the independently named mathematical task. -/
def bytes (operation : Logical64.Operation) : List Byte :=
  OS.Atomics64.LogicalRoutine.bytes operation.toLogicalOp

/-- Current checked mutation and actual event, full RAM and caller return,
independent set membership, and exact surviving resource registries and loans.
The old word is read from current RAM, not returned in an ABI result register.
Source, TSO, physical CPU and kernel refinement remain external. -/
def ResultContract (operation : Logical64.Operation) (input : Input) (shared : Shared)
    (initial : X86.State) (output : Result) : Prop :=
  ∃ changed : Shared × Event,
    OS.Atomics64.logicalUpdate operation.toLogicalOp shared input.actor input.handle
      (initial.registers .rsi) = .ok changed ∧
    OS.Atomics64.WellFormed changed.1 ∧
    output.instructions = 2 ∧ output.events = [changed.2.logical] ∧
    output.accesses = [.rmw8 (initial.registers .rdi), .stack8 (initial.registers .rsp)] ∧
    output.state.memory = toMemory changed.1.legacy.shared.resources.space ∧
    output.state.rip = input.returnAddress ∧
    output.state.registers .rsp = initial.registers .rsp + 8 ∧
    (∀ register, register ≠ .rsp → output.state.registers register = initial.registers register) ∧
    canonical (output.state.registers .rsp) = true ∧
    loadQWord initial.memory (initial.registers .rdi) = .ok changed.2.logical.event.before ∧
    loadQWord output.state.memory (initial.registers .rdi) = .ok changed.2.logical.event.after ∧
    Logical64.MathematicalResult operation changed.2.logical.event.before
      (initial.registers .rsi) changed.2.logical.event.after ∧
    (∀ query, 8 ≤ (query - initial.registers .rdi).toNat →
      output.state.memory.read query = initial.memory.read query) ∧
    changed.1.cells = shared.cells ∧ changed.1.handles = shared.handles ∧
    changed.1.legacy.shared.loans = shared.legacy.shared.loans ∧
    ∀ identifier loan, shared.legacy.shared.loans identifier = some loan →
      changed.1.legacy.shared.loans identifier = some loan ∧
      ∀ query, loan.region.Contains query →
        changed.1.legacy.shared.resources.space.cells query =
          shared.legacy.shared.resources.space.cells query

theorem semantics (operation : Logical64.Operation) {input shared initial}
    (pre : Pre (bytes operation) input shared initial) :
    LockedSet64.AllExecutions initial (ResultContract operation input shared initial) := by
  obtain ⟨handle, cell, authorized, pointer⟩ := pre.authority
  have disjoint := AtomicLogical64.Resources.disjoint pre.toResources handle cell authorized
  have callable := OS.Atomics64.LogicalRoutine.correct operation shared input.actor input.handle
    handle cell initial input.returnAddress pre.valid authorized pre.coupled pointer pre.code
    disjoint.1 disjoint.2 pre.stack pre.returnCanonical
  intro choices
  obtain ⟨output, executed, changed, success, valid, count, events, accesses, memory,
    target, rsp, registers, readback, mathematical⟩ := callable choices
  have sound := OS.Atomics64.logicalUpdate_sound _ _ _ _ _ _ success
  have identity := OS.Atomics64.logicalUpdate_identity _ _ _ _ _ _ _ _ success authorized
  have effect := OS.Atomics64.logicalUpdate_effect _ _ _ _ _ _ success
  refine ⟨output, executed, changed, success, valid, count, events, ?_, memory,
    target, rsp, registers, ?_, ?_, ?_, mathematical, ?_, effect.cells, effect.handles,
    effect.shared.loans, ?_⟩
  · simpa only [pointer] using accesses
  · simpa only [rsp] using pre.postStackCanonical
  · rw [pre.coupled, pointer, ← identity.2]
    exact sound.1.2.2.1
  · simpa only [pointer] using readback
  · intro query outside
    rw [memory, pre.coupled]
    apply sound.1.frame query
    simpa only [identity.2, ← pointer] using outside
  · intro identifier loan live
    exact ⟨(congrFun effect.shared.loans identifier).trans live,
      OS.Atomics64.logicalUpdate_loan_contents _ _ _ _ _ _ pre.valid success identifier loan live⟩

theorem ResultContract.instructions {operation input shared initial output}
    (contract : ResultContract operation input shared initial output) : output.instructions = 2 := by
  obtain ⟨_, _, _, count, _⟩ := contract
  exact count

/-- Exact retired-instruction cost, stated separately from set membership.
It applies to every actual execution, including an unchanged target word. -/
theorem exact2 (operation : Logical64.Operation) {input shared initial choices output}
    (pre : Pre (bytes operation) input shared initial)
    (execution : LockedSet64.Executes choices initial output) : output.instructions = 2 := by
  obtain ⟨certified, actual, contract⟩ := semantics operation pre choices
  have same := execution.fixed_choices_unique actual
  exact same ▸ contract.instructions

theorem run (operation : Logical64.Operation) {input shared initial}
    (pre : Pre (bytes operation) input shared initial) (choices : Choices) :
    ∃ output, LockedSet64.run choices 2 initial = .ok output ∧
      ResultContract operation input shared initial output := by
  obtain ⟨output, executed, contract⟩ := semantics operation pre choices
  exact ⟨output, LockedSet64.run_complete executed
    (by rw [contract.instructions]; exact Nat.le_refl 2), contract⟩

end EDSL.AtomicSet64
