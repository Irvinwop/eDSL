/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64

namespace EDSL.AtomicLogical64
open X86 OS.AddressSpace
abbrev Shared := OS.Atomics64.State
abbrev Event := OS.Atomics64.Event
abbrev Result := X86.LockedLogical64.Result
abbrev Choices := X86.LockedLogical64.Choices

structure Input where
  actor : Nat
  handle : OS.Atomics64.HandleId64
  codeLoan : Nat
  stackLoan : Nat
  returnAddress : Word

/-- Current stored read authority, not a caller-supplied byte snapshot. -/
def LoanAt (shared : Shared) (actor identifier : Nat) (region : Region) : Prop :=
  ∃ loan, shared.legacy.shared.loans identifier = some loan ∧
    loan.borrower = actor ∧ loan.region = region

/-- Present resources for a callable invocation. No old target value or
successful future mutation/execution is assumed. Native interpretation also
retains the locked profile's physical/lifetime assumptions. -/
structure Resources (candidate : List Byte) (input : Input) (shared : Shared)
    (initial : X86.State) : Prop where
  valid : OS.Atomics64.WellFormed shared
  authority : ∃ handle cell,
    OS.Atomics64.authorize shared input.actor input.handle = .ok (handle, cell) ∧
    initial.registers .rdi = cell.address
  coupled : initial.memory = toMemory shared.legacy.shared.resources.space
  codeLoan : LoanAt shared input.actor input.codeLoan ⟨initial.rip, candidate.length⟩
  stackLoan : LoanAt shared input.actor input.stackLoan ⟨initial.registers .rsp, 8⟩
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

structure Pre (candidate : List Byte) (input : Input) (shared : Shared)
    (initial : X86.State) : Prop extends Resources candidate input shared initial where
  code : CodeAt initial.memory initial.rip candidate

/-- An independent union result in current RAM, actual event identity and
current OS mutation, ABI frame, and exact surviving loan cells. It promises no
old-word ABI return and no source-language memory-order or physical refinement. -/
def ResultContract (input : Input) (shared : Shared) (initial : X86.State) (output : Result) : Prop :=
  ∃ changed : Shared × Event,
    OS.Atomics64.logicalDiscard shared input.actor input.handle (initial.registers .rsi) = .ok changed ∧
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
    Logical64.MathematicalResult .union changed.2.logical.event.before
      (initial.registers .rsi) changed.2.logical.event.after ∧
    (∀ query, 8 ≤ (query - initial.registers .rdi).toNat →
      output.state.memory.read query = initial.memory.read query) ∧
    changed.1.cells = shared.cells ∧ changed.1.handles = shared.handles ∧
    ∀ identifier loan, shared.legacy.shared.loans identifier = some loan →
      changed.1.legacy.shared.loans identifier = some loan ∧
      ∀ query, loan.region.Contains query →
        changed.1.legacy.shared.resources.space.cells query = shared.legacy.shared.resources.space.cells query

theorem Resources.disjoint {candidate input shared initial}
    (resources : Resources candidate input shared initial)
    (handle : OS.Atomics64.Handle) (cell : OS.Atomics64.Cell)
    (authorized : OS.Atomics64.authorize shared input.actor input.handle = .ok (handle, cell)) :
    QWordDisjoint cell.address initial.rip candidate.length ∧
      QWordDisjoint cell.address (initial.registers .rsp) 8 := by
  have linked := (OS.Atomics64.authorize_ok _ _ _ _ authorized).2.2.1
  obtain ⟨code, codeLive, _, codeRegion⟩ := resources.codeLoan
  obtain ⟨stack, stackLive, _, stackRegion⟩ := resources.stackLoan
  have codeFrame := OS.Atomics64.cell_loan_disjoint shared resources.valid handle.cell cell linked
    input.codeLoan code codeLive
  have stackFrame := OS.Atomics64.cell_loan_disjoint shared resources.valid handle.cell cell linked
    input.stackLoan stack stackLive
  exact ⟨by simpa only [codeRegion] using codeFrame, by simpa only [stackRegion] using stackFrame⟩

theorem semantics {input shared initial}
    (pre : Pre OS.Atomics64.Routine.bytes input shared initial) :
    LockedLogical64.AllExecutions initial (ResultContract input shared initial) := by
  obtain ⟨handle, cell, authorized, pointer⟩ := pre.authority
  have disjoint := pre.toResources.disjoint handle cell authorized
  have callable := OS.Atomics64.Routine.correct shared input.actor input.handle handle cell initial
    input.returnAddress pre.valid authorized pre.coupled pointer pre.code disjoint.1 disjoint.2
    pre.stack pre.returnCanonical
  intro choices
  obtain ⟨output, executed, changed, success, count, events, accesses, memory,
    target, rsp, registers, readback, mathematical⟩ := callable choices
  have sound := OS.Atomics64.logicalDiscard_sound _ _ _ _ _ success
  have identity := OS.Atomics64.logicalDiscard_identity _ _ _ _ _ _ _ success authorized
  have effect := OS.Atomics64.logicalDiscard_effect _ _ _ _ _ success
  refine ⟨output, executed, changed, success,
    OS.Atomics64.logicalDiscard_wellFormed _ _ _ _ _ pre.valid success,
    count, events, ?_, memory, target, rsp, registers, ?_, ?_, ?_, mathematical,
    ?_, effect.cells, effect.handles, ?_⟩
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
      OS.Atomics64.logicalDiscard_loan_contents _ _ _ _ _ pre.valid success identifier loan live⟩

theorem ResultContract.instructions {input shared initial output}
    (contract : ResultContract input shared initial output) : output.instructions = 2 := by
  obtain ⟨_, _, _, count, _⟩ := contract
  exact count

theorem run {input shared initial} (pre : Pre OS.Atomics64.Routine.bytes input shared initial)
    (choices : Choices) :
    ∃ output, LockedLogical64.run choices 2 initial = .ok output ∧
      ResultContract input shared initial output := by
  obtain ⟨output, executed, contract⟩ := semantics pre choices
  exact ⟨output, LockedLogical64.run_complete executed (by rw [contract.instructions]; exact Nat.le_refl 2), contract⟩

end EDSL.AtomicLogical64
