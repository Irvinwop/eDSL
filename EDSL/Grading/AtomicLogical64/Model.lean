/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicLogical64.Contract

namespace EDSL.Grading.AtomicLogical64
open X86 OS.AddressSpace

abbrev Shared := EDSL.AtomicLogical64.Shared
abbrev Input := EDSL.AtomicLogical64.Input
abbrev Event := OS.Atomics64.Event
abbrev Result := LockedLogical64.Result
abbrev Choices := LockedLogical64.Choices
abbrev LoanAt := EDSL.AtomicLogical64.LoanAt

/-- Immutable invocation identities and regions. The code extent and caller
slot are the ORIGINAL regions even after RIP/RSP change. -/
structure Frame where
  bytes : List Byte
  input : Input
  code : Word
  stack : Word
  target : Word
  cell : OS.Atomics64.CellId64

/-- Freeze the cell selected by the stored handle. The missing-handle branch
has no admitted `Pre` witness; it adds no admission or decoding restriction. -/
def frame (candidate : List Byte) (input : Input) (shared : Shared) (initial : X86.State) : Frame :=
  ⟨candidate, input, initial.rip, initial.registers .rsp, initial.registers .rdi,
    match shared.handles input.handle with | some handle => handle.cell | none => ⟨0⟩⟩

/-- Present authority, current RAM and ORIGINAL named loans. There is no
assumption about any future instruction, opcode, fuel, result or operation count. -/
structure Current (descriptor : Frame) (shared : Shared) (cpu : X86.State) : Prop where
  valid : OS.Atomics64.WellFormed shared
  authority : ∃ handle cell,
    OS.Atomics64.authorize shared descriptor.input.actor descriptor.input.handle = .ok (handle, cell) ∧
    handle.cell = descriptor.cell ∧ cell.address = descriptor.target
  coupled : cpu.memory = toMemory shared.legacy.shared.resources.space
  codeLoan : LoanAt shared descriptor.input.actor descriptor.input.codeLoan
    ⟨descriptor.code, descriptor.bytes.length⟩
  stackLoan : LoanAt shared descriptor.input.actor descriptor.input.stackLoan ⟨descriptor.stack, 8⟩
  code : CodeAt cpu.memory descriptor.code descriptor.bytes
  stack : readWord cpu.memory descriptor.stack = .ok descriptor.input.returnAddress
  returnCanonical : canonical descriptor.input.returnAddress = true
  stackBound : descriptor.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (descriptor.stack + 8) = true

theorem Current.of_pre {candidate input shared initial}
    (pre : EDSL.AtomicLogical64.Pre candidate input shared initial) :
    Current (frame candidate input shared initial) shared initial := by
  obtain ⟨handle, cell, authorized, address⟩ := pre.authority
  have stored := (OS.Atomics64.authorize_ok _ _ _ _ authorized).1
  refine ⟨pre.valid, ?_, pre.coupled, pre.codeLoan, pre.stackLoan, pre.code,
    pre.stack, pre.returnCanonical, pre.stackBound, pre.postStackCanonical⟩
  exact ⟨handle, cell, authorized, by simp [frame, stored], address.symm⟩

theorem Current.sameMemory {descriptor shared before after}
    (current : Current descriptor shared before) (memory : after.memory = before.memory) :
    Current descriptor shared after :=
  ⟨current.valid, current.authority, memory.trans current.coupled,
    current.codeLoan, current.stackLoan, by simpa only [memory] using current.code,
    by simpa only [memory] using current.stack,
    current.returnCanonical, current.stackBound, current.postStackCanonical⟩

theorem Current.disjoint {descriptor shared cpu} (current : Current descriptor shared cpu)
    (handle : OS.Atomics64.Handle) (cell : OS.Atomics64.Cell)
    (authorized : OS.Atomics64.authorize shared descriptor.input.actor descriptor.input.handle = .ok (handle, cell)) :
    QWordDisjoint cell.address descriptor.code descriptor.bytes.length ∧
      QWordDisjoint cell.address descriptor.stack 8 := by
  have linked := (OS.Atomics64.authorize_ok _ _ _ _ authorized).2.2.1
  obtain ⟨code, codeLive, _, codeRegion⟩ := current.codeLoan
  obtain ⟨stack, stackLive, _, stackRegion⟩ := current.stackLoan
  have codeFrame := OS.Atomics64.cell_loan_disjoint shared current.valid
    handle.cell cell linked descriptor.input.codeLoan code codeLive
  have stackFrame := OS.Atomics64.cell_loan_disjoint shared current.valid
    handle.cell cell linked descriptor.input.stackLoan stack stackLive
  exact ⟨by simpa only [codeRegion] using codeFrame, by simpa only [stackRegion] using stackFrame⟩

/-- Whole-instruction coverage uses the ACTUAL decode and original selected
extent. It belongs to execution evidence, never initial admission. -/
def FetchWithin (descriptor : Frame) (before : X86.State) : Prop :=
  ∃ offset instruction, before.rip = descriptor.code + BitVec.ofNat 64 offset ∧
    LockedLogical64.decodeAt before = .ok instruction ∧
    offset + instruction.length ≤ descriptor.bytes.length

theorem FetchWithin.decoded {descriptor before instruction}
    (covered : FetchWithin descriptor before)
    (decoded : LockedLogical64.decodeAt before = .ok instruction) :
    ∃ offset, before.rip = descriptor.code + BitVec.ofNat 64 offset ∧
      offset + instruction.length ≤ descriptor.bytes.length := by
  obtain ⟨offset, actual, pc, observed, bound⟩ := covered
  have same := Except.ok.inj (observed.symm.trans decoded)
  subst actual
  exact ⟨offset, pc, bound⟩

/-- Exact current resource registries, monotone frontiers and surviving loan
cells. Atomic effects can change the target bytes, never these resources. -/
structure Preservation (before after : Shared) : Prop where
  allocations : after.legacy.shared.resources.allocations = before.legacy.shared.resources.allocations
  frontier : after.legacy.shared.resources.frontier = before.legacy.shared.resources.frontier
  cells : after.cells = before.cells
  nextCell : after.nextCell = before.nextCell
  handles : after.handles = before.handles
  nextHandle : after.nextHandle = before.nextHandle
  legacyHandles : after.legacy.handles = before.legacy.handles
  legacyNextHandle : after.legacy.nextHandle = before.legacy.nextHandle
  loans : after.legacy.shared.loans = before.legacy.shared.loans
  nextLoan : after.legacy.shared.nextLoan = before.legacy.shared.nextLoan
  contents : ∀ identifier loan, before.legacy.shared.loans identifier = some loan →
    ∀ query, loan.region.Contains query →
      after.legacy.shared.resources.space.cells query = before.legacy.shared.resources.space.cells query

theorem Preservation.refl (shared : Shared) : Preservation shared shared :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem Preservation.trans {before middle after : Shared}
    (first : Preservation before middle) (last : Preservation middle after) : Preservation before after :=
  ⟨last.allocations.trans first.allocations, last.frontier.trans first.frontier,
    last.cells.trans first.cells, last.nextCell.trans first.nextCell,
    last.handles.trans first.handles, last.nextHandle.trans first.nextHandle,
    last.legacyHandles.trans first.legacyHandles, last.legacyNextHandle.trans first.legacyNextHandle,
    last.loans.trans first.loans, last.nextLoan.trans first.nextLoan,
    fun identifier loan live query inside =>
      (last.contents identifier loan ((congrFun first.loans identifier).trans live) query inside).trans
        (first.contents identifier loan live query inside)⟩

/-- Independent natural-bit union at the ORIGINAL target, callable SysV frame,
full outside-target byte/permission frame and exact surviving OS resources.
No instruction count, event count, mask sequence or opcode choice is specified. -/
structure Post (descriptor : Frame) (seed : Shared) (initial : X86.State)
    (evolved : Shared) (final : X86.State) : Prop where
  current : Current descriptor evolved final
  value : ∃ old result,
    loadQWord initial.memory descriptor.target = .ok old ∧
    loadQWord final.memory descriptor.target = .ok result ∧
    Logical64.MathematicalResult .union old (initial.registers .rsi) result
  returnAddress : final.rip = descriptor.input.returnAddress
  stackPointer : final.registers .rsp = descriptor.stack + 8
  preserved : ∀ register ∈ Logical64.calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask
  memory : ∀ query, 8 ≤ (query - descriptor.target).toNat → final.memory.read query = initial.memory.read query
  executable : final.memory.executable = initial.memory.executable
  writable : final.memory.writable = initial.memory.writable
  resources : Preservation seed evolved

end EDSL.Grading.AtomicLogical64
