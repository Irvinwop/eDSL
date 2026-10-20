/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Model
import EDSL.AtomicSet64.Contract
import EDSL.OS.Atomics64.LogicalTrace

namespace EDSL.Grading.AtomicSet64
open X86 OS.AddressSpace

abbrev Shared := EDSL.AtomicSet64.Shared
abbrev Input := EDSL.AtomicSet64.Input
abbrev Event := OS.Atomics64.Event
abbrev Result := LockedSet64.Result
abbrev Choices := LockedSet64.Choices
abbrev LoanAt := EDSL.AtomicSet64.LoanAt

/-- Original invocation regions, present resource authority and exact surviving
resources are operation neutral and shared with the existing OR grader. -/
abbrev Frame := AtomicLogical64.Frame
abbrev frame := AtomicLogical64.frame
abbrev Current := AtomicLogical64.Current
abbrev Preservation := AtomicLogical64.Preservation

theorem Current.of_pre {candidate input shared initial}
    (pre : EDSL.AtomicSet64.Pre candidate input shared initial) :
    Current (frame candidate input shared initial) shared initial :=
  AtomicLogical64.Current.of_pre pre

/-- Whole-instruction coverage uses the ACTUAL generic decode and original
selected extent. It is execution evidence, never an admission restriction. -/
def FetchWithin (descriptor : Frame) (before : X86.State) : Prop :=
  ∃ offset instruction, before.rip = descriptor.code + BitVec.ofNat 64 offset ∧
    LockedSet64.decodeAt before = .ok instruction ∧
    offset + instruction.length ≤ descriptor.bytes.length

theorem FetchWithin.decoded {descriptor before instruction}
    (covered : FetchWithin descriptor before)
    (decoded : LockedSet64.decodeAt before = .ok instruction) :
    ∃ offset, before.rip = descriptor.code + BitVec.ofNat 64 offset ∧
      offset + instruction.length ≤ descriptor.bytes.length := by
  obtain ⟨offset, actual, pc, observed, bound⟩ := covered
  have same := Except.ok.inj (observed.symm.trans decoded)
  subst actual
  exact ⟨offset, pc, bound⟩

/-- An independent desired set result at the ORIGINAL target, with the callable
SysV frame, complete outside-target byte/permission frame and exact surviving
OS resources. Actual instructions may use different operations and retain all
their ordered events. This is an uninterrupted callable result; it does not
assert compound-call linearizability under peer interference. -/
structure Post (desired : Logical64.Operation) (descriptor : Frame) (seed : Shared)
    (initial : X86.State) (evolved : Shared) (final : X86.State) : Prop where
  current : Current descriptor evolved final
  value : ∃ old result,
    loadQWord initial.memory descriptor.target = .ok old ∧
    loadQWord final.memory descriptor.target = .ok result ∧
    Logical64.MathematicalResult desired old (initial.registers .rsi) result
  returnAddress : final.rip = descriptor.input.returnAddress
  stackPointer : final.registers .rsp = descriptor.stack + 8
  preserved : ∀ register ∈ Logical64.calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask
  memory : ∀ query, 8 ≤ (query - descriptor.target).toNat → final.memory.read query = initial.memory.read query
  executable : final.memory.executable = initial.memory.executable
  writable : final.memory.writable = initial.memory.writable
  resources : Preservation seed evolved

end EDSL.Grading.AtomicSet64
