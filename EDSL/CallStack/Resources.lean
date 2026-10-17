/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Contract
import EDSL.OS.StackFrame

set_option warningAsError true

namespace EDSL.CallStack
open X86 OS

structure Resources where
  shared : Borrowing.State
  frame : StackFrame.Descriptor
  value : Word

def resourceInput (resource : Resources) : Input :=
  ⟨resource.value, resource.frame.call.returnAddress, resource.frame.region⟩

/-- Current world, exact whole code window and selected entry metadata. Entry
is independent of code position: helper-prefix bytes remain part of the bound
program. Admission contains no execution, result, or instruction-count premise. -/
structure ResourcePre (program : Program) (resource : Resources) (initial : State) : Prop where
  current : StackFrame.Current resource.frame resource.shared initial
  code : resource.frame.call.bytes = program.bytes
  entry : initial.rip = resource.frame.call.code + BitVec.ofNat 64 program.entry
  entryBound : program.entry < program.bytes.length
  stack : initial.registers .rsp = resource.frame.top
  argument : initial.registers .rdi = resource.value
  capacity : 16 ≤ resource.frame.capacity
  alignment : (initial.registers .rsp).toNat % 16 = 8

/-- The private allocation is disjoint from every live loan's containing
allocation. A disjoint subregion loan on that same allocation would still
freeze writes and is explicitly excluded by the current contract. -/
theorem frame_code_disjoint {frame : StackFrame.Descriptor} {shared : Borrowing.State}
    (contract : StackFrame.Contract frame shared) :
    Ownership.Disjoint frame.region ⟨frame.call.code, frame.call.bytes.length⟩ := by
  obtain ⟨allocation, found, _, _, region⟩ := contract.authority
  obtain ⟨loan, live, _, loanRegion⟩ := contract.pureCall.codeLoan
  obtain ⟨borrowed, foundBorrowed, _, _, contained, _, _⟩ :=
    (contract.wellFormed.2 _ _ live).2
  have different := (contract.unborrowed _ _ live).symm
  have separated := contract.wellFormed.1.2 _ _ _ _ found foundBorrowed different
  have restricted : Ownership.Disjoint allocation.region loan.region := by
    rcases separated with first | last
    · exact Or.inl (Nat.le_trans first contained.1)
    · exact Or.inr (Nat.le_trans contained.2 last)
  simpa only [region, loanRegion] using restricted

theorem ResourcePre.code_base {program resource initial}
    (pre : ResourcePre program resource initial) :
    program.codeBase initial = resource.frame.call.code := by
  simp only [Program.codeBase, pre.entry, BitVec.add_sub_cancel]

/-- Complete current authority supplies the raw machine preconditions. In
particular each stack write/read is authorized by its entire current qword,
and the untouched original caller slot still supplies its actual return word. -/
theorem ResourcePre.machine {program resource initial}
    (pre : ResourcePre program resource initial) :
    Pre program (resourceInput resource) initial := by
  have contract := pre.current.contract
  refine ⟨?_, pre.entryBound, pre.argument, contract.region_valid, ?_, pre.capacity,
    ?_, ?_, ?_, contract.pureCall.returnCanonical, ?_, ?_, pre.alignment⟩
  · rw [pre.current.coupled, pre.code_base, ← pre.code]
    exact contract.pureCall.code
  · change resource.frame.region.base.toNat + resource.frame.region.length =
      (initial.registers .rsp).toNat
    rw [pre.stack]
    exact contract.region_bounds.2
  · intro address inside
    rw [pre.current.coupled]
    exact (contract.ready address inside).writable
  · rw [pre.code_base, ← pre.code]
    exact frame_code_disjoint contract
  · rw [pre.current.coupled, pre.stack]
    exact contract.pureCall.stack
  · rw [pre.stack]
    exact contract.pureCall.stackBound
  · rw [pre.stack]
    exact contract.pureCall.postStackCanonical

end EDSL.CallStack
