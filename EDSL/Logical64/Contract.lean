/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy
import EDSL.OS.CallResources

set_option warningAsError true

namespace EDSL.Logical64
open X86 X86.Sequential

inductive Operation where
  | intersection | union | symmetricDifference
  deriving DecidableEq, Repr

/-- Membership in the finite set of positions set in a full64 natural. -/
def HasBit (word : Word) (index : Fin 64) : Prop :=
  word.toNat.testBit index = true

/-- Set intersection, union and symmetric difference, specified independently
of instruction selection, machine logical operators, flags and instruction counts. -/
def MathematicalResult : Operation → Word → Word → Word → Prop
  | .intersection, left, right, result =>
    ∀ index : Fin 64, HasBit result index ↔ HasBit left index ∧ HasBit right index
  | .union, left, right, result =>
    ∀ index : Fin 64, HasBit result index ↔ HasBit left index ∨ HasBit right index
  | .symmetricDifference, left, right, result =>
    ∀ index : Fin 64, HasBit result index ↔
      (HasBit left index ∧ ¬HasBit right index) ∨ (HasBit right index ∧ ¬HasBit left index)

/-- The membership contract fixes every result bit, so it admits at most one
full64 answer. This does not assume any backend operation or implementation. -/
theorem MathematicalResult.unique {operation : Operation} {left right first second : Word}
    (firstResult : MathematicalResult operation left right first)
    (secondResult : MathematicalResult operation left right second) : first = second := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index inside
  have membership : HasBit first ⟨index,inside⟩ ↔ HasBit second ⟨index,inside⟩ := by
    cases operation <;> exact (firstResult ⟨index,inside⟩).trans (secondResult ⟨index,inside⟩).symm
  exact Bool.coe_iff_coe.mp (by simpa only [HasBit,BitVec.testBit_toNat] using membership)

structure Input where
  left : Word
  right : Word
  returnAddress : Word

/-- Present code, full64 SysV arguments and original caller bytes. No decoding,
execution, future result, cost, mutable target or source compiler is admitted here. -/
structure Pre (bytes : List Byte) (input : Input) (initial : State) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  left : initial.registers .rdi = input.left
  right : initial.registers .rsi = input.right
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

def calleeSaved : List Register := [.rbx,.rbp,.r12,.r13,.r14,.r15]

/-- The independent full64 result, entire RAM/permission frame, actual caller
return and SysV frame. All six arithmetic flags are unconstrained. -/
structure Post (operation : Operation) (input : Input) (initial final : State) : Prop where
  result : MathematicalResult operation input.left input.right (final.registers .rax)
  memory : final.memory = initial.memory
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- Nontrivial domain witnesses are separate from universal correctness.
Equal and zero operands remain admitted by Pre and ResourcePre. -/
def Useful (input : Input) : Prop :=
  input.left ≠ 0 ∧ input.right ≠ 0 ∧ input.left ≠ input.right

/-- A stronger proof route retaining original RAM at every actual reachable
prefix and authorizing only the original STACK8 operand read. -/
def RawPolicy (initial : State) : Prop :=
  Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
    (fun _ read => read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8)

end EDSL.Logical64
