/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy
import EDSL.OS.CallResources

set_option warningAsError true

namespace EDSL.Comparison64
open X86 X86.Sequential

inductive Operation where
  | unsignedMaximum | unsignedMinimum | signedMaximum
  deriving DecidableEq, Repr

/-- Mathematical order specifications independent of flags, instruction
selection, compiler output, conditional expressions and instruction counts. -/
def MathematicalResult : Operation → Word → Word → Word → Prop
  | .unsignedMaximum, left, right, result => result.toNat = max left.toNat right.toNat
  | .unsignedMinimum, left, right, result => result.toNat = min left.toNat right.toNat
  | .signedMaximum, left, right, result => result.toInt = max left.toInt right.toInt

structure Input where
  left : Word
  right : Word
  returnAddress : Word

/-- Present executable bytes, full64 SysV arguments and complete caller slot.
There is no mutable DATA target, decoding, trace or future-success premise. -/
structure Pre (bytes : List Byte) (input : Input) (initial : State) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  left : initial.registers .rdi = input.left
  right : initial.registers .rsi = input.right
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

def calleeSaved : List Register := [.rbx,.rbp,.r12,.r13,.r14,.r15]

/-- Independent result, complete unchanged RAM (including permissions), actual
caller return and SysV frame. Arithmetic status flags are unconstrained. -/
structure Post (operation : Operation) (input : Input) (initial final : State) : Prop where
  result : MathematicalResult operation input.left input.right (final.registers .rax)
  memory : final.memory = initial.memory
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

def Useful (input : Input) : Prop := input.left ≠ input.right

/-- A reusable stronger raw proof route: every actual continuing prefix has
the original complete RAM; all operand reads are from the original STACK8.
This is correctness evidence, never an input admission premise. -/
def RawPolicy (initial : State) : Prop :=
  Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
    (fun _ read => read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8)

end EDSL.Comparison64
