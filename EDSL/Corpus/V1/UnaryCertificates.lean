/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.Corpus.V1.Comparisons
import EDSL.Corpus.V1.UnaryWindows
import EDSL.Corpus.V1.UnaryBodies

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.UnaryCertificates
open X86 OS

abbrev Compiler := UnaryCode.Compiler
abbrev Operation := UnaryCode.Operation
abbrev spec := UnaryCode.spec
abbrev bytes := UnaryCode.bytes
abbrev file := UnaryWindows.file
abbrev name := UnaryWindows.name
abbrev input := UnaryWindows.input

def taskID : Operation → Grading.TaskID
  | .absSigned32 => .absSigned32
  | .byteSwap64 => .byteSwap64

/-- Equality fixes the entire registered task, including its admission,
independent mathematical relation, ABI, current resources and prefix policy. -/
theorem registration (operation : Operation) :
    Grading.registered (taskID operation) =
      Grading.ofReadOnly (PureCall.readOnlyTask (spec operation)) := by
  cases operation <;> rfl

abbrev caller := Comparisons.caller

theorem fresh (compiler : Compiler) (operation : Operation) :
    ELF.fresh (input compiler operation).table.image caller.prior = true := by
  cases compiler with
  | defaultGCC => exact Comparisons.fresh .defaultGCC .minimum
  | defaultClang => exact Comparisons.fresh .defaultClang .minimum

theorem separate (compiler : Compiler) (operation : Operation) :
    Ownership.Disjoint ⟨(input compiler operation).function.window.base,
      (input compiler operation).bytes.length⟩ caller.region := by
  cases compiler <;> cases operation
  · change Ownership.Disjoint ⟨4205936, 12⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨4206064, 11⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨4199168, 8⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨4199264, 7⟩ ⟨0x700008, 8⟩
    decide +kernel

def environment (compiler : Compiler) (operation : Operation) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler operation) caller

theorem environment_facts (compiler : Compiler) (operation : Operation) :
    CallResources.Domain.Facts (environment compiler operation) :=
  ELFResources.initial_facts (UnaryWindows.checked compiler operation) (fresh compiler operation)
    Comparisons.caller_facts (separate compiler operation)

/-- Present scalar resources reuse the shared current-RAM/loan provider.
The value is arbitrary; usefulness is never an admission requirement. -/
def resource (compiler : Compiler) (operation : Operation) (value : (spec operation).Input) :
    PureCall.Resources (spec operation) :=
  Scalar.resource (environment compiler operation) (spec operation) value

def initial (compiler : Compiler) (operation : Operation) (value : (spec operation).Input) : State :=
  Scalar.initial (environment compiler operation) (spec operation) value

theorem pre (compiler : Compiler) (operation : Operation) (value : (spec operation).Input)
    (domain : (spec operation).domain value) :
    PureCall.ResourcePre (spec operation) (bytes compiler operation)
      (resource compiler operation value) (initial compiler operation value) :=
  Scalar.resource_pre (environment_facts compiler operation) (spec operation) value rfl domain

/-- These values force a mathematical change: -1 has absolute value 1, and
reversing full64 value 1 moves its only nonzero byte to the opposite end. -/
def usefulValue : (operation : Operation) → (spec operation).Input
  | .absSigned32 => (0xffffffff : BitVec 32)
  | .byteSwap64 => (1 : Word)

theorem useful_domain (operation : Operation) :
    (spec operation).domain (usefulValue operation) := by
  cases operation with
  | absSigned32 =>
    change (0xffffffff : BitVec 32).toInt ≠ -2147483648
    decide +kernel
  | byteSwap64 => trivial

theorem useful_value (operation : Operation) :
    (spec operation).useful (usefulValue operation) := by
  cases operation with
  | absSigned32 =>
    change (0xffffffff : BitVec 32).toInt < 0
    decide +kernel
  | byteSwap64 =>
    change WordMath.base256Digit (1 : Word).toNat 0 ≠ 0 ∧
      WordMath.base256Digit (1 : Word).toNat 7 = 0
    decide +kernel

/-- Universal registered contracts for four exact complete named ELF extents,
jointly inhabited by useful current resources at their actual selected entry.
Abs excludes only INT32_MIN and admits arbitrary upper RDI halves; byte reversal
admits every full64 value. The witness's convenience arguments do not narrow
the universal semantic claim.

This inherits sequential long mode, CET/IBT/shadow stacks disabled, stable
ordinary modeled RAM, supplied modeled ownership/loan authority and no
asynchronous interference. Native loading/authority, physical CPU refinement,
source/IR preservation, concurrency and corpus coverage are separate claims. -/
def certificate (compiler : Compiler) (operation : Operation) :
    Corpus.Certificate (taskID operation) (file compiler) (name operation) :=
  Scalar.certificate (taskID operation) (spec operation) (registration operation)
    (input compiler operation) (UnaryWindows.checked compiler operation)
    (UnaryBodies.raw_semantics compiler operation)
    caller (fresh compiler operation) Comparisons.caller_facts (separate compiler operation)
    (usefulValue operation) (useful_domain operation) (useful_value operation)

#print axioms registration
#print axioms environment_facts
#print axioms pre
#print axioms certificate
end EDSL.Corpus.V1.UnaryCertificates
#audit_edsl
