/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.Corpus.V1.ArithmeticWindows
import EDSL.Corpus.V1.Comparisons
import EDSL.X86.VCGen.CompilerArithmetic

namespace EDSL.Corpus.V1.Arithmetic
open X86 OS

abbrev Compiler := ArithmeticWindows.Compiler

def file : Compiler → List Byte := ArithmeticWindows.file
def name : List Byte := ArithmeticWindows.name
def input : Compiler → FunctionInput := ArithmeticWindows.input

theorem registration : Grading.registered .addModulo64 =
    Grading.ofReadOnly (PureCall.readOnlyTask Arithmetic64.addition) := rfl

theorem checked (compiler : Compiler) :
    (input compiler).check (file compiler) name = true := ArithmeticWindows.checked compiler

theorem body (compiler : Compiler) :
    (input compiler).bytes = X86.VCGen.CompilerArithmetic.bytes compiler := by
  cases compiler <;> rfl

/-- The existing independently supplied caller slot is reused, rather than
adding another routine-specific OS domain or inferring native authority. -/
def caller : ELFResources.Caller := Comparisons.caller

theorem fresh (compiler : Compiler) :
    ELF.fresh (input compiler).table.image caller.prior = true := by
  cases compiler with
  | defaultGCC => exact Comparisons.fresh .defaultGCC .minimum
  | defaultClang => exact Comparisons.fresh .defaultClang .minimum

theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(input compiler).function.window.base,
      (input compiler).bytes.length⟩ caller.region := by
  cases compiler <;> decide +kernel

def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler) caller

theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  ELFResources.initial_facts (checked compiler) (fresh compiler)
    Comparisons.caller_facts (separate compiler)

/-- Exact named final-ELF bytes, independent unsigned modular addition, and
useful current resources at the actual selected address. Shared scalar/VCG/ELF
rules supply all plumbing. Overflow remains in the universal input domain.

This inherits the fixed sequential long-mode/CET-disabled target, stable modeled
RAM and registered caller/resource assumptions. There is no native loading,
physical CPU, source/IR preservation or concurrent-history conclusion. -/
def certificate (compiler : Compiler) : Certificate .addModulo64 (file compiler) name :=
  Scalar.certificate .addModulo64 Arithmetic64.addition registration (input compiler)
    (checked compiler) (by
      rw [body compiler]
      exact X86.VCGen.CompilerArithmetic.raw_semantics compiler)
    caller (fresh compiler) Comparisons.caller_facts (separate compiler)
    (0xffffffffffffffff, 1) trivial (by
      change (0xffffffffffffffff : Word) ≠ 0 ∧ (1 : Word) ≠ 0
      exact ⟨by decide +kernel, by decide +kernel⟩)

end EDSL.Corpus.V1.Arithmetic
