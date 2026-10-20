/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.Corpus.V1.ClampWindows
import EDSL.Corpus.V1.Comparisons
import EDSL.X86.VCGen.CompilerClamp32

namespace EDSL.Corpus.V1.Clamps
open X86 OS

abbrev Compiler := ClampWindows.Compiler

def file : Compiler → List Byte := ClampWindows.file
def name : List Byte := ClampWindows.name
def input : Compiler → FunctionInput := ClampWindows.input

theorem registration : Grading.registered .clampSigned32 =
    Grading.ofReadOnly (PureCall.readOnlyTask Scalar32.clampSigned) := rfl

theorem checked (compiler : Compiler) :
    (input compiler).check (file compiler) name = true := ClampWindows.checked compiler

theorem body (compiler : Compiler) :
    (input compiler).bytes = X86.VCGen.CompilerClamp32.bytes compiler := by
  cases compiler <;> rfl

/-- Reuse the shared caller and fresh-file facts. The scalar constructor binds
its resources to the selected symbol's actual address in the installed ELF. -/
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

/-- Both exact complete-file/name bindings satisfy the fixed signed low32
interval contract, with useful current resources at the selected ELF address.
Equal endpoints and arbitrary upper argument halves remain in the universal
input domain. No new program interpreter or OS authority constructor is needed.

This inherits sequential long mode, CET/IBT/shadow stacks disabled, stable
ordinary modeled RAM and the supplied caller/resource facts. It does not infer
native ownership, physical CPU refinement, compiler preservation or concurrency.
-/
def certificate (compiler : Compiler) : Certificate .clampSigned32 (file compiler) name :=
  Scalar.certificate .clampSigned32 Scalar32.clampSigned registration (input compiler)
    (checked compiler) (by
      rw [body compiler]
      exact X86.VCGen.CompilerClamp32.raw_semantics compiler)
    caller (fresh compiler) Comparisons.caller_facts (separate compiler)
    ⟨0, 0xffffffff, 1⟩ (by
      change (0xffffffff : BitVec 32).toInt ≤ (1 : BitVec 32).toInt
      decide +kernel) (by
      change (0xffffffff : BitVec 32).toInt < (0 : BitVec 32).toInt ∧
        (0 : BitVec 32).toInt < (1 : BitVec 32).toInt
      decide +kernel)

end EDSL.Corpus.V1.Clamps
