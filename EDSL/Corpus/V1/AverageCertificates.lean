/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.ELF.CallerResources.Stack
import EDSL.Corpus.V1.AverageWindows
import EDSL.Corpus.V1.AverageBodies

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.AverageCertificates
open X86 OS

abbrev Compiler := AverageCode.Compiler
abbrev spec := AverageCode.spec
abbrev bytes := AverageCode.bytes
abbrev file := AverageWindows.file
abbrev name := AverageWindows.name
abbrev input := AverageWindows.input
abbrev caller := ELF.CallerResources.Stack.standard

/-- The registry fixes the whole independent contract and admission policy. -/
theorem registration :
    Grading.registered .average64 =
      Grading.ofReadOnly (PureCall.readOnlyTask spec) := rfl

theorem fresh (compiler : Compiler) :
    ELF.fresh (input compiler).table.image caller.prior = true := by
  apply ELF.CallerResources.Stack.check_sound _ 0x700008 0x654321
  cases compiler <;> decide +kernel

theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(input compiler).function.window.base,
      (input compiler).bytes.length⟩ caller.region := by
  cases compiler
  · change Ownership.Disjoint ⟨4206016, 20⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨4199232, 16⟩ ⟨0x700008, 8⟩
    decide +kernel

def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler) caller

theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  ELFResources.initial_facts (AverageWindows.checked compiler) (fresh compiler)
    ELF.CallerResources.Stack.standard_facts (separate compiler)

/-- Actual current caller/code resources for every full64 pair, with no result
or future-run premise. The original caller loan is supplied by the shared
domain constructor and retained by the production semantics bridge. -/
def resource (compiler : Compiler) (value : Word × Word) : PureCall.Resources spec :=
  Scalar.resource (environment compiler) spec value

def initial (compiler : Compiler) (value : Word × Word) : State :=
  Scalar.initial (environment compiler) spec value

theorem pre (compiler : Compiler) (value : Word × Word) :
    PureCall.ResourcePre spec (bytes compiler)
      (resource compiler value) (initial compiler value) :=
  Scalar.resource_pre (environment_facts compiler) spec value rfl trivial

/-- Distinct high operands make the input sum overflow unsigned full64.
This selects a useful existential call and never narrows universal admission. -/
def usefulValue : Word × Word := (0xffffffffffffffff, 0xfffffffffffffffd)

theorem useful_value : spec.useful usefulValue :=
  Arithmetic64.average_useful_overflow_asymmetric

/-- The GCC constructor supplies only GCC's generated semantic evidence. -/
def gcc_certificate : Corpus.Certificate .average64 (file .defaultGCC) name :=
  Scalar.certificate .average64 spec registration (input .defaultGCC)
    (AverageWindows.checked .defaultGCC) AverageBodies.gcc_semantics
    caller (fresh .defaultGCC) ELF.CallerResources.Stack.standard_facts (separate .defaultGCC)
    usefulValue trivial useful_value

/-- Independent Clang semantic evidence is selected before packet construction. -/
def clang_certificate : Corpus.Certificate .average64 (file .defaultClang) name :=
  Scalar.certificate .average64 spec registration (input .defaultClang)
    (AverageWindows.checked .defaultClang) AverageBodies.clang_semantics
    caller (fresh .defaultClang) ELF.CallerResources.Stack.standard_facts (separate .defaultClang)
    usefulValue trivial useful_value

/-- Complete named frozen-symbol certificates for the registered independent
contract. The fixed contract admits overflow and every full64 pair.
Per-artifact constructors avoid importing another compiler's annotation proof
as packet semantic evidence.

The sequential target assumes stable ordinary modeled RAM, canonical code and
return addresses, CET/IBT/shadow stacks disabled, supplied logical ownership
and caller loans, and no asynchronous interference. Physical CPU/Linux/OS
refinement, source/IR/compiler preservation and physical cost are not claimed. -/
def certificate (compiler : Compiler) : Corpus.Certificate .average64 (file compiler) name :=
  match compiler with
  | .defaultGCC => gcc_certificate
  | .defaultClang => clang_certificate

#print axioms registration
#print axioms environment_facts
#print axioms pre
#print axioms gcc_certificate
#print axioms clang_certificate
end EDSL.Corpus.V1.AverageCertificates
#audit_edsl
