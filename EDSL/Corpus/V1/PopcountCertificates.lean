/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.Corpus.V1.Comparisons
import EDSL.Corpus.V1.PopcountWindows
import EDSL.Corpus.V1.PopcountBodies

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.PopcountCertificates
open X86 OS

abbrev Compiler := PopcountCode.Compiler
abbrev spec := PopcountCode.spec
abbrev bytes := PopcountCode.bytes
abbrev file := PopcountWindows.file
abbrev name := PopcountWindows.name
abbrev input := PopcountWindows.input
abbrev caller := Comparisons.caller

theorem registration :
    Grading.registered .populationCount64 =
      Grading.ofReadOnly (PureCall.readOnlyTask spec) := rfl

theorem fresh (compiler : Compiler) :
    ELF.fresh (input compiler).table.image caller.prior = true := by
  cases compiler with
  | defaultGCC => exact Comparisons.fresh .defaultGCC .minimum
  | defaultClang => exact Comparisons.fresh .defaultClang .minimum

theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(input compiler).function.window.base,
      (input compiler).bytes.length⟩ caller.region := by
  cases compiler
  · change Ownership.Disjoint ⟨4206080, 31⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨4199280, 28⟩ ⟨0x700008, 8⟩
    decide +kernel

def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler) caller

theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  ELFResources.initial_facts (PopcountWindows.checked compiler) (fresh compiler)
    Comparisons.caller_facts (separate compiler)

/-- Present caller/code resources for arbitrary full64 arguments. These use
the shared domain constructor; no result or future run is an admission fact. -/
def resource (compiler : Compiler) (value : Word) : PureCall.Resources spec :=
  Scalar.resource (environment compiler) spec value

def initial (compiler : Compiler) (value : Word) : State :=
  Scalar.initial (environment compiler) spec value

theorem pre (compiler : Compiler) (value : Word) :
    PureCall.ResourcePre spec (bytes compiler)
      (resource compiler value) (initial compiler value) :=
  Scalar.resource_pre (environment_facts compiler) spec value rfl trivial

/-- The exact final symbol has a universal total result/resource proof and a
useful current call at its selected address. Zero and every full64 input remain
admitted; usefulness of 0x81 is only the existential witness. Return means the
unsigned low32 cardinality, without requiring any particular upper RAX bits.

The shared sequential target requires stable ordinary RAM, canonical code and
return addresses, CET/IBT/shadow stacks disabled, supplied logical ownership
and loans, and no asynchronous interference. Native Linux authority/loading,
physical CPU refinement, compiler preservation and concurrent behavior remain
separate obligations. -/
def certificate (compiler : Compiler) :
    Corpus.Certificate .populationCount64 (file compiler) name :=
  Scalar.certificate .populationCount64 spec registration
    (input compiler) (PopcountWindows.checked compiler)
    (PopcountBodies.semantics compiler) caller (fresh compiler)
    Comparisons.caller_facts (separate compiler) (0x81 : Word) trivial
    Arithmetic64.populationCount_useful_asymmetric

#print axioms registration
#print axioms environment_facts
#print axioms pre
#print axioms certificate
end EDSL.Corpus.V1.PopcountCertificates
#audit_edsl
