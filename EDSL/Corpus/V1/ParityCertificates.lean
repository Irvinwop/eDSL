/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.ELF.CallerResources.Stack
import EDSL.Corpus.V1.ParityWindows
import EDSL.Corpus.V1.ParityBodies

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.ParityCertificates
open X86 OS

abbrev Compiler := ParityCode.Compiler
abbrev spec := ParityCode.spec
abbrev file := ParityWindows.file
abbrev name := ParityWindows.name
abbrev input := ParityWindows.input
abbrev caller := ELF.CallerResources.Stack.standard

theorem registration :
    Grading.registered .parity64 =
      Grading.ofReadOnly (PureCall.readOnlyTask spec) := rfl

theorem fresh (compiler : Compiler) :
    ELF.fresh (input compiler).table.image caller.prior = true := by
  apply ELF.CallerResources.Stack.check_sound _ 0x700008 0x654321
  cases compiler <;> decide +kernel

theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(input compiler).function.window.base,
      (input compiler).bytes.length⟩ caller.region := by
  cases compiler
  · change Ownership.Disjoint ⟨0x402e20, 33⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨0x401390, 36⟩ ⟨0x700008, 8⟩
    decide +kernel

/-- A useful present call does not restrict the universal full64 domain. -/
def usefulValue : Word := 0x8000000000000001

def gcc_certificate : Corpus.Certificate .parity64 (file .defaultGCC) name :=
  Scalar.certificate .parity64 spec registration (input .defaultGCC)
    (ParityWindows.checked .defaultGCC) ParityBodies.gcc_semantics
    caller (fresh .defaultGCC) ELF.CallerResources.Stack.standard_facts
    (separate .defaultGCC) usefulValue trivial Arithmetic64.parity64_useful_separated

def clang_certificate : Corpus.Certificate .parity64 (file .defaultClang) name :=
  Scalar.certificate .parity64 spec registration (input .defaultClang)
    (ParityWindows.checked .defaultClang) ParityBodies.clang_semantics
    caller (fresh .defaultClang) ELF.CallerResources.Stack.standard_facts
    (separate .defaultClang) usefulValue trivial Arithmetic64.parity64_useful_separated

/-- Complete named files, independent mathematics and original caller authority
compose through the existing scalar constructor. Each artifact supplies only
its own semantic proof. Assumptions retain stable ordinary modeled RAM,
canonical code/stack/return, supplied logical caller loans, CET off and no
asynchronous interference; CPU/OS/compiler refinement and physical cost remain
outside this conditional certificate. -/
def certificate (compiler : Compiler) : Corpus.Certificate .parity64 (file compiler) name :=
  match compiler with
  | .defaultGCC => gcc_certificate
  | .defaultClang => clang_certificate

#print axioms registration
#print axioms gcc_certificate
#print axioms clang_certificate
end EDSL.Corpus.V1.ParityCertificates
#audit_edsl
