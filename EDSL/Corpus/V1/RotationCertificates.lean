/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Scalar
import EDSL.ELF.CallerResources.Stack
import EDSL.Corpus.V1.RotationWindows
import EDSL.Corpus.V1.RotationBodies

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.RotationCertificates
open X86 OS

abbrev Compiler := RotationCode.Compiler
abbrev spec := RotationCode.spec
abbrev file := RotationWindows.file
abbrev name := RotationWindows.name
abbrev input := RotationWindows.input
abbrev caller := ELF.CallerResources.Stack.standard

theorem registration :
    Grading.registered .rotateLeft64 =
      Grading.ofReadOnly (PureCall.readOnlyTask spec) := rfl

theorem fresh (compiler : Compiler) :
    ELF.fresh (input compiler).table.image caller.prior = true := by
  apply ELF.CallerResources.Stack.check_sound _ 0x700008 0x654321
  cases compiler <;> decide +kernel

theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(input compiler).function.window.base,
      (input compiler).bytes.length⟩ caller.region := by
  cases compiler
  · change Ownership.Disjoint ⟨0x402de0, 13⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨0x401350, 9⟩ ⟨0x700008, 8⟩
    decide +kernel

/-- One useful present call inhabits the domain; all values and counts remain
admitted by the mathematical specification and universal body theorems. -/
def usefulValue : Word × BitVec 32 := (0x8123456789abcdef, 4)

def gcc_certificate : Corpus.Certificate .rotateLeft64 (file .defaultGCC) name :=
  Scalar.certificate .rotateLeft64 spec registration (input .defaultGCC)
    (RotationWindows.checked .defaultGCC) RotationBodies.gcc_semantics
    caller (fresh .defaultGCC) ELF.CallerResources.Stack.standard_facts
    (separate .defaultGCC) usefulValue trivial Arithmetic64.rotateLeft_useful_wraparound

def clang_certificate : Corpus.Certificate .rotateLeft64 (file .defaultClang) name :=
  Scalar.certificate .rotateLeft64 spec registration (input .defaultClang)
    (RotationWindows.checked .defaultClang) RotationBodies.clang_semantics
    caller (fresh .defaultClang) ELF.CallerResources.Stack.standard_facts
    (separate .defaultClang) usefulValue trivial Arithmetic64.rotateLeft_useful_wraparound

/-- Bind each independent generated body proof to the unchanged complete ELF,
requested symbol, executable mapping and supplied current caller resources.
The existing sequential target assumptions apply; this is not native CPU/OS
refinement, compiler preservation, concurrency or physical cost evidence. -/
def certificate (compiler : Compiler) : Corpus.Certificate .rotateLeft64 (file compiler) name :=
  match compiler with
  | .defaultGCC => gcc_certificate
  | .defaultClang => clang_certificate

#print axioms registration
#print axioms gcc_certificate
#print axioms clang_certificate
end EDSL.Corpus.V1.RotationCertificates
#audit_edsl
