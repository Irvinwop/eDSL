/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.RotationCertificates

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.RotationResources
open X86 X86.Sequential OS Corpus.V1 RotationCertificates

private def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELF.CallerResources.initial (file compiler) (input compiler) caller

private def resource (compiler : Compiler) (value : Word × BitVec 32) : PureCall.Resources spec :=
  Corpus.Scalar.resource (environment compiler) spec value

private def initial (compiler : Compiler) (value : Word × BitVec 32) : State :=
  Corpus.Scalar.initial (environment compiler) spec value

/-- Exercise the registered final-file certificate and actual current-resource
bridge. The expected result is supplied through the independent bit-origin
contract, rather than through the instruction's rotate operation. -/
theorem actual_rotation (compiler : Compiler) (value : Word × BitVec 32) (expected : Word)
    (useful : spec.useful value)
    (mathematics : WordMath.IsRotateLeft64 value.1 value.2.toNat expected) :
    AllExecutions (initial compiler value) (fun result =>
      result.state.registers .rax = expected ∧
      result.state.rip = caller.returnAddress ∧
      result.state.registers .rsp = (initial compiler value).registers .rsp + 8 ∧
      result.state.memory = (initial compiler value).memory ∧
      CallResources.Current (resource compiler value).call
        (resource compiler value).shared result.state) ∧
    Grading.ReadOnlyPolicy (initial compiler value)
      (CallResources.Current (resource compiler value).call (resource compiler value).shared)
      (fun _ read => CallResources.ReadAllowed (resource compiler value).call
        (resource compiler value).shared read) := by
  have facts : CallResources.Domain.Facts (environment compiler) :=
    ELF.CallerResources.initial_facts (RotationWindows.checked compiler) (fresh compiler)
      ELF.CallerResources.Stack.standard_facts (separate compiler)
  have pre := Corpus.Scalar.resource_pre facts spec value rfl trivial
  have selected : (certificate compiler).input = input compiler := by
    cases compiler <;> rfl
  have certified := (certificate compiler).resource
  rw [selected] at certified
  let call : Corpus.LoadedCall .rotateLeft64 (file compiler) name (input compiler) := by
    refine ⟨caller.prior, ELF.CallerResources.loaded (file compiler) (input compiler) caller,
      ELF.CallerResources.admitted (RotationWindows.checked compiler) (fresh compiler),
      resource compiler value, initial compiler value, useful, pre, rfl, ?_⟩
    intro _ _
    exact ⟨rfl, rfl⟩
  have present := certified call
  refine ⟨?_, present.2⟩
  intro choices
  obtain ⟨result, execution, post, current⟩ := present.1 choices
  exact ⟨result, execution, WordMath.isRotateLeft_unique post.result mathematics,
    post.returnAddress, post.stackPointer, post.memory, current⟩

-- Wraparound of the top hexadecimal digit into the low digit is independently
-- fixed here; the certificate must retain actual code and caller authority.
example (compiler : Compiler) :=
  actual_rotation compiler (0x8123456789abcdef, 4) 0x123456789abcdef8
    Arithmetic64.rotateLeft_useful_wraparound (by
      intro i hi
      have bits : ∀ position : Fin 64,
          (0x123456789abcdef8 : Word).getLsbD position.val =
            (0x8123456789abcdef : Word).getLsbD ((position.val + 64 - 4 % 64) % 64) := by
        decide +kernel
      exact bits ⟨i, hi⟩)

#print axioms actual_rotation
end EDSL.Tests.RotationResources
#audit_edsl
