/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ParityCertificates

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ParityResources
open X86 X86.Sequential OS Corpus.V1 ParityCertificates

private def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELF.CallerResources.initial (file compiler) (input compiler) caller

private def resource (compiler : Compiler) (value : Word) : PureCall.Resources spec :=
  Corpus.Scalar.resource (environment compiler) spec value

private def initial (compiler : Compiler) (value : Word) : State :=
  Corpus.Scalar.initial (environment compiler) spec value

/-- Exercise the registered complete-file certificate through its production
resource bridge at the actual symbol address. Literal mathematical answers
below check both parity values while retaining the original caller authority. -/
theorem actual_parity (compiler : Compiler) (value : Word) (expected : Nat)
    (useful : spec.useful value)
    (mathematics : WordMath.cardinality value % 2 = expected) :
    AllExecutions (initial compiler value) (fun result =>
      ((result.state.registers .rax).setWidth 32).toNat = expected ∧
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
    ELF.CallerResources.initial_facts (ParityWindows.checked compiler) (fresh compiler)
      ELF.CallerResources.Stack.standard_facts (separate compiler)
  have pre := Corpus.Scalar.resource_pre facts spec value rfl trivial
  have selected : (certificate compiler).input = input compiler := by
    cases compiler <;> rfl
  have certified := (certificate compiler).resource
  rw [selected] at certified
  let call : Corpus.LoadedCall .parity64 (file compiler) name (input compiler) := by
    refine ⟨caller.prior, ELF.CallerResources.loaded (file compiler) (input compiler) caller,
      ELF.CallerResources.admitted (ParityWindows.checked compiler) (fresh compiler),
      resource compiler value, initial compiler value, useful, pre, rfl, ?_⟩
    intro _ _
    exact ⟨rfl, rfl⟩
  have present := certified call
  refine ⟨?_, present.2⟩
  intro choices
  obtain ⟨result, execution, post, current⟩ := present.1 choices
  exact ⟨result, execution, post.result.trans mathematics, post.returnAddress,
    post.stackPointer, post.memory, current⟩

example (compiler : Compiler) :
    AllExecutions (initial compiler 0x8000000000000001) (fun result =>
      ((result.state.registers .rax).setWidth 32).toNat = 0 ∧
      result.state.rip = 0x654321 ∧
      result.state.registers .rsp = 0x700010 ∧
      result.state.memory = (initial compiler 0x8000000000000001).memory ∧
      CallResources.Current (resource compiler 0x8000000000000001).call
        (resource compiler 0x8000000000000001).shared result.state) :=
  (actual_parity compiler 0x8000000000000001 0
    Arithmetic64.parity64_useful_separated (by decide +kernel)).1

example (compiler : Compiler) :=
  actual_parity compiler 0x8000000100000001 1
    ((Arithmetic64.parity64_useful_iff _).mpr (by decide +kernel)) (by decide +kernel)

#print axioms actual_parity
end EDSL.Tests.ParityResources
#audit_edsl
