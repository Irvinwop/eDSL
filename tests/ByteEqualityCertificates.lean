/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ByteEqualityCertificates
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ByteEqualityCertificates
open X86 X86.Sequential OS OS.AddressSpace BufferCall Corpus.V1
open Corpus.V1.ByteEqualityCertificates

/-- The original caller and both overlapping inputs keep their exact loan
identifiers in the current world of the new function. Code attachment does not
replace their selectors with newly chosen loans. -/
def OriginalAuthority (compiler : Compiler) : Prop :=
  Threads.HasLoan (loaded compiler).resource.shared
    (ByteComparisonResources.resources compiler).call.worker
    (ByteComparisonResources.resources compiler).call.stackLoan
    ⟨(ByteComparisonResources.resources compiler).call.stack, 8⟩ ∧
  Threads.HasLoan (loaded compiler).resource.shared
    (ByteComparisonResources.resources compiler).call.worker
    ((ByteComparisonResources.resources compiler).inputLoan ByteComparisonResources.left)
    ByteComparisonResources.left.region ∧
  Threads.HasLoan (loaded compiler).resource.shared
    (ByteComparisonResources.resources compiler).call.worker
    ((ByteComparisonResources.resources compiler).inputLoan ByteComparisonResources.right)
    ByteComparisonResources.right.region

/-- Apply each final-file certificate to its useful current-resource witness.
The inputs overlap and disagree at their first byte. The expected Boolean comes
from list inequality, independently of the decoded instruction stream. For every
AF stream, execution returns to the original caller with its full stack, memory,
permissions and original input authority intact. -/
theorem actual_overlapping_mismatch (compiler : Compiler) :
    AllExecutions (loaded compiler).initial (fun result =>
      Grading.ByteEquality.returnValue (result.state.registers .rax) = 0 ∧
      result.state.rip = 0x654320 ∧
      result.state.registers .rsp = 0x700010 ∧
      result.state.memory = (loaded compiler).initial.memory ∧
      result.state.memory =
        toMemory (ByteComparisonResources.resources compiler).shared.resources.space ∧
      Current (loaded compiler).resource result.state ∧ OriginalAuthority compiler) ∧
    Grading.ReadOnlyPolicy (loaded compiler).initial (Current (loaded compiler).resource)
      (fun _ read => ReadAllowed (loaded compiler).resource read) := by
  have present := (certificate compiler).resource (loaded compiler)
  refine ⟨?_, present.2⟩
  intro choices
  obtain ⟨result, execution, post, current⟩ := present.1 choices
  have different : (loaded compiler).resource.value.left ≠
      (loaded compiler).resource.value.right :=
    Grading.ByteEquality.unequal_at (index := 0) (a := 0x41) (b := 0x42)
      rfl rfl (by decide +kernel)
  have zero := (Grading.ByteEquality.result_mismatch different _).mp post.result
  have returned : result.state.rip = 0x654320 := post.returnAddress
  have stack : result.state.registers .rsp = 0x700010 := post.stackPointer
  have memory : result.state.memory =
      toMemory (ByteComparisonResources.resources compiler).shared.resources.space := by
    rw [current.coupled]
    exact congrArg toMemory (ByteEqualityResources.space compiler)
  have authority := (Grading.ByteEquality.resourceContract_iff
    (loaded compiler).resource (loaded compiler).resource.shared).mp current.contract
  refine ⟨result, execution, zero, returned, stack, post.memory, memory, current, ?_⟩
  exact ⟨authority.1.stackLoan,
    authority.2.2.2.1 (by change ([0x41, 0x42, 0] : List Byte) ≠ []; decide +kernel),
    authority.2.2.2.2 (by change ([0x42, 0, 0] : List Byte) ≠ []; decide +kernel)⟩

/-- The complete 68-byte Clang extent cannot be admitted through the public
default 64-byte path, even with a completely fresh prior address space. This
checks the admission boundary, rather than the assigned explicit cap. -/
theorem clang_default_admission_rejected (prior : Space) :
    (ByteEqualityWindows.input .defaultClang).admit
      (ByteEqualityWindows.file .defaultClang) ByteEqualityWindows.name prior =
        .error .invalidImage := by
  have rejected : (ByteEqualityWindows.input .defaultClang).checkWith 64
      (ByteEqualityWindows.file .defaultClang) ByteEqualityWindows.name = false := by
    cases observed : (ByteEqualityWindows.input .defaultClang).checkWith 64
        (ByteEqualityWindows.file .defaultClang) ByteEqualityWindows.name with
    | false => rfl
    | true =>
      have selected := (ELF.FunctionSymbol.checked_soundWith observed).2.2.2
      have bound := selected.bounds.2.1
      change (68 : Nat) ≤ 64 at bound
      omega
  change ELF.FunctionSymbol.checkWith 64 _ _ _ _ _ _ = false at rejected
  simp only [Corpus.FunctionInput.admit, Corpus.FunctionInput.admitWith,
    ELF.FunctionInput.admitWith, ELF.FunctionSymbol.admitWith, rejected,
    Bool.false_eq_true, ↓reduceIte]

/-- No useful-loaded-call package can silently downgrade that full Clang
function to the default bound. Its actual explicit-bound package above is used
by the semantic execution regression. -/
theorem clang_default_loaded_call_rejected :
    ¬Nonempty (Corpus.Buffer.LoadedCall .equalBytes
      (ByteEqualityWindows.file .defaultClang) ByteEqualityWindows.name
      (ByteEqualityWindows.input .defaultClang)) := by
  rintro ⟨call⟩
  have accepted := call.admitted
  change (ByteEqualityWindows.input .defaultClang).admit
    (ByteEqualityWindows.file .defaultClang) ByteEqualityWindows.name call.prior =
      .ok call.loaded at accepted
  rw [clang_default_admission_rejected] at accepted
  cases accepted

#print axioms actual_overlapping_mismatch
#print axioms clang_default_admission_rejected
#print axioms clang_default_loaded_call_rejected
end EDSL.Tests.ByteEqualityCertificates
#audit_edsl
