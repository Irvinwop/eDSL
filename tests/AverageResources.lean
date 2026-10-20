/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.AverageCertificates

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.AverageResources
open X86 X86.Sequential OS Corpus.V1 AverageCertificates

/-- Apply the registered certificate to present resources at the selected
actual frozen address. Expected results use independent natural arithmetic,
with no usefulness requirement on the admitted inputs. -/
theorem actual_average (compiler : Compiler) (value : Word × Word) (expected : Word)
    (mathematics : expected.toNat = (value.1.toNat + value.2.toNat) / 2) :
    AllExecutions (initial compiler value) (fun result =>
      result.state.registers .rax = expected ∧
      result.state.rip = caller.returnAddress ∧
      result.state.registers .rsp = (initial compiler value).registers .rsp + 8 ∧
      result.state.memory = (initial compiler value).memory ∧
      CallResources.Current (resource compiler value).call
        (resource compiler value).shared result.state ∧
      PureCall.ScratchFrame (.rsp :: AverageBodies.scratch compiler)
        (initial compiler value) result.state) := by
  have claim := (certificate compiler).claim.1
  have artifactBytes : (certificate compiler).input.bytes = bytes compiler := by
    cases compiler <;> rfl
  rw [artifactBytes] at claim
  change Grading.SemanticClaim (Grading.registered .average64) (bytes compiler) at claim
  rw [registration] at claim
  have semantic := (Grading.old_semanticClaim_iff _ _).mp claim
  have present := semantic.resource _ _ (pre compiler value)
  intro choices
  obtain ⟨result, execution, post, current⟩ := present.1 choices
  have observed := AverageBodies.observations compiler (pre compiler value).machine execution
  exact ⟨result, execution, BitVec.eq_of_toNat_eq (post.result.trans mathematics.symm),
    post.returnAddress, post.stackPointer, post.memory, current, observed.2.1⟩

-- These literal expectations distinguish floor from rounding, full64 from
-- low32 arguments, logical from arithmetic shift, and unbounded from wrapping
-- input addition. Both operand orders are covered at the high-bit boundary.
example (compiler : Compiler) := actual_average compiler (0, 0) 0 (by decide +kernel)
example (compiler : Compiler) := actual_average compiler (0, 1) 0 (by decide +kernel)
example (compiler : Compiler) :=
  actual_average compiler (0, 0xffffffffffffffff) 0x7fffffffffffffff (by decide +kernel)
example (compiler : Compiler) :=
  actual_average compiler (0xffffffffffffffff, 0) 0x7fffffffffffffff (by decide +kernel)
example (compiler : Compiler) :=
  actual_average compiler (0x8000000000000000, 0) 0x4000000000000000 (by decide +kernel)
example (compiler : Compiler) :=
  actual_average compiler (0xffffffffffffffff, 0xffffffffffffffff)
    0xffffffffffffffff (by decide +kernel)
example (compiler : Compiler) :=
  actual_average compiler (0xffffffffffffffff, 0xfffffffffffffffe)
    0xfffffffffffffffe (by decide +kernel)
example (compiler : Compiler) :=
  actual_average compiler (0xffffffffffffffff, 0xfffffffffffffffd)
    0xfffffffffffffffe (by decide +kernel)

#print axioms actual_average
end EDSL.Tests.AverageResources
#audit_edsl
