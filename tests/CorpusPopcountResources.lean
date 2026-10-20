/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.PopcountCertificates

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.CorpusPopcountResources
open X86 X86.Sequential OS Corpus.V1 PopcountCertificates

/-- Apply the exact final-file certificate to a present call with an arbitrary
full64 argument. Mathematical expected results are supplied independently of
execution; the original caller/code loans must still hold at actual return. -/
theorem actual_count (compiler : Compiler) (value : Word) (expected : BitVec 32)
    (mathematics : expected.toNat = WordMath.cardinality value) :
    AllExecutions (initial compiler value) (fun result =>
      (result.state.registers .rax).setWidth 32 = expected ∧
      result.state.rip = caller.returnAddress ∧
      CallResources.Current (resource compiler value).call
        (resource compiler value).shared result.state) := by
  have claim := (certificate compiler).claim.1
  change Grading.SemanticClaim (Grading.registered .populationCount64) (bytes compiler) at claim
  rw [registration] at claim
  have semantics := (Grading.old_semanticClaim_iff _ _).mp claim
  have present := semantics.resource _ _ (pre compiler value)
  intro choices
  obtain ⟨result, execution, post, current⟩ := present.1 choices
  refine ⟨result, execution, BitVec.eq_of_toNat_eq ?_, post.returnAddress, current⟩
  exact post.result.trans mathematics.symm

-- Zero exercises the entry bypass and confirms that useful-input witnesses
-- do not narrow the universal admission domain. All-ones requires64 clearing
-- iterations without a wrapping counter. The high-bit case detects low32
-- truncation of the input; the mixed pattern distinguishes bit from byte count.
example (compiler : Compiler) := actual_count compiler 0 0 (by decide +kernel)
example (compiler : Compiler) :=
  actual_count compiler 0xffffffffffffffff 64 (by decide +kernel)
example (compiler : Compiler) :=
  actual_count compiler 0x8000000000000000 1 (by decide +kernel)
example (compiler : Compiler) :=
  actual_count compiler 0x0123456789abcdef 32 (by decide +kernel)

#print axioms actual_count
end EDSL.Tests.CorpusPopcountResources
#audit_edsl
