/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.Comparisons
import EDSL.Audit

namespace EDSL.Tests.CorpusCertificates
open X86 X86.Sequential Corpus
open Corpus.V1.Comparisons

-- High full64 operands with equal low32 halves catch a plausible accidental
-- width reduction. Expected results come from unsigned order, not instruction
-- selection, flags, graph metadata or the decoder's comparison logic.
def left : Word := 0xffffffff00000007
def right : Word := 0x100000007

theorem actual_order (compiler : Compiler) (operation : Operation) :
    AllExecutions (Comparison.initial (environment compiler operation) left right)
      (fun result => result.state.registers .rax =
        if operation = .minimum then right else left) := by
  have pre : Comparison64.ResourcePre (input compiler operation).bytes
      (Comparison.resource (environment compiler operation) left right)
      (Comparison.initial (environment compiler operation) left right) :=
    Comparison.resource_pre (environment_facts compiler operation) rfl left right
  rw [body compiler operation] at pre
  have semantic := (X86.VCGen.CompilerComparisons.raw_semantics compiler operation
    _ _ pre.machine).1
  intro choices
  obtain ⟨result, execution, post⟩ := semantic choices
  refine ⟨result, execution, ?_⟩
  have ordered := post.result
  cases operation <;>
    simp only [X86.VCGen.CompilerComparisons.operation, Comparison64.MathematicalResult,
      Comparison64.resourceInput, Comparison.resource] at ordered
  · have expected : min left.toNat right.toNat = right.toNat := by decide +kernel
    have same : (result.state.registers .rax).toNat = right.toNat := ordered.trans expected
    exact BitVec.eq_of_toNat_eq same
  · have expected : max left.toNat right.toNat = left.toNat := by decide +kernel
    have same : (result.state.registers .rax).toNat = left.toNat := ordered.trans expected
    exact BitVec.eq_of_toNat_eq same

#print axioms actual_order
#audit_edsl
end EDSL.Tests.CorpusCertificates
