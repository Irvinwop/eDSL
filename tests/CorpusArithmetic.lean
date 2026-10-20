/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.Arithmetic
import EDSL.Audit

namespace EDSL.Tests.CorpusArithmetic
open X86 X86.Sequential Corpus
open Corpus.V1.Arithmetic

/-- Actual fetched execution in the complete checked ELF's installed mapping,
at the selected symbol's address with its present caller/code resources.
Expected results are independently supplied natural arithmetic, not graph or
decoder metadata. The full ABI/RAM return contract is retained. -/
theorem result_at_symbol (compiler : Compiler) (left right expected : Word)
    (mathematics : expected.toNat = (left.toNat + right.toNat) % 2^64)
    (choices : Choices) :
    ∃ result, Sequential.run choices (X86.VCGen.CompilerArithmetic.retired compiler)
        (Scalar.initial (environment compiler) Arithmetic64.addition (left, right)) = .ok result ∧
      result.state.registers .rax = expected ∧
      PureCall.Post Arithmetic64.addition
        (PureCall.resourceInput (Scalar.resource (environment compiler) Arithmetic64.addition
          (left, right)))
        (Scalar.initial (environment compiler) Arithmetic64.addition (left, right)) result.state := by
  have pre : PureCall.ResourcePre Arithmetic64.addition (input compiler).bytes
      (Scalar.resource (environment compiler) Arithmetic64.addition (left, right))
      (Scalar.initial (environment compiler) Arithmetic64.addition (left, right)) :=
    Scalar.resource_pre (environment_facts compiler) Arithmetic64.addition
      (left, right) rfl trivial
  rw [body compiler] at pre
  obtain ⟨result, execution, observed, _⟩ :=
    X86.VCGen.CompilerArithmetic.executes compiler _ _ pre.machine choices
  exact ⟨result, execution, BitVec.eq_of_toNat_eq (observed.1.result.trans mathematics.symm),
    observed.1⟩

-- Both actual ELF profiles must handle 64-bit wrap, carry beyond low32 and
-- a noncanonical integer result. LEA must not acquire a memory-read premise.
example (compiler : Compiler) (choices : Choices) :=
  result_at_symbol compiler 0xffffffffffffffff 1 0 (by decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :=
  result_at_symbol compiler 0xffffffff 1 0x100000000 (by decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :=
  result_at_symbol compiler 0x7fffffffffff 1 0x800000000000 (by decide +kernel) choices

end EDSL.Tests.CorpusArithmetic

#audit_edsl
