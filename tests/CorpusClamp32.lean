/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.Clamps
import EDSL.Audit

namespace EDSL.Tests.CorpusClamp32
open X86 X86.Sequential Corpus
open Corpus.V1.Clamps

/-- A complete return at the selected final ELF symbol, with an independently
specified full-register result and the entire ABI/memory postcondition. -/
def ReturnedAtSymbol (compiler : Compiler) (value : Scalar32.ClampInput)
    (expected : Word) (choices : Choices) : Prop :=
  ∃ result, Sequential.run choices (X86.VCGen.CompilerClamp32.retired compiler)
      (Scalar.initial (environment compiler) Scalar32.clampSigned value) = .ok result ∧
    result.state.registers .rax = expected ∧
    PureCall.Post Scalar32.clampSigned
      (PureCall.resourceInput (Scalar.resource (environment compiler) Scalar32.clampSigned value))
      (Scalar.initial (environment compiler) Scalar32.clampSigned value) result.state

/-- Actual fetched execution in the complete ELF's installed mapping and at
its selected function address. The expected signed result is supplied through
independent interval mathematics; upper RAX is derived from machine evidence.
The complete mathematical/ABI/RAM postcondition is retained. -/
theorem result_at_symbol (compiler : Compiler) (value : Scalar32.ClampInput)
    (expected : BitVec 32) (ordered : value.lower.toInt ≤ value.upper.toInt)
    (mathematics : Scalar32.Clamped value.value.toInt value.lower.toInt
      value.upper.toInt expected.toInt) (choices : Choices) :
    ReturnedAtSymbol compiler value (expected.setWidth 64) choices := by
  have pre : PureCall.ResourcePre Scalar32.clampSigned (input compiler).bytes
      (Scalar.resource (environment compiler) Scalar32.clampSigned value)
      (Scalar.initial (environment compiler) Scalar32.clampSigned value) :=
    Scalar.resource_pre (environment_facts compiler) Scalar32.clampSigned value rfl ordered
  rw [body compiler] at pre
  obtain ⟨result, execution, observed, _⟩ :=
    X86.VCGen.CompilerClamp32.executes compiler _ _ pre.machine choices
  have signed := Scalar32.clamped_unique observed.1.result mathematics
  have narrow : (result.state.registers .rax).setWidth 32 = expected :=
    BitVec.toInt_inj.mp signed
  have natural := congrArg BitVec.toNat narrow
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt observed.2.2.2] at natural
  have full : result.state.registers .rax = expected.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    exact natural
  exact ⟨result, execution, full, observed.1⟩

-- Both actual final-file profiles cover below/above/within interval cases,
-- signed extremes and equal endpoints. These explicitly typed full-register
-- results are independent of any decoded graph fields.
example (compiler : Compiler) (choices : Choices) :
    ReturnedAtSymbol compiler ⟨0x80000000, 0xffffffff, 1⟩ 0xffffffff choices :=
  result_at_symbol compiler ⟨0x80000000, 0xffffffff, 1⟩ 0xffffffff
    (by decide +kernel) (by unfold Scalar32.Clamped; decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :
    ReturnedAtSymbol compiler ⟨0x7fffffff, 0xffffffff, 1⟩ 1 choices :=
  result_at_symbol compiler ⟨0x7fffffff, 0xffffffff, 1⟩ 1
    (by decide +kernel) (by unfold Scalar32.Clamped; decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :
    ReturnedAtSymbol compiler ⟨0xffffffff, 0x80000000, 0x7fffffff⟩ 0xffffffff choices :=
  result_at_symbol compiler ⟨0xffffffff, 0x80000000, 0x7fffffff⟩ 0xffffffff
    (by decide +kernel) (by unfold Scalar32.Clamped; decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :
    ReturnedAtSymbol compiler ⟨0x7fffffff, 0x80000000, 0x7fffffff⟩ 0x7fffffff choices :=
  result_at_symbol compiler ⟨0x7fffffff, 0x80000000, 0x7fffffff⟩ 0x7fffffff
    (by decide +kernel) (by unfold Scalar32.Clamped; decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :
    ReturnedAtSymbol compiler ⟨0, 0xfffffff9, 0xfffffff9⟩ 0xfffffff9 choices :=
  result_at_symbol compiler ⟨0, 0xfffffff9, 0xfffffff9⟩ 0xfffffff9
    (by decide +kernel) (by unfold Scalar32.Clamped; decide +kernel) choices

example (compiler : Compiler) (choices : Choices) :
    ReturnedAtSymbol compiler ⟨0x7fffffff, 0x80000000, 0x80000000⟩ 0x80000000 choices :=
  result_at_symbol compiler ⟨0x7fffffff, 0x80000000, 0x80000000⟩ 0x80000000
    (by decide +kernel) (by unfold Scalar32.Clamped; decide +kernel) choices

end EDSL.Tests.CorpusClamp32

#audit_edsl
