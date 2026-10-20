/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.AverageCertificates

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.AverageBodies
open X86 X86.Sequential OS Corpus.V1 AverageCertificates

/-- Dirty unbound registers and arbitrary flags, with actual frozen code and
the original caller stack. This challenges accidental zero-state assumptions. -/
private def dirty (compiler : Compiler) (value : Word × Word) (flags : Word) : State :=
  { initial compiler value with
    registers := fun register =>
      if register = .rdi ∨ register = .rsi ∨ register = .rsp then
        (initial compiler value).registers register else 0xfedcba9876543210
    flags := flags }

private theorem dirty_pre (compiler : Compiler) (value : Word × Word) (flags : Word) :
    PureCall.ResourcePre spec (bytes compiler) (resource compiler value) (dirty compiler value flags) := by
  have present := pre compiler value
  refine ⟨present.current.sameMemory rfl, present.code, present.entry, ?_, trivial, ?_⟩
  · exact present.stack
  · apply (Arithmetic64.average_bound_iff value _).mpr
    exact (Arithmetic64.average_bound_iff value (initial compiler value)).mp present.arguments

/-- Arbitrary dirty flags and registers still give the correct overflowing
average, exact original-slot read, real RET RSP update and complete frame.
All independent AF streams remain universal. -/
theorem dirty_overflow (compiler : Compiler) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (AverageBodies.retired compiler)
        (dirty compiler (0xffffffffffffffff, 0xfffffffffffffffd) flags) = .ok result ∧
      result.state.registers .rax = 0xfffffffffffffffe ∧
      result.state.rip = caller.returnAddress ∧
      result.state.registers .rsp = caller.stack + 8 ∧
      result.reads = [⟨.stack, caller.stack, 8⟩] ∧
      PureCall.ScratchFrame (.rsp :: AverageBodies.scratch compiler)
        (dirty compiler (0xffffffffffffffff, 0xfffffffffffffffd) flags) result.state := by
  have present := (dirty_pre compiler (0xffffffffffffffff, 0xfffffffffffffffd) flags).machine
  obtain ⟨result, actual, observed, _⟩ := AverageBodies.executes compiler _ _ present choices
  refine ⟨result, actual, ?_, observed.1.returnAddress, observed.1.stackPointer,
    observed.2.2.2, observed.2.1⟩
  apply BitVec.eq_of_toNat_eq
  exact observed.1.result.trans (by
    change ((0xffffffffffffffff : Word).toNat + (0xfffffffffffffffd : Word).toNat) / 2 =
      (0xfffffffffffffffe : Word).toNat
    decide +kernel)

#print axioms dirty_overflow
end EDSL.Tests.AverageBodies
#audit_edsl
