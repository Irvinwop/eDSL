/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.CompilerArithmetic
import EDSL.OS.CallResources.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CompilerArithmetic
open X86 X86.Sequential X86.VCGen OS
open X86.VCGen.CompilerComparisons (Compiler)
open X86.VCGen.CompilerArithmetic

-- Distinct supplied entry addresses also exercise selection of the complete
-- GCC prefix versus the Clang window. These are modeled mappings, not ELF facts.
def codeBase : Compiler → Word
  | .defaultGCC => 0x401300
  | .defaultClang => 0x501320
def stackBase : Word := 0x700008
def continuation : Word := 0x654321

def space (compiler : Compiler) : AddressSpace.Space where
  cells address :=
    if (⟨codeBase compiler, (bytes compiler).length⟩ : AddressSpace.Region).Contains address then
      ((bytes compiler)[address.toNat - (codeBase compiler).toNat]?).map fun byte =>
        ⟨byte, AddressSpace.readExecute⟩
    else if (⟨stackBase, 8⟩ : AddressSpace.Region).Contains address then
      some ⟨continuation.extractLsb' ((address.toNat - stackBase.toNat) * 8) 8,
        AddressSpace.readOnly⟩
    else if address = 0x900000 then some ⟨0xa5, AddressSpace.readWrite⟩
    else if address = 0x900001 then some ⟨0x5a, AddressSpace.inaccessible⟩
    else none

def declared (compiler : Compiler) : CallResources.Domain.Initial :=
  ⟨space compiler, 17, 29, 41, codeBase compiler, bytes compiler, stackBase, continuation⟩

theorem present (compiler : Compiler) : CallResources.Domain.Facts (declared compiler) := by
  apply CallResources.Domain.check_sound
  cases compiler <;> decide +kernel

def resource (compiler : Compiler) (left right : Word) : PureCall.Resources Arithmetic64.addition :=
  ⟨CallResources.Domain.shared (declared compiler),
    CallResources.Domain.call (declared compiler), (left, right)⟩

def caller (compiler : Compiler) (left right : Word)
    (registers : Register → Word) (flags : Word) : State :=
  CallResources.Domain.machine (declared compiler)
    (fun register => if register = .rdi then left else if register = .rsi then right
      else registers register) flags

theorem admitted (compiler : Compiler) (left right : Word)
    (registers : Register → Word) (flags : Word) :
    PureCall.ResourcePre Arithmetic64.addition (bytes compiler) (resource compiler left right)
      (caller compiler left right registers flags) := by
  refine ⟨CallResources.Domain.current (present compiler) _ _, rfl, rfl, ?_, trivial, ?_⟩
  · simp [caller, CallResources.Domain.machine, declared, resource, CallResources.Domain.call]
  · apply (Arithmetic64.bound_iff _ _).mpr
    simp [caller, CallResources.Domain.machine, resource]

/-- Real decoded return, ABI/whole-RAM frames, all flags, exact profile count
and the original caller read retain the same resource world. Its actual read
origin is backed by current loans and a successful eight-byte read. -/
theorem current_execution (compiler : Compiler) (left right : Word)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    let res := resource compiler left right
    let initial := caller compiler left right registers flags
    ∃ result, Sequential.Executes choices initial result ∧
      PureCall.Post Arithmetic64.addition (PureCall.resourceInput res) initial result.state ∧
      CallResources.Current res.call res.shared result.state ∧
      result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
      result.state.flags = flags ∧
      ∃ count before priorReads observation, count < result.instructions ∧
        Block choices initial before count priorReads ∧
        Sequential.step (choices count) before = .ok observation ∧
        stackRead initial ∈ observation.reads ∧ CallResources.Current res.call res.shared before ∧
        CallResources.ReadAllowed res.call res.shared (stackRead initial) ∧
        OperandReadSucceeds before (stackRead initial) := by
  dsimp only
  have pre := admitted compiler left right registers flags
  obtain ⟨executions, policy⟩ := (raw_semantics compiler).resource _ _ pre
  obtain ⟨result, execution, post, current⟩ := executions choices
  have observed := observations compiler pre.machine execution
  have read : stackRead (caller compiler left right registers flags) ∈ result.reads := by
    rw [observed.2.1]
    simp
  exact ⟨result, execution, post, current, observed.1, observed.2.1, observed.2.2,
    policy.read_origin execution read⟩

/-- Useful overflowing inputs are inhabited from present mappings and bindings
alone, at either supplied address. No execution/output premise is admitted. -/
theorem nonvacuous (compiler : Compiler) :
    Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask Arithmetic64.addition) (bytes compiler) :=
  PureCall.nonvacuous_of_resource (resource compiler 0xffffffffffffffff 1)
    (caller compiler 0xffffffffffffffff 1 (fun _ => 0) 0)
    (by change (0xffffffffffffffff : Word) ≠ 0 ∧ (1 : Word) ≠ 0; decide +kernel)
    (admitted compiler _ _ _ _)

def Returns (compiler : Compiler) (left right expected : Word)
    (registers : Register → Word) (flags : Word) (choices : Choices) : Prop :=
  ∃ result, Sequential.run choices (retired compiler)
      (caller compiler left right registers flags) = .ok result ∧
    result.state.registers .rax = expected ∧
    Observed compiler (PureCall.resourceInput (resource compiler left right))
      (caller compiler left right registers flags) result

/-- Expected literals are checked by independent natural arithmetic. The
production run still fetches/decodes bytes and returns through the real slot;
incoming unrelated registers, all flags and all AF choices remain arbitrary. -/
theorem numeric_result (compiler : Compiler) (left right expected : Word)
    (mathematics : expected.toNat = (left.toNat + right.toNat) % 2^64)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler left right expected registers flags choices := by
  obtain ⟨result, actual, observed, _⟩ := executes compiler _ _
    (admitted compiler left right registers flags).machine choices
  refine ⟨result, actual, BitVec.eq_of_toNat_eq ?_, observed⟩
  exact observed.1.result.trans mathematics.symm

theorem wrapping (compiler : Compiler) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler 0xffffffffffffffff 1 0 registers flags choices :=
  numeric_result compiler 0xffffffffffffffff 1 0 (by decide +kernel) registers flags choices

theorem high_bit_wrap (compiler : Compiler) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler 0x8000000000000000 0x8000000000000000 0 registers flags choices :=
  numeric_result compiler 0x8000000000000000 0x8000000000000000 0
    (by decide +kernel) registers flags choices

theorem full64_carry (compiler : Compiler) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler 0xffffffff 1 0x100000000 registers flags choices :=
  numeric_result compiler 0xffffffff 1 0x100000000 (by decide +kernel) registers flags choices

theorem noncanonical_integer (compiler : Compiler) (registers : Register → Word) (flags : Word)
    (choices : Choices) :
    Returns compiler 0x7fffffffffff 1 0x800000000000 registers flags choices :=
  numeric_result compiler 0x7fffffffffff 1 0x800000000000 (by decide +kernel) registers flags choices

theorem zero_left (compiler : Compiler) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler 0 0xffffffffffffffff 0xffffffffffffffff registers flags choices :=
  numeric_result compiler 0 0xffffffffffffffff 0xffffffffffffffff
    (by decide +kernel) registers flags choices

theorem zero_right (compiler : Compiler) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler 0x8000000000000000 0 0x8000000000000000 registers flags choices :=
  numeric_result compiler 0x8000000000000000 0 0x8000000000000000
    (by decide +kernel) registers flags choices

theorem both_zero (compiler : Compiler) (registers : Register → Word) (flags : Word) (choices : Choices) :
    Returns compiler 0 0 0 registers flags choices :=
  numeric_result compiler 0 0 0 (by decide +kernel) registers flags choices

/-- Clang's two-step budget cannot skip GCC's actual retired ENDBR64. This
checks execution of the complete prefix with arbitrary caller state/choices. -/
theorem gcc_prefix_consumes_step (left right : Word) (registers : Register → Word)
    (flags : Word) (choices : Choices) :
    Sequential.run choices 2 (caller .defaultGCC left right registers flags) =
      .error .exhaustedFuel := by
  obtain ⟨result, actual, observed, _⟩ := executes .defaultGCC _ _
    (admitted .defaultGCC left right registers flags).machine choices
  apply (Sequential.run_sound actual).exhausted
  rw [observed.2.1]
  decide

/-- A graph for the other complete compiler window cannot be accepted. This
tests production decoding/window coverage rather than an assigned graph field. -/
theorem swapped_profiles_rejected :
    CFG.check (bytes .defaultGCC) (graph .defaultClang) = false ∧
    CFG.check (bytes .defaultClang) (graph .defaultGCC) = false := by
  decide +kernel

end EDSL.Tests.CompilerArithmetic

#print axioms EDSL.Arithmetic64.bound_iff
#print axioms EDSL.X86.VCGen.CompilerArithmetic.valid
#print axioms EDSL.X86.VCGen.CompilerArithmetic.generated_vc
#print axioms EDSL.X86.VCGen.CompilerArithmetic.raw_semantics
#print axioms EDSL.X86.VCGen.CompilerArithmetic.observations
#print axioms EDSL.Tests.CompilerArithmetic.current_execution
#print axioms EDSL.Tests.CompilerArithmetic.nonvacuous
#print axioms EDSL.Tests.CompilerArithmetic.numeric_result
#print axioms EDSL.Tests.CompilerArithmetic.gcc_prefix_consumes_step
#print axioms EDSL.Tests.CompilerArithmetic.swapped_profiles_rejected
#audit_edsl
