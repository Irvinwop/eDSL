/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.CompilerClamp32
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CompilerClamp32
open X86 X86.Sequential X86.VCGen OS
open X86.VCGen.CompilerComparisons (Compiler)
open X86.VCGen.CompilerClamp32

/- Reuse the existing ordinary-RAM/code/caller-loan fixture. These definitions
only install ABI registers and inputs; they do not interpret code or define a
new per-program Domain. The shared fixture returns to 8192 from slot 65544. -/
private def values (value lower upper : Word) : Scalar32.ClampInput :=
  ⟨value.setWidth 32, lower.setWidth 32, upper.setWidth 32⟩

private def input (value lower upper : Word) : PureCall.Invocation Scalar32.clampSigned :=
  ⟨values value lower upper, 8192⟩

private def resource (compiler : Compiler) (value lower upper : Word) :
    PureCall.Resources Scalar32.clampSigned :=
  ⟨Grading.Domain.shared (bytes compiler), Comparison64.Domain.call (bytes compiler),
    values value lower upper⟩

private def caller (compiler : Compiler) (value lower upper : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State where
  registers register := match register with
    | .rdi => value
    | .rsi => lower
    | .rdx => upper
    | .rsp => 65544
    | _ => registers register
  rip := 4096
  flags := flags
  memory := AddressSpace.toMemory (Grading.Domain.space (bytes compiler))

private theorem admitted (compiler : Compiler) (value lower upper : Word)
    (ordered : (lower.setWidth 32).toInt ≤ (upper.setWidth 32).toInt)
    (registers : Register → Word) (flags : Word) :
    PureCall.ResourcePre Scalar32.clampSigned (bytes compiler) (resource compiler value lower upper)
      (caller compiler value lower upper registers flags) := by
  refine ⟨⟨Comparison64.Domain.contract (bytes compiler)
    (by cases compiler <;> decide) (by cases compiler <;> decide), rfl⟩,
    rfl, rfl, rfl, ordered, ?_⟩
  exact (Scalar32.clamp_bound_iff _ _).mpr ⟨rfl, rfl, rfl⟩

/-- All full64 argument registers are admitted using only their signed low32
order. Upper halves, scratch/callee registers, flags and AF streams are free.
The independent PureCall postcondition checks signed mathematics, complete
RAM/permissions, actual return, SysV callee saves and nonarithmetic flags. The
actual caller-read origin also retains the original OS world and authority. -/
theorem current_execution (compiler : Compiler) (value lower upper : Word)
    (ordered : (lower.setWidth 32).toInt ≤ (upper.setWidth 32).toInt)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    let resource := resource compiler value lower upper
    let initial := caller compiler value lower upper registers flags
    ∃ result, Sequential.Executes choices initial result ∧
      PureCall.Post Scalar32.clampSigned (PureCall.resourceInput resource) initial result.state ∧
      CallResources.Current resource.call resource.shared result.state ∧
      result.instructions = (match compiler with | .defaultGCC => 7 | .defaultClang => 6) ∧
      result.reads = [⟨.stack, 65544, 8⟩] ∧ (result.state.registers .rax).toNat < 2^32 ∧
      Grading.ReadOnlyPolicy initial (CallResources.Current resource.call resource.shared)
        (fun _ => CallResources.ReadAllowed resource.call resource.shared) ∧
      ∃ count before priorReads observation, count < result.instructions ∧
        Block choices initial before count priorReads ∧
        Sequential.step (choices count) before = .ok observation ∧
        (⟨.stack, 65544, 8⟩ : Read) ∈ observation.reads ∧
        CallResources.Current resource.call resource.shared before ∧
        CallResources.ReadAllowed resource.call resource.shared ⟨.stack, 65544, 8⟩ ∧
        OperandReadSucceeds before ⟨.stack, 65544, 8⟩ := by
  dsimp only
  have pre := admitted compiler value lower upper ordered registers flags
  obtain ⟨executions, policy⟩ := (raw_semantics compiler).resource _ _ pre
  obtain ⟨result, execution, post, current⟩ := executions choices
  have observed := observations compiler pre.machine execution
  have present : stackRead (caller compiler value lower upper registers flags) ∈ result.reads := by
    rw [observed.2.1]
    simp
  exact ⟨result, execution, post, current, observed.1, observed.2.1, observed.2.2,
    policy, policy.read_origin execution present⟩

private theorem numeric_result (compiler : Compiler) (value lower upper : Word)
    (expected : BitVec 32)
    (ordered : (lower.setWidth 32).toInt ≤ (upper.setWidth 32).toInt)
    (mathematics : Scalar32.Clamped (value.setWidth 32).toInt (lower.setWidth 32).toInt
      (upper.setWidth 32).toInt expected.toInt)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler)
        (caller compiler value lower upper registers flags) = .ok result ∧
      result.state.registers .rax = expected.setWidth 64 ∧
      result.state.rip = 8192 ∧ result.state.registers .rsp = 65552 := by
  have pre := (admitted compiler value lower upper ordered registers flags).machine
  obtain ⟨result, actual, observed, _⟩ := executes compiler (input value lower upper)
    (caller compiler value lower upper registers flags) pre choices
  have signedEq := Scalar32.clamped_unique observed.1.result mathematics
  have lowEq : (result.state.registers .rax).setWidth 32 = expected :=
    BitVec.toInt_inj.mp signedEq
  refine ⟨result, actual, ?_, observed.1.returnAddress, observed.1.stackPointer⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt observed.2.2.2] using
    congrArg BitVec.toNat lowEq

/-- A signed-overflow boundary, with all three upper argument halves arbitrary.
The explicitly typed conclusion requires the independent literal -1 result;
it cannot silently change with the numeric helper's inferred return type. -/
theorem signed_minimum_high_halves (compiler : Compiler) (value lower upper : Word)
    (valueLow : value.setWidth 32 = 0x80000000)
    (lowerLow : lower.setWidth 32 = 0xffffffff)
    (upperLow : upper.setWidth 32 = 1)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler)
        (caller compiler value lower upper registers flags) = .ok result ∧
      result.state.registers .rax = 0xffffffff ∧
      result.state.rip = 8192 ∧ result.state.registers .rsp = 65552 := by
  exact numeric_result compiler value lower upper 0xffffffff
    (by rw [lowerLow, upperLow]; decide +kernel)
    (by rw [valueLow, lowerLow, upperLow]; unfold Scalar32.Clamped; decide +kernel)
    registers flags choices

/-- Equal signed endpoints are admitted, including INT32_MIN/MAX. Their high
halves may differ, and the value may be any full64 word. The expected full RAX
is the mathematical endpoint zero-extended from 32 bits. -/
theorem equal_endpoints (compiler : Compiler) (value lower upper : Word)
    (same : lower.setWidth 32 = upper.setWidth 32)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler)
        (caller compiler value lower upper registers flags) = .ok result ∧
      result.state.registers .rax = (lower.setWidth 32).setWidth 64 ∧
      result.state.rip = 8192 ∧ result.state.registers .rsp = 65552 := by
  apply numeric_result compiler value lower upper (lower.setWidth 32) ?_ ?_ registers flags choices
  · simpa only [← same] using (Int.le_refl (lower.setWidth 32).toInt)
  · rw [← same]
    unfold Scalar32.Clamped
    omega

private def observe (compiler : Compiler) (value lower upper : Word) (choices : Choices) :
    Except Error (Word × Nat × Word × Word) :=
  (Sequential.run choices 7 (caller compiler value lower upper)).map fun result =>
    (result.state.registers .rax, result.instructions, result.state.rip, result.state.registers .rsp)

/-- Actual decoding and execution, with independent signed boundary vectors,
unrelated upper halves and nonzero incoming RAX. Checking the complete RAX
catches full64 source transfer or sign-extension instead of r32 writeback;
the literal counts/continuation/RSP require the real RET and GCC ENDBR64. -/
theorem decoded_signed_boundaries (compiler : Compiler) (choices : Choices) :
    let count := match compiler with | .defaultGCC => 7 | .defaultClang => 6
    ([(0xaabbccdd80000000, 0x55667788ffffffff, 0xdeadbeef00000001),
      (0x112233447fffffff, 0x88776655ffffffff, 0xa5a5a5a500000001),
      (0xf0e1d2c380000000, 0x0123456780000000, 0xfedcba987fffffff),
      (0x111122227fffffff, 0xaabbccdd80000000, 0x012345677fffffff),
      (0x9abcdef0ffffffff, 0x8765432180000000, 0x123456787fffffff),
      (0x1234567800000000, 0xabcdef01ffffffff, 0x1010101000000001)] :
        List (Word × Word × Word)).map (fun (value, lower, upper) =>
          observe compiler value lower upper choices) =
    [.ok (0xffffffff, count, 8192, 65552), .ok (1, count, 8192, 65552),
      .ok (0x80000000, count, 8192, 65552), .ok (0x7fffffff, count, 8192, 65552),
      .ok (0xffffffff, count, 8192, 65552), .ok (0, count, 8192, 65552)] := by
  cases compiler <;> rfl

/-- Equal endpoints with different high halves and values on either side,
including both extreme signed endpoints, through the real decoded executor. -/
theorem decoded_equal_endpoints (compiler : Compiler) (choices : Choices) :
    let count := match compiler with | .defaultGCC => 7 | .defaultClang => 6
    ([(0xabcdef0180000000, 0x111111110000002a, 0xeeeeeeee0000002a),
      (0x123456787fffffff, 0xaaaaaaaa80000000, 0xbbbbbbbb80000000),
      (0xfedcba9800000000, 0x010203047fffffff, 0x556677887fffffff)] :
        List (Word × Word × Word)).map (fun (value, lower, upper) =>
          observe compiler value lower upper choices) =
    [.ok (42, count, 8192, 65552), .ok (0x80000000, count, 8192, 65552),
      .ok (0x7fffffff, count, 8192, 65552)] := by
  cases compiler <;> rfl

/-- The first GCC CMOV writes RDX, which retains a high argument half unless
the r32 writeback zero-extends even when false. RAX's earlier MOV32 alone cannot
detect that defect. Observe RDX after the full decoded function for both
outcomes, with independent literal expected values and the actual RET. -/
theorem gcc_cmov32_both_outcomes_zero_extend (choices : Choices) :
    ((Sequential.run choices 7 (caller .defaultGCC
        0x1111111100000002 0x2222222200000000 0xdeadbeef00000001)).map
        (fun result => (result.state.registers .rdx, result.state.registers .rax)),
      (Sequential.run choices 7 (caller .defaultGCC
        0x33333333ffffffff 0x44444444fffffffe 0xdeadbeef00000001)).map
        (fun result => (result.state.registers .rdx, result.state.registers .rax))) =
    (.ok (1, 1), .ok (0xffffffff, 0xffffffff)) := by rfl

/-- A signed-to-unsigned condition mutation must invalidate the original
certificate. This catches a checker that ignores the decoded CMOV condition. -/
theorem unsigned_condition_rejected :
    (CFG.check ((bytes .defaultGCC).set 9 0x46) (graph .defaultGCC),
      CFG.check ((bytes .defaultClang).set 5 0x42) (graph .defaultClang)) =
    (false, false) := by decide +kernel

/-- A certificate for the frozen window cannot silently certify an additional
unmodeled suffix byte; CFG admission must cover the complete selected window. -/
theorem trailing_byte_rejected (compiler : Compiler) :
    CFG.check (bytes compiler ++ [0x90]) (graph compiler) = false := by
  cases compiler <;> decide +kernel

/-- The observed RET read prevents a vacuous empty-read permission proof.
Removing the original caller authority rules out a generated WP for any fuel
and any postcondition, without changing the executor or assuming a future run. -/
theorem missing_caller_authority (compiler : Compiler)
    {resource : PureCall.Resources Scalar32.clampSigned} {initial : State}
    (pre : PureCall.ResourcePre Scalar32.clampSigned (bytes compiler) resource initial)
    (withoutCaller : Borrowing.State)
    (missing : ¬CallResources.ReadAllowed resource.call withoutCaller
      ⟨.stack, initial.registers .rsp, 8⟩)
    (fuel : Nat) (Postcondition : Contract) :
    ¬wp (graph compiler) initial.rip
      (fun _ read => CallResources.ReadAllowed resource.call withoutCaller read)
      fuel (entry compiler) initial Postcondition := by
  intro vc
  let choices : Choices := fun _ => false
  obtain ⟨result, execution, _, _, trace⟩ :=
    X86.VCGen.sound (valid compiler) pre.machine.code (by simp) vc choices
  have observed := observations compiler pre.machine execution
  have present : stackRead initial ∈ result.reads := by rw [observed.2.1]; simp
  obtain ⟨_, _, _, _, _, _, _, _, allowed, _⟩ := trace.read_origin present
  exact missing allowed

end EDSL.Tests.CompilerClamp32

#print axioms EDSL.X86.VCGen.CompilerClamp32.checked
#print axioms EDSL.X86.VCGen.CompilerClamp32.valid
#print axioms EDSL.X86.VCGen.CompilerClamp32.generated_vc
#print axioms EDSL.X86.VCGen.CompilerClamp32.raw_semantics
#print axioms EDSL.X86.VCGen.CompilerClamp32.executes
#print axioms EDSL.X86.VCGen.CompilerClamp32.observations
#print axioms EDSL.Tests.CompilerClamp32.current_execution
#print axioms EDSL.Tests.CompilerClamp32.signed_minimum_high_halves
#print axioms EDSL.Tests.CompilerClamp32.equal_endpoints
#print axioms EDSL.Tests.CompilerClamp32.decoded_signed_boundaries
#print axioms EDSL.Tests.CompilerClamp32.decoded_equal_endpoints
#print axioms EDSL.Tests.CompilerClamp32.gcc_cmov32_both_outcomes_zero_extend
#print axioms EDSL.Tests.CompilerClamp32.unsigned_condition_rejected
#print axioms EDSL.Tests.CompilerClamp32.trailing_byte_rejected
#print axioms EDSL.Tests.CompilerClamp32.missing_caller_authority

#audit_edsl
