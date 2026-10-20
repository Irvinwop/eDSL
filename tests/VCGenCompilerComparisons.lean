/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.CompilerComparisons
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.VCGenCompilerComparisons
open X86 X86.Sequential X86.VCGen OS
open X86.VCGen.CompilerComparisons

/-- This integration boundary uses the existing registered tasks, including
both universal raw/current-resource domains and independent useful witnesses. -/
theorem registered (compiler : Compiler) (op : Operation) :
    Grading.Claim (taskID op) (bytes compiler op) := claim compiler op

/-- All full64 arguments, incoming scratch/callee registers, flags and AF
streams pass through the independent domain constructor and real resource
adapter. Exact observations are composed separately from task correctness.
The actual caller-read origin retains the original world and its authority. -/
theorem current_execution (compiler : Compiler) (op : Operation) (left right : Word)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    let candidate := bytes compiler op
    let resource := Comparison64.Domain.resource candidate left right
    let initial := Comparison64.Domain.initial candidate left right registers flags
    ∃ result, Sequential.Executes choices initial result ∧
      Comparison64.Post (operation op) (Comparison64.resourceInput resource) initial result.state ∧
      CallResources.Current resource.call resource.shared result.state ∧
      result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
      ∃ count before priorReads observation, count < result.instructions ∧
        Block choices initial before count priorReads ∧
        Sequential.step (choices count) before = .ok observation ∧
        stackRead initial ∈ observation.reads ∧
        CallResources.Current resource.call resource.shared before ∧
        CallResources.ReadAllowed resource.call resource.shared (stackRead initial) ∧
        OperandReadSucceeds before (stackRead initial) := by
  dsimp only
  have pre := Comparison64.Domain.resource_pre (bytes compiler op)
    (by cases compiler <;> cases op <;> decide)
    (by cases compiler <;> cases op <;> decide) left right registers flags
  obtain ⟨executions,policy⟩ := (readOnly_semantics compiler op).resource _ _ pre
  obtain ⟨result,execution,post,current⟩ := executions choices
  have observed := observations compiler op pre.machine execution
  have present : stackRead (Comparison64.Domain.initial (bytes compiler op)
      left right registers flags) ∈ result.reads := by rw [observed.2]; simp
  exact ⟨result,execution,post,current,observed.1,observed.2,
    policy.read_origin execution present⟩

private def observe (compiler : Compiler) (left right : Word) (af : Bool) :
    Except Error (Word × Word) := do
  let minimum ← Sequential.run (fun _ => af) 5
    (Comparison64.Domain.initial (bytes compiler .minimum) left right)
  let maximum ← Sequential.run (fun _ => af) 5
    (Comparison64.Domain.initial (bytes compiler .maximum) left right)
  return (minimum.state.registers .rax,maximum.state.registers .rax)

/-- Independently specified high-half, signed/unsigned, borrow/wrap, reversed
and equal inputs. Truncating CMP/MOV/CMOV, reversing operands or using signed
flags changes these values. The production decoder and RET really execute. -/
theorem full_width_boundaries (compiler : Compiler) (af : Bool) :
    ([(0x100000001,0xffffffff), (0x8000000000000000,1),
      (0,0xffffffffffffffff), (0xffffffffffffffff,0),
      (0xdeadbeef12345678,0xdeadbeef12345678)] : List (Word × Word)).map
      (fun (left,right) => observe compiler left right af) =
    [.ok (0xffffffff,0x100000001), .ok (1,0x8000000000000000),
      .ok (0,0xffffffffffffffff), .ok (0,0xffffffffffffffff),
      .ok (0xdeadbeef12345678,0xdeadbeef12345678)] := by
  cases compiler <;> cases af <;> rfl

/-- Four steps suffice for Clang but cannot return from the complete GCC
window: ENDBR64 must consume its own retired step before CMP/MOV/CMOV/RET. -/
theorem gcc_needs_prefix_step (op : Operation) (af : Bool) :
    Sequential.run (fun _ => af) 4
      (Comparison64.Domain.initial (bytes .defaultGCC op) 0 1) =
      .error .exhaustedFuel := by
  cases op <;> cases af <;> rfl

private def opposite : Operation → Operation
  | .minimum => .maximum
  | .maximum => .minimum

/-- A useful independently admitted high-half input rules out swapping the
registered minimum/maximum contract. Both claims would constrain the SAME
actual execution to different mathematical values, rather than merely failing
to prove some unsupported program. -/
theorem swapped_contract_rejected (compiler : Compiler) (op : Operation) :
    ¬Grading.Claim (taskID (opposite op)) (bytes compiler op) := by
  intro wrong
  have wrongSemantics : Grading.ReadOnlySemanticClaim
      (Comparison64.readOnlyTask (operation (opposite op))) (bytes compiler op) := by
    cases op <;> exact ((Grading.old_claim_iff _ _).mp wrong).1
  let resource := Comparison64.Domain.resource (bytes compiler op)
    0xffffffffffffffff 0x100000000
  let initial := Comparison64.Domain.initial (bytes compiler op)
    0xffffffffffffffff 0x100000000
  have pre : Comparison64.ResourcePre (bytes compiler op) resource initial :=
    Comparison64.Domain.resource_pre _
      (by cases compiler <;> cases op <;> decide)
      (by cases compiler <;> cases op <;> decide) 0xffffffffffffffff 0x100000000
  obtain ⟨correct,actual,post⟩ := (raw_semantics compiler op _ _ pre.machine).1 (fun _ => false)
  obtain ⟨incorrect,claimed,wrongPost⟩ :=
    (wrongSemantics.machine _ _ pre.machine).1 (fun _ => false)
  have same := Sequential.Executes.fixed_choices_unique actual claimed
  subst incorrect
  have correctValue := post.result
  have wrongValue := wrongPost.result
  cases op <;>
    simp [operation,opposite,Comparison64.MathematicalResult,
      Comparison64.resourceInput,resource,Comparison64.Domain.resource]
      at correctValue wrongValue <;> omega

/-- Missing caller authority is checked against the real OS permission
predicate, without replacing the ISA evaluator or assuming future execution.
This reuses the existing policy bridge; exact trace membership prevents an
empty-read proof from passing. The alternative world may retain arbitrary
unrelated loans, but must lack authorization for this original caller slot. -/
theorem missing_caller_authority (compiler : Compiler) (op : Operation)
    {resource : Comparison64.Resources} {initial : State}
    (pre : Comparison64.ResourcePre (bytes compiler op) resource initial)
    (withoutCaller : Borrowing.State)
    (missing : ¬CallResources.ReadAllowed resource.call withoutCaller (stackRead initial))
    (fuel : Nat) (Postcondition : Contract) :
    ¬wp (graph compiler op) initial.rip
      (fun _ read => CallResources.ReadAllowed resource.call withoutCaller read)
      fuel (entry compiler op) initial Postcondition := by
  intro vc
  let choices : Choices := fun _ => false
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((graph compiler op).node (entry compiler op)).offset := by simp
  obtain ⟨result,execution,_,_,trace⟩ :=
    X86.VCGen.sound (valid compiler op) pre.machine.code pc vc choices
  have observed := observations compiler op pre.machine execution
  have present : stackRead initial ∈ result.reads := by rw [observed.2]; simp
  obtain ⟨_,_,_,_,_,_,_,_,allowed,_⟩ := trace.read_origin present
  exact missing allowed

end EDSL.Tests.VCGenCompilerComparisons

#print axioms EDSL.X86.VCGen.CompilerComparisons.valid
#print axioms EDSL.X86.VCGen.CompilerComparisons.generated_vc
#print axioms EDSL.X86.VCGen.CompilerComparisons.verifies
#print axioms EDSL.X86.VCGen.CompilerComparisons.observations
#print axioms EDSL.X86.VCGen.CompilerComparisons.raw_semantics
#print axioms EDSL.X86.VCGen.CompilerComparisons.readOnly_semantics
#print axioms EDSL.X86.VCGen.CompilerComparisons.claim
#print axioms EDSL.Tests.VCGenCompilerComparisons.registered
#print axioms EDSL.Tests.VCGenCompilerComparisons.current_execution
#print axioms EDSL.Tests.VCGenCompilerComparisons.full_width_boundaries
#print axioms EDSL.Tests.VCGenCompilerComparisons.gcc_needs_prefix_step
#print axioms EDSL.Tests.VCGenCompilerComparisons.swapped_contract_rejected
#print axioms EDSL.Tests.VCGenCompilerComparisons.missing_caller_authority

#audit_edsl
