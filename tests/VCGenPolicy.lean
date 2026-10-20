/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.GradingExamples
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.VCGenPolicy
open X86 X86.Sequential X86.VCGen OS
open X86.VCGen.GradingExamples

/-- Connect the production execution's actual trace to the protected caller
read. Uniqueness compares executions with the same complete AF stream. -/
private theorem stack_present (minimum : Bool) {input : Comparison64.Input}
    {initial : State}
    (pre : Comparison64.Pre (Examples.bytes (routine minimum)) input initial)
    {choices : Choices} {result : Result} (execution : Executes choices initial result) :
    Examples.stackRead initial ∈ result.reads := by
  have ready : Examples.ReturnReady initial input.returnAddress :=
    ⟨pre.stack, pre.returnCanonical, pre.stackBound, pre.postStackCanonical⟩
  obtain ⟨verified, actual, post, _⟩ := Examples.verifies (routine minimum) initial
    input.returnAddress 0 pre.code ready
    (by cases minimum <;> simp [routine, Examples.DataReady])
    (by cases minimum <;> simp [routine, Examples.OrderReady]) choices
  have same := execution.fixed_choices_unique (Sequential.run_sound actual)
  subst verified
  rw [post.2.2.2.2.2.2.2]
  cases minimum <;> simp [routine, Examples.footprint]

/-- Independent current-domain construction feeds the new bridge. For every
full64 pair, other-register assignment, flags and AF stream, the actual return
has the registered contract and retains the original OS world. Its caller read
has an actual prefix/step origin with current code/slot loans and permission.
The explicit stack-read membership prevents a vacuous empty-trace check. -/
theorem resource_execution_and_origin (minimum : Bool) (left right : Word)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    let bytes := Examples.bytes (routine minimum)
    let resource := Comparison64.Domain.resource bytes left right
    let initial := Comparison64.Domain.initial bytes left right registers flags
    ∃ result, Executes choices initial result ∧
      Comparison64.Post (operation minimum) (Comparison64.resourceInput resource)
        initial result.state ∧ CallResources.Current resource.call resource.shared result.state ∧
      ∃ count before priorReads observation, count < result.instructions ∧
        Block choices initial before count priorReads ∧
        Sequential.step (choices count) before = .ok observation ∧
        Examples.stackRead initial ∈ observation.reads ∧
        CallResources.Current resource.call resource.shared before ∧
        CallResources.ReadAllowed resource.call resource.shared (Examples.stackRead initial) ∧
        OperandReadSucceeds before (Examples.stackRead initial) := by
  dsimp only
  have pre := Comparison64.Domain.resource_pre (Examples.bytes (routine minimum))
    (by cases minimum <;> decide) (by cases minimum <;> decide) left right registers flags
  obtain ⟨executions, policy⟩ := (readOnly_semantics minimum).resource _ _ pre
  obtain ⟨result, execution, post, current⟩ := executions choices
  exact ⟨result, execution, post, current,
    policy.read_origin execution (stack_present minimum pre.machine execution)⟩

/-- A useful independent full64 current input separates min from max. Both
claims would constrain the same production execution to different results. -/
private theorem inconsistent_claims (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (minimum : Grading.Claim .minimum64 bytes)
    (maximum : Grading.Claim .maximum64 bytes) : False := by
  let resource := Comparison64.Domain.resource bytes 0xffffffffffffffff 0x100000000
  let initial := Comparison64.Domain.initial bytes 0xffffffffffffffff 0x100000000
  have pre : Comparison64.ResourcePre bytes resource initial :=
    Comparison64.Domain.resource_pre bytes positive bound 0xffffffffffffffff 0x100000000
  obtain ⟨smaller, smallExecution, smallPost, _⟩ :=
    (minimum.1.resource resource initial pre).1 (fun _ => false)
  obtain ⟨larger, largeExecution, largePost, _⟩ :=
    (maximum.1.resource resource initial pre).1 (fun _ => false)
  have same := Sequential.Executes.fixed_choices_unique smallExecution largeExecution
  subst larger
  have smallContract : Comparison64.Post .unsignedMinimum
      (Comparison64.resourceInput resource) initial smaller.state := smallPost
  have largeContract : Comparison64.Post .unsignedMaximum
      (Comparison64.resourceInput resource) initial smaller.state := largePost
  have smallValue : (smaller.state.registers .rax).toNat = 4294967296 := by
    simpa [Comparison64.MathematicalResult, Comparison64.resourceInput, resource,
      Comparison64.Domain.resource] using smallContract.result
  have largeValue : (smaller.state.registers .rax).toNat = 18446744073709551615 := by
    simpa [Comparison64.MathematicalResult, Comparison64.resourceInput, resource,
      Comparison64.Domain.resource] using largeContract.result
  omega

/-- Swapping the task's mathematical order cannot reuse either byte claim.
This rejects a wrong output contract on a real independently admitted input. -/
theorem swapped_contract_rejected (minimum : Bool) :
    ¬Grading.Claim (taskID (!minimum)) (Examples.bytes (routine minimum)) := by
  cases minimum with
  | false =>
    intro wrong
    exact inconsistent_claims _ (by decide) (by decide) wrong maximum_claim
  | true =>
    intro wrong
    exact inconsistent_claims _ (by decide) (by decide) minimum_claim wrong

/-- Revoke only the original caller-slot loan. Code, cells, permissions,
allocation metadata and all other loans retain their original definitions. -/
private def revokedStack (bytes : List Byte) : Borrowing.State :=
  { Grading.Domain.shared bytes with
    loans := fun identifier => if identifier = 1 then none
      else (Grading.Domain.shared bytes).loans identifier }

/-- Neither the code loan nor the unrelated array loans may authorize the
missing caller read. This checks real authorization and region containment. -/
private theorem revoked_stack_denied (bytes : List Byte) (bound : bytes.length ≤ 4096) :
    ¬CallResources.ReadAllowed (Comparison64.Domain.call bytes) (revokedStack bytes)
      ⟨.stack, 65544, 8⟩ := by
  intro allowed
  obtain ⟨identifier, loan, authorized, inside⟩ := allowed.2.2.2
  by_cases gone : identifier = 1
  · simp [revokedStack, Borrowing.authorize, gone] at authorized
  by_cases small : identifier < 4
  · have same : Grading.Domain.loan bytes identifier = loan := by
      simpa [revokedStack, Borrowing.authorize, Grading.Domain.shared,
        Grading.Domain.loan, Comparison64.Domain.call, Threads.principal, gone, small]
        using authorized
    subst loan
    have alternatives : identifier = 0 ∨ identifier = 2 ∨ identifier = 3 := by omega
    rcases alternatives with rfl | rfl | rfl
    · have upper := inside.2
      change 65552 ≤ 4096 + bytes.length at upper
      omega
    · have lower := inside.1
      change 131072 ≤ 65544 at lower
      omega
    · have lower := inside.1
      change 196608 ≤ 65544 at lower
      omega
  · simp [revokedStack, Borrowing.authorize, Grading.Domain.shared, gone, small] at authorized

/-- Even though the unchanged raw memory really executes and returns, a WP
with the revoked resource permissions cannot pass for ANY postcondition/fuel.
The contradiction uses the new every-prefix bridge and an actual caller-read
origin, rather than assuming that failed resource admission proves a fault. -/
theorem missing_stack_authority (minimum : Bool) (left right : Word)
    (registers : Register → Word) (flags : Word) (fuel : Nat) (Post : Contract) :
    let bytes := Examples.bytes (routine minimum)
    let initial := Comparison64.Domain.initial bytes left right registers flags
    ¬wp (Examples.graph (routine minimum)) initial.rip
      (fun _ read => CallResources.ReadAllowed (Comparison64.Domain.call bytes)
        (revokedStack bytes) read) fuel (Examples.entry (routine minimum)) initial Post := by
  dsimp only
  intro vc
  have pre := Comparison64.Domain.resource_pre (Examples.bytes (routine minimum))
    (by cases minimum <;> decide) (by cases minimum <;> decide) left right registers flags
  have pc : (Comparison64.Domain.initial (Examples.bytes (routine minimum))
      left right registers flags).rip =
      (Comparison64.Domain.initial (Examples.bytes (routine minimum))
        left right registers flags).rip +
      BitVec.ofNat 64 ((Examples.graph (routine minimum)).node
        (Examples.entry (routine minimum))).offset := by simp
  have policy := readOnly_policy_memory (Examples.valid (routine minimum)) pre.machine.code pc vc
  obtain ⟨result, execution, _⟩ := (raw_semantics minimum _ _ pre.machine).1 (fun _ => false)
  obtain ⟨_, _, _, _, _, _, _, _, _, allowed, _⟩ :=
    policy.read_origin execution (stack_present minimum pre.machine execution)
  exact revoked_stack_denied _ (by cases minimum <;> decide) allowed

end EDSL.Tests.VCGenPolicy

#print axioms EDSL.X86.VCGen.block_residual
#print axioms EDSL.X86.VCGen.readOnly_policy
#print axioms EDSL.X86.VCGen.readOnly_policy_memory
#print axioms EDSL.X86.VCGen.GradingExamples.post_contract
#print axioms EDSL.X86.VCGen.GradingExamples.raw_semantics
#print axioms EDSL.X86.VCGen.GradingExamples.readOnly_semantics
#print axioms EDSL.X86.VCGen.GradingExamples.claim
#print axioms EDSL.X86.VCGen.GradingExamples.minimum_claim
#print axioms EDSL.X86.VCGen.GradingExamples.maximum_claim
#print axioms EDSL.Tests.VCGenPolicy.resource_execution_and_origin
#print axioms EDSL.Tests.VCGenPolicy.swapped_contract_rejected
#print axioms EDSL.Tests.VCGenPolicy.missing_stack_authority

#audit_edsl
