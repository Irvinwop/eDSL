/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingStoreReturn
open EDSL X86 X86.Sequential Grading

/-- The present domains remain inhabited by useful current-owned inputs even
when the candidate cannot decode. No shape/decoder/future-run gate admits it. -/
theorem unsupported_domain : Nonvacuous (registered .storeReturn32) [0xff] :=
  domain_nonvacuous .storeReturn32 [0xff] (by decide) (by decide)

/-- Truncated FF group code fails actual total execution on the independently
constructed current domain; it is not excluded by the new task's admission. -/
theorem unsupported_not_claim : ¬Claim .storeReturn32 [0xff] := by
  intro claim
  let witness := Write32.Domain.unsupported
  let resource : Write32.Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : Write32.ResourcePre [0xff] resource witness.initial :=
    ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
      witness.raw.targetPointer, rfl, witness.raw.old⟩
  have total := (claim.1.machine (Write32.resourceInput resource) witness.initial pre.machine).1
  have decoded : Sequential.decodeAt witness.initial = .error (.inaccessibleInstruction 4097) :=
    Write32.Domain.unsupported_rejected
  have stepFault : Sequential.step false witness.initial = .error (.inaccessibleInstruction 4097) := by
    simp only [Sequential.step, decoded, error_bind]
  have fault := Sequential.run_fault (choices := fun _ => false) (fuel := 0) stepFault
  have impossible := total.no_fault_prefix (fun _ => false) fault
  cases impossible

/-- The real store/RET implementation satisfies the original void task, but
its returned RAX remains unrelated to the target. A genuine admitted input
and actual successful execution refute the stronger task on the SAME bytes. -/
theorem void_store_not_pointer_claim : ¬Claim .storeReturn32 Write32.bytes := by
  intro claim
  let witness := Write32.Domain.candidate Write32.bytes (by decide) (by decide)
  let resource : Write32.Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : Write32.ResourcePre Write32.bytes resource witness.initial :=
    ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
      witness.raw.targetPointer, rfl, witness.raw.old⟩
  obtain ⟨result, execution, post⟩ :=
    (claim.1.machine (Write32.resourceInput resource) witness.initial pre.machine).1 (fun _ => false)
  have actual : Sequential.Executes (fun _ => false) witness.initial
      ⟨Write32.returned witness.initial (Write32.resourceInput resource).returnAddress,
        2, [⟨.stack, witness.initial.registers .rsp, 8⟩]⟩ := by
    have run := Sequential.Executes.next (choices := fun _ => false)
      (Write32.store_step pre.machine false) (Sequential.Executes.ret (Write32.ret_step pre.machine false))
    simpa only [Result.prepend, List.nil_append] using run
  have same := Sequential.Executes.fixed_choices_unique execution actual
  rw [same] at post
  have wrong := post.pointer
  change (0xfedcba9876543210 : Word) = 262144 at wrong
  exact (by decide : (0xfedcba9876543210 : Word) ≠ 262144) wrong

/-- Registration adds a distinct proven obligation without relabeling the
published void-store proof or silently strengthening its expected result. -/
theorem distinct_task_contracts :
    Claim .write32 Write32.bytes ∧ ¬Claim .storeReturn32 Write32.bytes :=
  ⟨Known.write, void_store_not_pointer_claim⟩

end EDSL.Tests.GradingStoreReturn

#print axioms EDSL.Grading.storeReturn_claim_write
#print axioms EDSL.Grading.storeReturn_semantics
#print axioms EDSL.Grading.Known.storeReturnStoreCopy
#print axioms EDSL.Grading.Known.storeReturnCopyStore
#print axioms EDSL.Grading.Known.storeReturnCopyStoreRax
#print axioms EDSL.Tests.GradingStoreReturn.unsupported_not_claim
#print axioms EDSL.Tests.GradingStoreReturn.void_store_not_pointer_claim
#audit_edsl
