/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64Contract
open EDSL.CallMemory64 X86

def unsupported : Program := ⟨[0xff], 0⟩

/-- The useful domain remains inhabited even for a truncated FF group instruction. -/
theorem unsupported_admitted : Nonvacuous unsupported :=
  domain_nonvacuous unsupported (by decide) (by decide)

/-- Present resources cannot turn decoder rejection into a certified execution.
This checks the real initialized RAM and the fixed universal claim together. -/
theorem unsupported_not_semantic : ¬SemanticClaim unsupported := by
  intro claim
  have pre := Domain.resource_pre unsupported (by decide) (by decide) 1 0
  obtain ⟨_, _, covered, _⟩ := claim _ _ pre (fun _ => false)
  obtain ⟨_, instruction, _, decoded, _⟩ := covered.fetchWithin
  have rejected : CallReturn.decodeAt (Domain.initial unsupported 1 0) =
      .error (.inaccessibleInstruction 4097) := rfl
  rw [rejected] at decoded
  cases decoded

theorem unsupported_not_claim : ¬Claim unsupported :=
  fun claim => unsupported_not_semantic claim.1

end EDSL.Tests.CallMemory64Contract

#print axioms EDSL.CallMemory64.domain_nonvacuous
#print axioms EDSL.CallMemory64.SemanticClaim.run
#print axioms EDSL.CallMemory64.SemanticClaim.all_results
#print axioms EDSL.CallMemory64.Returned.target_read
#print axioms EDSL.Tests.CallMemory64Contract.unsupported_not_claim
#audit_edsl
