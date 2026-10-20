/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddBatch64.Frames
import EDSL.OS.FetchAddBatch64.Admission

set_option warningAsError true
set_option autoImplicit false

/-!
A checked instruction family establishes the fixed independent concurrent
contract. Initial admission uses only present ABI arguments and resources;
whole-batch histories, frames, safety and progress are proved consequences.
The contract retains the managed scalar TSO64 and CET-off assumptions. It does
not establish a physical x86-TSO refinement or source-language atomic ordering.
-/

namespace EDSL.OS.FetchAddBatch64
open X86 X86.VCGen.AtomicMethods

/-- One static check suffices for all independently admitted populations,
full64 input words and successful schedules of this exact complete image. -/
theorem checked_claim (image : FetchAddABI64.Image) (padding : List Padding)
    (checked : check image.bytes .rsi LockedAdd64.frozen padding = true) :
    Grading.ConcurrentTask.FetchAdd64.Claim image := by
  apply claim_of_admission image
  intro target cell before deltas pre
  obtain ⟨family⟩ := Admission.admit checked pre
  exact ⟨family.members, family.pre, family.inputs⟩

#print axioms checked_claim
end EDSL.OS.FetchAddBatch64

#audit_edsl
