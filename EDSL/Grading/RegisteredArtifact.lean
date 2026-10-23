/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Artifact
import EDSL.Grading.Registry

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.RegisteredArtifact
open X86

/-- Full-artifact admission and the trusted registered contract for exactly the
selected bytes. Selection uses the unchanged raw/ELF parser and window checks. -/
def Claim (id : RegistryID) (artifact : Artifact) : Prop :=
  ∃ selected, Artifact.select artifact = .ok selected ∧ RegisteredClaim id selected.code

/-- The kernel recomputes artifact selection before accepting the registered
contract for the exact selected code bytes. -/
theorem certify (id : RegistryID) (artifact : Artifact) (code : List Byte)
    (selection : Artifact.selectedBytes artifact = some code) (proof : RegisteredClaim id code) :
    Claim id artifact := by
  cases result : Artifact.select artifact with
  | error error => simp [Artifact.selectedBytes, result, Except.toOption] at selection
  | ok selected =>
    have same : selected.code = code := by
      simpa [Artifact.selectedBytes, result, Except.toOption] using selection
    exact ⟨selected, result, same.symm ▸ proof⟩

/-- Additive registration preserves the entire original legacy artifact claim,
including parsing, full selected extent and useful raw/resource domains. -/
theorem legacy_iff (id : TaskID) (artifact : Artifact) :
    Claim (.legacy id) artifact ↔ Artifact.Claim id artifact := by
  constructor
  · rintro ⟨selected, selection, proof⟩
    exact ⟨selected, selection, (registeredClaim_legacy_iff id selected.code).mp proof⟩
  · rintro ⟨selected, selection, proof⟩
    exact ⟨selected, selection, (registeredClaim_legacy_iff id selected.code).mpr proof⟩

end EDSL.Grading.RegisteredArtifact
