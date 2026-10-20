/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Contract
import EDSL.Grading.Artifact

namespace EDSL.Grading.AtomicSet64

/-- Reuse complete literal-file selection and the explicit executable window.
The selected-byte limit is a protocol bound, not a semantic solution shape. -/
abbrev Artifact := EDSL.Grading.Artifact

namespace Artifact

/-- Bind the exact raw/full-ELF artifact to the independently requested set
operation's uninterrupted callable contract. The proposition retains its literal
artifact parameter even when selection ignores nonloaded metadata. Actual event
tags need not be homogeneous. No other container code is claimed to execute. -/
structure Claim (desired : Logical64.Operation) (artifact : Artifact) : Prop where
  evidence : ∃ selected, EDSL.Grading.Artifact.select artifact = .ok selected ∧
    AtomicSet64.Claim desired selected.code

/-- Kernel checking redoes selection for this literal artifact, including the
complete ELF file and explicit span; a displayed hash has no proof authority. -/
theorem certify (desired : Logical64.Operation) (artifact : Artifact)
    (code : List X86.Byte)
    (selection : EDSL.Grading.Artifact.selectedBytes artifact = some code)
    (proof : AtomicSet64.Claim desired code) : Claim desired artifact := by
  cases result : EDSL.Grading.Artifact.select artifact with
  | error error =>
    simp [EDSL.Grading.Artifact.selectedBytes, result, Except.toOption] at selection
  | ok selected =>
    have same : selected.code = code := by
      simpa [EDSL.Grading.Artifact.selectedBytes, result, Except.toOption] using selection
    exact ⟨⟨selected, result, same.symm ▸ proof⟩⟩

end Artifact
end EDSL.Grading.AtomicSet64
