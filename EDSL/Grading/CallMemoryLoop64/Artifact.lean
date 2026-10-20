/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemoryLoop64
import EDSL.Grading.CallStack.Artifact

set_option warningAsError true

namespace EDSL.Grading.CallMemoryLoop64

/-- Reuse the literal file, whole code window and entry selection format. -/
abbrev Artifact := EDSL.Grading.CallStack.Artifact

namespace Artifact

/-- Successful selection of this exact artifact and the independent full64
counted DATA/resource contract for its selected program. -/
def Claim (artifact : Artifact) : Prop :=
  ∃ selected, EDSL.Grading.CallStack.Artifact.select artifact = .ok selected ∧
    EDSL.CallMemoryLoop64.Claim selected.program

/-- Bind an independent counted proof to the literal file and entry metadata.
ELF selection checks the complete executable, file-backed code window. -/
theorem certify (artifact : Artifact) (program : EDSL.CallMemoryLoop64.Program)
    (selection : EDSL.Grading.CallStack.Artifact.selectedProgram artifact = some program)
    (proof : EDSL.CallMemoryLoop64.Claim program) : Claim artifact := by
  cases result : EDSL.Grading.CallStack.Artifact.select artifact with
  | error error =>
    simp [EDSL.Grading.CallStack.Artifact.selectedProgram, result, Except.toOption] at selection
  | ok selected =>
    have same : selected.program = program := by
      simpa [EDSL.Grading.CallStack.Artifact.selectedProgram, result, Except.toOption] using selection
    exact ⟨selected, result, same.symm ▸ proof⟩

end Artifact
end EDSL.Grading.CallMemoryLoop64
