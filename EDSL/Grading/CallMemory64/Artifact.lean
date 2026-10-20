/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Artifact
import EDSL.CallMemory64.Admission

set_option warningAsError true

namespace EDSL.Grading.CallMemory64

/-- Reuse the checked literal-file, entry and whole-window selection format. -/
abbrev Artifact := EDSL.Grading.CallStack.Artifact

namespace Artifact

/-- Successful selection of the literal artifact and the independent
CallMemory64 resource and functional contract for that selected program. -/
def Claim (artifact : Artifact) : Prop :=
  ∃ selected, EDSL.Grading.CallStack.Artifact.select artifact = .ok selected ∧
    EDSL.CallMemory64.Claim selected.program

/-- Bind a closed CallMemory64 proof to this exact file and entry metadata.
The selector also checks the complete executable, file-backed ELF window. -/
theorem certify (artifact : Artifact) (program : EDSL.CallMemory64.Program)
    (selection : EDSL.Grading.CallStack.Artifact.selectedProgram artifact = some program)
    (proof : EDSL.CallMemory64.Claim program) : Claim artifact := by
  cases result : EDSL.Grading.CallStack.Artifact.select artifact with
  | error error =>
    simp [EDSL.Grading.CallStack.Artifact.selectedProgram, result, Except.toOption] at selection
  | ok selected =>
    have same : selected.program = program := by
      simpa [EDSL.Grading.CallStack.Artifact.selectedProgram, result, Except.toOption] using selection
    exact ⟨selected, result, same.symm ▸ proof⟩

end Artifact
end EDSL.Grading.CallMemory64
