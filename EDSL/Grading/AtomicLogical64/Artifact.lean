/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Contract
import EDSL.Grading.AtomicLogical64.Domain
import EDSL.Grading.Artifact

namespace EDSL.Grading.AtomicLogical64

/-- The existing complete-file, entry-zero executable-window format. The
selected byte limit is an IO protocol bound, not a semantic solution shape. -/
abbrev Artifact := EDSL.Grading.Artifact

namespace Artifact

/-- Bind the complete literal artifact and successful selection to the fixed
current-resource atomic union contract. Other executable bytes outside the
selected window are not claimed to execute or form a complete process. -/
def Claim (artifact : Artifact) : Prop :=
  ∃ selected, EDSL.Grading.Artifact.select artifact = .ok selected ∧
    AtomicLogical64.Claim selected.code

/-- The checked wrapper redoes selection of this exact raw/full-ELF artifact;
it never substitutes a displayed hash or a host-selected byte list. -/
theorem certify (artifact : Artifact) (code : List X86.Byte)
    (selection : EDSL.Grading.Artifact.selectedBytes artifact = some code)
    (proof : AtomicLogical64.Claim code) : Claim artifact := by
  cases result : EDSL.Grading.Artifact.select artifact with
  | error error =>
    simp [EDSL.Grading.Artifact.selectedBytes, result, Except.toOption] at selection
  | ok selected =>
    have same : selected.code = code := by
      simpa [EDSL.Grading.Artifact.selectedBytes, result, Except.toOption] using selection
    exact ⟨selected, result, same.symm ▸ proof⟩

end Artifact
end EDSL.Grading.AtomicLogical64
