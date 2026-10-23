/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export
import EDSL.Grading.RegisteredArtifact

set_option autoImplicit false
set_option warningAsError true

namespace EDSLGrader.Export
open Lean

/-- Client-side export against the same fixed registered-task snapshot used by
`trustedRegistryEnvironment`. Only the separate client environment imports the
requested local module. Neither environment supplies the grader's expected
contract, and the grader independently reconstructs all packet declarations. -/
def loadRegisteredEnvironments (moduleName : Name) : IO (Environment × Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL },
      { module := `EDSL.Grading.Known }, { module := `EDSL.Grading.Artifact },
      { module := `EDSL.Grading.CallStack.Artifact },
      { module := `EDSL.Grading.CallMemory64.Artifact },
      { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
      { module := `EDSL.Grading.AtomicLogical64.Artifact },
      { module := `EDSL.Grading.AtomicSet64.Artifact },
      { module := `EDSL.Grading.RegisteredArtifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := moduleName }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted, client)

end EDSLGrader.Export
