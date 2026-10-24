/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL
import EDSL.Grading.Export.Core
import EDSL.Grading.Runtime.Checker
import Lean.Util.Path

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Export facade with the default installed snapshot. Import
`EDSL.Grading.Export.Core` for snapshot-independent producer functions. -/
namespace EDSLGrader.Export
open Lean

/-- Client executable setup: respect the configured Lean search path, import the
fixed snapshot first, then separately read the locally compiled client module.
No plugins, environment extensions or user source compilation are requested.
This configured client snapshot does not replace the grader's pinned snapshot. -/
def loadEnvironments (moduleName : Name) : IO (Environment × Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL },
      { module := `EDSL.Grading.Known }, { module := `EDSL.Grading.Artifact },
      { module := `EDSL.Grading.CallStack.Artifact },
      { module := `EDSL.Grading.CallMemory64.Artifact },
      { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
      { module := `EDSL.Grading.AtomicLogical64.Artifact },
      { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := moduleName }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted, client)

end EDSLGrader.Export
