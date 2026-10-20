/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

/-- A client importing the reusable API must not accidentally load frozen ELF
literals, historical programs or task registrations. This catches transitive
import regressions, which a grep of the umbrella alone cannot detect. -/
elab "#check_verification_import_boundary" : command => do
  let environment ← Lean.getEnv
  let forbidden := #[`EDSL.Corpus, `EDSL.Examples,
    `EDSL.X86.VCGen.Examples, `EDSL.X86.VCGen.GradingExamples]
  let registrations := #[`EDSL.Grading.Task, `EDSL.Grading.ReadOnlyTask]
  for name in environment.header.moduleNames do
    if forbidden.any (fun family => family.isPrefixOf name) then
      throwError "Reusable EDSL import unexpectedly includes program module {name}"
    if registrations.contains name then
      throwError "Reusable EDSL import unexpectedly includes task registrations {name}"
  let projectModules := environment.header.moduleNames.filter ((`EDSL).isPrefixOf ·)
  Lean.logInfo m!"Reusable EDSL imports {projectModules.size} project modules; no corpus, examples or registrations"

#check_verification_import_boundary
#audit_edsl
