/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL
import Lean

/- Audit every public project declaration and its transitive dependencies.
The allowed axioms are Lean's standard logical axioms, not OS/compiler claims. -/
run_cmd do
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut count : Nat := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`EDSL).isPrefixOf name then
      count := count + 1
      for dependency in ← Lean.collectAxioms name do
        unless allowed.contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
  if count == 0 then
    throwError "No EDSL declarations were audited"
  Lean.logInfo m!"Audited {count} EDSL declarations; no unapproved axioms"
