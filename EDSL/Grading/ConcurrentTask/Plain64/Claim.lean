/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Completion
import EDSL.Grading.ConcurrentTask.Plain64.History
import EDSL.OS.TSO64.DrainClosure

/-!
The complete independent registered contract for managed plain64 call cohorts.
Every admission field describes present inputs and resources. Successful finite
executions are quantified, while enabledness and a chosen finite completion
must be derived. Empty endpoint queues delimit complete atomic histories;
returned stores need not have published before their actual response.

The own-issue upper bound is a proof output, not a requested precondition,
physical timing bound, minimum-operation theorem or fairness assumption.
A value of this type establishes no exact-file or useful-population certificate
without those separately checked bindings and inhabitants.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open OS.TSO64

structure Claim (catalog : Catalog) : Prop where
  prefixes : ∀ before inputs, Pre catalog before inputs → ∀ actions actual,
    schedule before actions .sharedCell = .ok actual → SafePrefix before actual.1 inputs
  completed : ∀ before inputs, Pre catalog before inputs → ∀ actions actual,
    schedule before actions .sharedCell = .ok actual → Returned actual.1 →
    Nonempty (Post before inputs actions actual)
  whole : ∀ before inputs, ClosedPre catalog before inputs → ∀ actions actual,
    schedule before actions .sharedCell = .ok actual → Finished actual.1 →
    Nonempty (ClosedPost before inputs actions actual 0)
  enabled : ∀ before inputs, Pre catalog before inputs → ∀ actions actual,
    schedule before actions .sharedCell = .ok actual → Enabled actual.1
  completion : ∀ before inputs, Pre catalog before inputs → ∀ prior actual,
    schedule before prior .sharedCell = .ok actual → ∀ choices : Nat → Nat → Bool,
    ∃ suffix finished,
      ChosenIssues choices suffix ∧
      schedule actual.1 suffix .sharedCell = .ok finished ∧ Returned finished.1
  closure : ∀ before inputs, Pre catalog before inputs → ∀ actions actual,
    schedule before actions .sharedCell = .ok actual → Returned actual.1 →
    ∃ closed,
      DrainClosure.drainAll actual.1 .sharedCell = .ok closed ∧
      DrainClosure.Certificate actual.1 closed .sharedCell ∧ Finished closed.1 ∧
      schedule before (actions ++ DrainClosure.actions actual.1) .sharedCell =
        .ok (closed.1, actual.2 ++ closed.2) ∧
      Nonempty (Post before inputs (actions ++ DrainClosure.actions actual.1)
        (closed.1, actual.2 ++ closed.2)) ∧
      (Quiescent before →
        Nonempty (ClosedPost before inputs (actions ++ DrainClosure.actions actual.1)
          (closed.1, actual.2 ++ closed.2) 0))
  bounded : ∃ bound : Nat, 0 < bound ∧
    ∀ before inputs, Pre catalog before inputs → ∀ actions actual,
    schedule before actions .sharedCell = .ok actual → Bounded bound actions actual.1

/-- Restricting the trusted site catalog changes neither present resource
requirements nor any demanded behavioral/safety/history/progress observation. -/
theorem Pre.mono {small large : Catalog} {before : State}
    {inputs : Fin before.workers.length → Input} (pre : Pre small before inputs)
    (subset : ∀ site, site ∈ small → site ∈ large) : Pre large before inputs where
  valid := pre.valid
  selected := fun tid => subset _ (pre.selected tid)
  entry := pre.entry
  privateCallers := pre.privateCallers
  codeCallerSeparation := pre.codeCallerSeparation

/-- A mixed-catalog proof also certifies every registered subcatalog, with
identical full obligations. Homogeneous clients need no repeated machine proof. -/
theorem Claim.mono {small large : Catalog} (claim : Claim large)
    (subset : ∀ site, site ∈ small → site ∈ large) : Claim small where
  prefixes := fun before inputs pre actions actual success =>
    claim.prefixes before inputs (pre.mono subset) actions actual success
  completed := fun before inputs pre actions actual success returned =>
    claim.completed before inputs (pre.mono subset) actions actual success returned
  whole := fun before inputs pre actions actual success finished =>
    claim.whole before inputs ⟨pre.1.mono subset, pre.2⟩ actions actual success finished
  enabled := fun before inputs pre actions actual success =>
    claim.enabled before inputs (pre.mono subset) actions actual success
  completion := fun before inputs pre prior actual success choices =>
    claim.completion before inputs (pre.mono subset) prior actual success choices
  closure := fun before inputs pre actions actual success returned =>
    claim.closure before inputs (pre.mono subset) actions actual success returned
  bounded := by
    obtain ⟨bound, positive, limited⟩ := claim.bounded
    exact ⟨bound, positive, fun before inputs pre actions actual success =>
      limited before inputs (pre.mono subset) actions actual success⟩

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
