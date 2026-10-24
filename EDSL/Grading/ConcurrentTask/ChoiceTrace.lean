/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.ChoiceTrace
import EDSL.Grading.ConcurrentTask.Plain64.Completion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
The shared zero-offset choice contract is exactly the existing Plain64 output
property, using its original issue counter and leaving that predicate intact.
The OS choice-accounting module has no dependency on grading.
-/

namespace EDSL.Grading.ConcurrentTask.ChoiceTrace
open OS.TSO64

theorem issues_eq_plain64 (tid : Nat) (actions : List Action) :
    OS.TSO64.EffectSimulation.Mixed.ChoiceTrace.issues tid actions =
      Plain64.issues tid actions := rfl

theorem chosenIssues_iff_plain64 (choices : Nat → Nat → Bool) (actions : List Action) :
    OS.TSO64.EffectSimulation.Mixed.ChoiceTrace.ChosenIssues choices actions ↔
      Plain64.ChosenIssues choices actions := by
  simp only [OS.TSO64.EffectSimulation.Mixed.ChoiceTrace.ChosenIssues,
    OS.TSO64.EffectSimulation.Mixed.ChoiceTrace.ChosenFrom, Plain64.ChosenIssues,
    Nat.zero_add, issues_eq_plain64]

#print axioms issues_eq_plain64
#print axioms chosenIssues_iff_plain64

end EDSL.Grading.ConcurrentTask.ChoiceTrace

#audit_edsl
