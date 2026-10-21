/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Progress
import EDSL.Grading.ConcurrentTask.Plain64.Behavior

/-!
Independent chosen-issue observations for a finite completion suffix.
AF is indexed by each thread's own issue count before that original suffix
action, rather than its global position or the preceding invocation prefix.
This is an output property; no future success or method point enters admission.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open OS.TSO64

/-- Only issue actions, preserving every supplied thread-local AF choice at
its actual original suffix position. Drains are a separate closure phase. -/
def ChosenIssues (choices : Nat → Nat → Bool) (actions : List Action) : Prop :=
  (∀ action ∈ actions, ∃ tid af, action = .issue tid af) ∧
  (∀ index tid af, actions[index]? = some (.issue tid af) →
    af = choices tid (issues tid (actions.take index)))

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
