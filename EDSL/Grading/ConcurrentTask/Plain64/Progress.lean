/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Admission

/-!
Independent progress observations for a fixed admitted call cohort. Counts are
successful issue actions in the original schedule, including padding and RET;
drains do not count. An issue bound is a property of this restricted modeled
execution, rather than physical timing, fairness or an optimization lower bound.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open OS.TSO64

def issues (tid : Nat) (actions : List Action) : Nat :=
  (actions.filter fun action => match action with
    | .issue thread _ => decide (thread = tid)
    | .drain _ => false).length

/-- Every currently running actual slot can retire an instruction for either
AF choice. Absent or returned workers retain the scheduler's normal faults. -/
def Enabled (state : State) : Prop :=
  ∀ tid worker, state.workers[tid]? = some worker → worker.phase = .running →
    ∀ af, ∃ next, step state (.issue tid af) .sharedCell = .ok next ∧ next.2.retired = 1

/-- An upper bound on successful own issues to return, across any successful
finite interleaving. It does not promise the scheduler will choose these issues. -/
def Bounded (bound : Nat) (actions : List Action) (after : State) : Prop :=
  ∀ tid worker, after.workers[tid]? = some worker → bound ≤ issues tid actions →
    worker.phase = .returned

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
