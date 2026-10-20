/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Counts

namespace EDSL.OS.MutexTSO
open X86

/-- Instruction retirement advances checked replay. Publication and blocked
issues retain the complete replay state, including guards and loan records. -/
inductive LiftTrace : Logical → List TSO.Action → List TSO.Observation → Logical → Prop where
  | nil {state} : LiftTrace state [] [] state
  | cons {before middle after action observation actions observations}
      (head : Lift before action observation middle)
      (tail : LiftTrace middle actions observations after) :
      LiftTrace before (action :: actions) (observation :: observations) after

/-- The replay schedule and event list are uniquely selected by the actual
physical observations. No schedule or atomic event is guessed by this theorem. -/
theorem LiftTrace.replay {before after : Logical} {actions : List TSO.Action}
    {observations : List TSO.Observation} (trace : LiftTrace before actions observations after) :
    MutexReplay.schedule before (retiredSelections observations) =
      .ok (after, TSO.atomicEvents observations) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | @retired identifier event logicalAfter checked =>
      simp only [retiredSelections, TSO.atomicEvents] at ih
      cases event <;>
        simp [retiredSelections, TSO.atomicEvents, MutexReplay.schedule, checked,
          MutexReplay.recordEvent, ih]
    | blocked => exact ih
    | drained => exact ih

end EDSL.OS.MutexTSO
