/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Trace

namespace EDSL.OS.Suspend

def enteredCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .entered _ _ => true | _ => false).length

def resumedCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .resumed _ _ _ => true | _ => false).length

def parkedCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .parked _ _ => true | _ => false).length

def blockedCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .machine (.blocked _) => true | _ => false).length

def drainCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .machine (.drained _ _) => true | _ => false).length

def idleCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .idle => true | _ => false).length

theorem retiredCount_append (first rest : List Observation) :
    retiredCount (first ++ rest) = retiredCount first + retiredCount rest := by
  simp only [retiredCount, List.map_append, List.sum_append]

theorem atomicEvents_append (first rest : List Observation) :
    atomicEvents (first ++ rest) = atomicEvents first ++ atomicEvents rest := by
  simp only [atomicEvents, List.filterMap_append]

theorem enteredCount_append (first rest : List Observation) :
    enteredCount (first ++ rest) = enteredCount first + enteredCount rest := by
  simp only [enteredCount, List.filter_append, List.length_append]

theorem resumedCount_append (first rest : List Observation) :
    resumedCount (first ++ rest) = resumedCount first + resumedCount rest := by
  simp only [resumedCount, List.filter_append, List.length_append]

/-- Entering a call retires its actual SYSCALL once. Returning to userspace,
parked selections, idle, store propagation and locked stalls add no retirement. -/
theorem observation_partition (observations : List Observation) :
    observations.length = retiredCount observations + resumedCount observations + parkedCount observations +
      blockedCount observations + drainCount observations + idleCount observations := by
  induction observations with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | machine actual =>
      cases actual <;> simp [retiredCount, resumedCount, parkedCount, blockedCount, drainCount, idleCount] at * <;> omega
    | entered worker invocation | parked worker invocation | resumed worker invocation raw | idle =>
      simp [retiredCount, resumedCount, parkedCount, blockedCount, drainCount, idleCount] at * <;> omega

theorem schedule_action_count (state : State) (actions : List Action)
    (result : State × List Observation) (success : schedule state actions = .ok result) :
    actions.length = retiredCount result.2 + resumedCount result.2 + parkedCount result.2 +
      blockedCount result.2 + drainCount result.2 + idleCount result.2 :=
  (schedule_trace _ _ _ success).length.symm.trans (observation_partition result.2)

end EDSL.OS.Suspend
