/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Model

namespace EDSL.OS.MutexTSO
open X86

def blockedCount (observations : List TSO.Observation) : Nat :=
  (observations.filter fun observation => match observation with | .blocked _ => true | _ => false).length

def drainCount (observations : List TSO.Observation) : Nat :=
  (observations.filter fun observation => match observation with | .drained _ _ => true | _ => false).length

def pendingCount (state : Physical) : Nat := (pending state).length

theorem retiredSelections_length (observations : List TSO.Observation) :
    (retiredSelections observations).length = TSO.retiredCount observations := by
  induction observations with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [retiredSelections, TSO.retiredCount] at * <;> omega

theorem retiredSelections_append (first rest : List TSO.Observation) :
    retiredSelections (first ++ rest) = retiredSelections first ++ retiredSelections rest := by
  simp only [retiredSelections, List.filterMap_append]

theorem atomicEvents_append (first rest : List TSO.Observation) :
    TSO.atomicEvents (first ++ rest) = TSO.atomicEvents first ++ TSO.atomicEvents rest := by
  simp only [TSO.atomicEvents, List.filterMap_append]

theorem retiredCount_append (first rest : List TSO.Observation) :
    TSO.retiredCount (first ++ rest) = TSO.retiredCount first + TSO.retiredCount rest := by
  simp only [TSO.retiredCount, List.filter_append, List.length_append]

theorem blockedCount_append (first rest : List TSO.Observation) :
    blockedCount (first ++ rest) = blockedCount first + blockedCount rest := by
  simp only [blockedCount, List.filter_append, List.length_append]

theorem drainCount_append (first rest : List TSO.Observation) :
    drainCount (first ++ rest) = drainCount first + drainCount rest := by
  simp only [drainCount, List.filter_append, List.length_append]

/-- Model actions include storage propagation and blocked issues. They must
not be mistaken for retired machine instructions or hardware elapsed time. -/
theorem observation_partition (observations : List TSO.Observation) :
    observations.length = TSO.retiredCount observations + blockedCount observations + drainCount observations := by
  induction observations with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp [TSO.retiredCount, blockedCount, drainCount] at * <;> omega

theorem schedule_action_count (state : Physical) (actions : List TSO.Action)
    (result : Physical × List TSO.Observation) (success : TSO.schedule state actions = .ok result) :
    actions.length = TSO.retiredCount result.2 + blockedCount result.2 + drainCount result.2 :=
  (TSO.schedule_trace _ _ _ success).length.symm.trans (observation_partition result.2)

end EDSL.OS.MutexTSO
