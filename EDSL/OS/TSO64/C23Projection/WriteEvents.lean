/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.PublishedHistory

/-!
Enumerate every managed publication and RMW from a supplied observation stream.
This reuses the existing write classifier and retains full causes at their
original global positions; equal payloads are never merged. Execution origin
comes from the separate successful-schedule theorem below.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection
open PublishedHistory

/-- All managed writes in observation order, including unchanged-value RMWs.
Nonwriting observations still consume a global action position. -/
def writes (offset : Nat) : List Observation → List Stamp
  | [] => []
  | observation :: rest =>
      match writeOf observation with
      | none => writes (offset + 1) rest
      | some cause => ⟨offset, cause⟩ :: writes (offset + 1) rest

/-- Finite list membership corresponds to the exact original observation and
write cause, without identifying writers by their payload values. -/
theorem mem_writes_iff (offset : Nat) (observations : List Observation) (stamp : Stamp) :
    stamp ∈ writes offset observations ↔
      ∃ index observation, observations[index]? = some observation ∧
        writeOf observation = some stamp.cause ∧ stamp.position = offset + index := by
  induction observations generalizing offset with
  | nil => simp [writes]
  | cons observation rest ih =>
      constructor
      · intro member
        cases written : writeOf observation with
        | none =>
            have tail : stamp ∈ writes (offset + 1) rest := by
              simpa only [writes, written] using member
            obtain ⟨index, actual, found, cause, position⟩ := (ih (offset + 1)).mp tail
            exact ⟨index + 1, actual, found, cause, by omega⟩
        | some cause =>
            have split : stamp = ⟨offset, cause⟩ ∨ stamp ∈ writes (offset + 1) rest := by
              simpa only [writes, written, List.mem_cons] using member
            rcases split with same | tail
            · subst stamp
              exact ⟨0, observation, rfl, written, rfl⟩
            · obtain ⟨index, actual, found, cause, position⟩ := (ih (offset + 1)).mp tail
              exact ⟨index + 1, actual, found, cause, by omega⟩
      · rintro ⟨index, actual, found, cause, position⟩
        cases index with
        | zero =>
            have sameObservation : observation = actual := Option.some.inj found
            subst actual
            have samePosition : stamp.position = offset := by omega
            have sameStamp : stamp = ⟨offset, stamp.cause⟩ := by
              cases stamp
              simp_all
            rw [writes, cause]
            exact List.mem_cons.mpr (.inl sameStamp)
        | succ index =>
            have tailFound : rest[index]? = some actual := found
            have tail := (ih (offset + 1)).mpr
              ⟨index, actual, tailFound, cause, by omega⟩
            cases written : writeOf observation with
            | none => simpa only [writes, written] using tail
            | some head =>
                rw [writes, written]
                exact List.mem_cons_of_mem _ tail

/-- Every retained position lies in the exact supplied global interval. -/
theorem writes_bounds {offset : Nat} {observations : List Observation} {stamp : Stamp}
    (member : stamp ∈ writes offset observations) :
    offset ≤ stamp.position ∧ stamp.position < offset + observations.length := by
  obtain ⟨index, observation, found, _, position⟩ := (mem_writes_iff offset observations stamp).mp member
  have bound := (List.getElem_of_getElem? found).1
  omega

/-- Extracted writes remain strictly ordered by action position, even when
multiple writes have identical causes and values. -/
theorem writes_ordered (offset : Nat) (observations : List Observation) :
    (writes offset observations).Pairwise (fun first second => first.position < second.position) := by
  induction observations generalizing offset with
  | nil => exact .nil
  | cons observation rest ih =>
      cases written : writeOf observation with
      | none => simpa only [writes, written] using ih (offset + 1)
      | some cause =>
          rw [writes, written]
          apply List.pairwise_cons.mpr
          constructor
          · intro stamp member
            have bound := writes_bounds member
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self offset) bound.1
          · exact ih (offset + 1)

/-- One event is retained per selected observation; identical event payloads at
different positions do not collapse into one identity. -/
theorem writes_nodup (offset : Nat) (observations : List Observation) :
    (writes offset observations).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact (writes_ordered offset observations).imp (fun less same => by
    rw [same] at less
    exact (Nat.lt_irrefl _ less))

/-- Every computed write from an actual run carries the real prefix, selected
action and successful step required by the existing publication-history API. -/
theorem writes_origin {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat} {stamp : Stamp}
    (success : schedule state actions profile = .ok result)
    (member : stamp ∈ writes offset result.2) :
    Nonempty (WriteAt state actions result profile offset stamp) := by
  obtain ⟨index, observation, found, written, position⟩ :=
    (mem_writes_iff offset result.2 stamp).mp member
  obtain ⟨before, action, next, prefixRun, selected, stepped⟩ :=
    ScheduleTrace.observation_at success found
  exact ⟨⟨index, observation, before, action, next, position, found, prefixRun,
    selected, stepped, written⟩⟩

/-- The enumeration omits no managed write witnessed in the actual stream. -/
theorem writeAt_mem_writes {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat} {stamp : Stamp}
    (witness : WriteAt state actions result profile offset stamp) :
    stamp ∈ writes offset result.2 :=
  (mem_writes_iff offset result.2 stamp).mpr
    ⟨witness.index, witness.observation, witness.observed, witness.written, witness.position⟩

end EDSL.OS.TSO64.C23Projection
