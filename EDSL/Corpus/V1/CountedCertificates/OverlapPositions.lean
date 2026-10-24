/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterOverlap
import EDSL.OS.TSO64.PositionHistory

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Lift an ordered issuer projection to original full observation indices.
Repeated payloads and actor labels are unrestricted. This is a list theorem;
it does not infer scheduling, target provenance or completion from a pattern.
-/

namespace EDSL.Corpus.V1.CountedCertificates
open OS OS.TSO64

private def issuer? : Observation → Option Nat
  | .rmw tid _ => some tid
  | _ => none

private theorem issuers_eq_filterMap (observations : List Observation) :
    CounterOverlap.issuers observations = observations.filterMap issuer? := by
  induction observations with
  | nil => rfl
  | cons head rest ih => cases head <;> simp_all [CounterOverlap.issuers, issuer?, List.filterMap]

/-- Every RMW is retained, including its actual scheduler tid and multiplicity. -/
theorem occurrences_issuers (observations : List Observation) :
    (PositionHistory.occurrences observations).map PositionHistory.Occurrence.tid =
      CounterOverlap.issuers observations := by
  unfold PositionHistory.occurrences
  rw [List.map_filterMap]
  calc
    _ = observations.zipIdx.filterMap (issuer? ∘ Prod.fst) := by
      congr 1
      funext entry
      rcases entry with ⟨observation, index⟩
      cases observation <;> rfl
    _ = observations.filterMap issuer? := by
      rw [← List.filterMap_map, List.zipIdx_map_fst]
    _ = CounterOverlap.issuers observations := (issuers_eq_filterMap observations).symm

/-- A three-event issuer pattern gives three strictly ordered original
positions, rather than guessed instruction counts or payload-based matches. -/
theorem overlap_positions (observations : List Observation) (own peer : Nat)
    (pattern : CounterOverlap.issuers observations = [own, peer, own]) :
    ∃ first middle last : PositionHistory.Occurrence,
      PositionHistory.occurrences observations = [first, middle, last] ∧
      first.tid = own ∧ middle.tid = peer ∧ last.tid = own ∧
      first.index < middle.index ∧ middle.index < last.index ∧
      last.index < observations.length ∧
      observations[first.index]? = some (.rmw own first.event) ∧
      observations[middle.index]? = some (.rmw peer middle.event) ∧
      observations[last.index]? = some (.rmw own last.event) := by
  have projected : (PositionHistory.occurrences observations).map
      PositionHistory.Occurrence.tid = [own, peer, own] :=
    (occurrences_issuers observations).trans pattern
  obtain ⟨first, rest, firstShape, firstTid, restMap⟩ := List.map_eq_cons_iff.mp projected
  obtain ⟨middle, tail, middleShape, middleTid, tailMap⟩ := List.map_eq_cons_iff.mp restMap
  obtain ⟨last, lastShape, lastTid⟩ := List.map_eq_singleton_iff.mp tailMap
  have shape : PositionHistory.occurrences observations = [first, middle, last] := by
    rw [firstShape, middleShape, lastShape]
  have ordered := PositionHistory.occurrences_chronological observations
  rw [shape] at ordered
  have firstLess : first.index < middle.index :=
    ordered.rel_getElem_of_lt (by simp) (by simp) (by decide : 0 < 1)
  have middleLess : middle.index < last.index :=
    ordered.rel_getElem_of_lt (by simp) (by simp) (by decide : 1 < 2)
  have firstObserved := (PositionHistory.mem_occurrences_iff observations first).mp
    (by rw [shape]; simp)
  have middleObserved := (PositionHistory.mem_occurrences_iff observations middle).mp
    (by rw [shape]; simp)
  have lastObserved := (PositionHistory.mem_occurrences_iff observations last).mp
    (by rw [shape]; simp)
  have lastBound := (List.getElem?_eq_some_iff.mp lastObserved).choose
  refine ⟨first, middle, last, shape, firstTid, middleTid, lastTid,
    firstLess, middleLess, lastBound, ?_, ?_, ?_⟩
  · simpa only [firstTid] using firstObserved
  · simpa only [middleTid] using middleObserved
  · simpa only [lastTid] using lastObserved

#print axioms occurrences_issuers
#print axioms overlap_positions

end EDSL.Corpus.V1.CountedCertificates

#audit_edsl
