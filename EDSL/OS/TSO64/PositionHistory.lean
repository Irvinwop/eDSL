/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.ModuloCounter.Relabel
import EDSL.OS.TSO64History

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Position-aware projections of actual arithmetic RMW observations.

All list projections retain every RMW, its scheduler tid and its index in the
entire observation list. No actor interpretation or payload uniqueness is used.
The conservation wrapper reuses the existing owned-only schedule theorem for
either existing instruction family. Its explicit target-coverage hypothesis
cannot be replaced by a selected-event count.

This inherits that theorem's current-resource, coherent scalar ordinary RAM,
stable-translation/no-hidden-alias and represented CPU assumptions. It adds no
native, physical LOCK, ABI, invocation/RET, refinement or progress guarantee.
-/

namespace EDSL.OS.TSO64.PositionHistory
open X86 Concurrency

/-- An occurrence keeps the entire original event, including its separate
actor, handle, cell and arithmetic payload. The index counts silent labels too. -/
structure Occurrence where
  index : Nat
  tid : Nat
  event : Atomics64.FetchAddEvent

private def occurrence? (entry : Observation × Nat) : Option Occurrence :=
  match entry.1 with
  | .rmw tid event => some ⟨entry.2, tid, event⟩
  | _ => none

def occurrences (observations : List Observation) : List Occurrence :=
  observations.zipIdx.filterMap occurrence?

def Occurrence.asCall (occurrence : Occurrence) : ModuloCounter.Call 64 Nat Nat :=
  AtomicFetchAddHistory64.asCall occurrence.index occurrence.tid occurrence.event

/-- Same unfiltered definition as the independent Counted64 specification.
Indices come from the complete list before any non-RMW labels are removed. -/
def incrementCalls (observations : List Observation) : List (ModuloCounter.Call 64 Nat Nat) :=
  observations.zipIdx.filterMap fun entry =>
    match entry.1 with
    | .rmw tid event => some (AtomicFetchAddHistory64.asCall entry.2 tid event)
    | _ => none

theorem incrementCalls_eq_map (observations : List Observation) :
    incrementCalls observations = (occurrences observations).map Occurrence.asCall := by
  unfold incrementCalls occurrences
  rw [List.map_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨observation, index⟩
  cases observation <;> rfl

/-- Exact lookup in both directions, without assumptions about target, actor,
delta, repeated payloads, or successful scheduling. -/
theorem mem_occurrences_iff (observations : List Observation) (occurrence : Occurrence) :
    occurrence ∈ occurrences observations ↔
      observations[occurrence.index]? = some (.rmw occurrence.tid occurrence.event) := by
  unfold occurrences
  constructor
  · intro member
    obtain ⟨⟨observation, index⟩, indexed, extracted⟩ := List.mem_filterMap.mp member
    have observed := List.mem_zipIdx_iff_getElem?.mp indexed
    cases observation <;>
      simp only [occurrence?, Option.some.injEq, reduceCtorEq] at extracted
    case rmw tid event =>
      subst occurrence
      exact observed
  · intro observed
    apply List.mem_filterMap.mpr
    refine ⟨(.rmw occurrence.tid occurrence.event, occurrence.index),
      List.mem_zipIdx_iff_getElem?.mpr observed, ?_⟩
    cases occurrence
    rfl

/-- Erasure recovers the complete chronological native event list, not merely
a set or a target-filtered sublist. Thus multiplicity and order are preserved. -/
theorem occurrences_events (observations : List Observation) :
    (occurrences observations).map Occurrence.event =
      observations.filterMap TSO64History.label := by
  unfold occurrences
  rw [List.map_filterMap]
  have same : (fun entry => (occurrence? entry).map Occurrence.event) =
      TSO64History.label ∘ Prod.fst := by
    funext entry
    rcases entry with ⟨observation, index⟩
    cases observation <;> rfl
  rw [same, ← List.filterMap_map, List.zipIdx_map_fst]

theorem occurrences_chronological (observations : List Observation) :
    (occurrences observations).Pairwise (fun left right => left.index < right.index) := by
  have ordered : observations.zipIdx.Pairwise (fun left right => left.2 < right.2) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj less
    simpa using less
  unfold occurrences
  apply List.Pairwise.filterMap occurrence? ?_ ordered
  intro left right less first extractedFirst second extractedSecond
  rcases left with ⟨leftObservation, leftIndex⟩
  cases leftObservation <;>
    simp only [occurrence?, Option.some.injEq, reduceCtorEq] at extractedFirst
  case rmw leftTid leftEvent =>
    subst first
    rcases right with ⟨rightObservation, rightIndex⟩
    cases rightObservation <;>
      simp only [occurrence?, Option.some.injEq, reduceCtorEq] at extractedSecond
    case rmw rightTid rightEvent =>
      subst second
      exact less

theorem incrementCalls_chronological (observations : List Observation) :
    (incrementCalls observations).Pairwise (fun left right => left.id < right.id) := by
  rw [incrementCalls_eq_map, List.pairwise_map]
  exact occurrences_chronological observations

theorem incrementCalls_distinct (observations : List Observation) :
    ((incrementCalls observations).map (fun call => call.id)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (incrementCalls_chronological observations).imp (fun less => Nat.ne_of_lt less)

/-- Total occurrence count requires no selected-target or unit-delta premise.
In particular foreign-cell and non-unit events are still counted. -/
theorem incrementCalls_length (observations : List Observation) :
    (incrementCalls observations).length =
      (observations.filterMap TSO64History.label).length := by
  have same := congrArg List.length (occurrences_events observations)
  simpa only [incrementCalls_eq_map, List.length_map] using same

private theorem selectedCalls_eq_map_events {Id Thread : Type}
    (target : Atomics64.CellId64) (identifier : Atomics64.FetchAddEvent → Id)
    (thread : Atomics64.FetchAddEvent → Thread) (observations : List Observation)
    (covered : ∀ tid event, Observation.rmw tid event ∈ observations → event.cell = target) :
    AtomicFetchAddHistory64.selectedCalls target identifier thread
        (observations.map TSO64History.label) =
      (observations.filterMap TSO64History.label).map
        (fun event => AtomicFetchAddHistory64.asCall (identifier event) (thread event) event) := by
  revert covered
  induction observations with
  | nil =>
    intro _covered
    rfl
  | cons observation rest ih =>
    intro covered
    have tailCovered : ∀ tid event, Observation.rmw tid event ∈ rest → event.cell = target := by
      intro tid event member
      exact covered tid event (List.mem_cons_of_mem observation member)
    have remaining := ih tailCovered
    cases observation with
    | ordinary _tid =>
      simpa only [List.map_cons, List.filterMap_cons, TSO64History.label,
        AtomicFetchAddHistory64.selectedCalls] using remaining
    | returned _tid =>
      simpa only [List.map_cons, List.filterMap_cons, TSO64History.label,
        AtomicFetchAddHistory64.selectedCalls] using remaining
    | blocked _tid =>
      simpa only [List.map_cons, List.filterMap_cons, TSO64History.label,
        AtomicFetchAddHistory64.selectedCalls] using remaining
    | drained _tid _pending =>
      simpa only [List.map_cons, List.filterMap_cons, TSO64History.label,
        AtomicFetchAddHistory64.selectedCalls] using remaining
    | rmw tid event =>
      have selected := covered tid event List.mem_cons_self
      simp only [List.map_cons, List.filterMap_cons, TSO64History.label,
        AtomicFetchAddHistory64.selectedCalls, selected, ↓reduceIte]
      exact congrArg
        (fun calls => AtomicFetchAddHistory64.asCall (identifier event) (thread event) event :: calls)
        remaining

/-- Change only the labels of each call, in the original order. Complete
target coverage is a separate premise, not inferred from a count or a filter. -/
theorem selectedCalls_forall₂_incrementCalls {Id Thread : Type}
    (target : Atomics64.CellId64) (identifier : Atomics64.FetchAddEvent → Id)
    (thread : Atomics64.FetchAddEvent → Thread) (observations : List Observation)
    (covered : ∀ tid event, Observation.rmw tid event ∈ observations → event.cell = target) :
    ModuloCounter.Forall₂ ModuloCounter.SameValues
      (AtomicFetchAddHistory64.selectedCalls target identifier thread
        (observations.map TSO64History.label))
      (incrementCalls observations) := by
  rw [selectedCalls_eq_map_events target identifier thread observations covered,
    ← occurrences_events observations, List.map_map, incrementCalls_eq_map]
  exact ModuloCounter.Forall₂.of_map
    (fun occurrence : Occurrence => AtomicFetchAddHistory64.asCall
      (identifier occurrence.event) (thread occurrence.event) occurrence.event)
    Occurrence.asCall (occurrences observations) (fun _ => ⟨rfl, rfl⟩)

/-- Same run, same current full64 word, chronological original positions and
actual scheduler tids. The owned-only profile is required by the reused
history theorem; either existing RMW family is supported. Arbitrary deltas
remain arbitrary: unit increments must be established separately by clients. -/
theorem schedule_sequential {before : State} {actions : List Action}
    {result : State × List Observation} {family : RMWFamily}
    (valid : WellFormed before .ownedOnly)
    (success : schedule before actions .ownedOnly family = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : before.world.cells target = some cell)
    (covered : ∀ tid event, Observation.rmw tid event ∈ result.2 → event.cell = target)
    (prior : Word)
    (read : loadQWord (published before.world) cell.address = .ok prior) :
    ∃ final, loadQWord (published result.1.world) cell.address = .ok final ∧
      ModuloCounter.Sequential prior (incrementCalls result.2) final := by
  obtain ⟨final, current, legal⟩ :=
    TSO64History.schedule_sequential valid success target cell live
      (fun _ => ()) (fun _ => ()) prior read
  exact ⟨final, current, legal.relabel
    (selectedCalls_forall₂_incrementCalls target (fun _ => ()) (fun _ => ()) result.2 covered)⟩

#print axioms incrementCalls_eq_map
#print axioms mem_occurrences_iff
#print axioms occurrences_events
#print axioms occurrences_chronological
#print axioms incrementCalls_chronological
#print axioms incrementCalls_distinct
#print axioms incrementCalls_length
#print axioms selectedCalls_forall₂_incrementCalls
#print axioms schedule_sequential

end EDSL.OS.TSO64.PositionHistory

#audit_edsl
