/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Counts
import EDSL.OS.TSO64History
import EDSL.Audit
import Init.Data.List.Nat.Sum

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Finite-cohort arithmetic for complete native observation
lists. No scheduler positions are removed before a subject's existing Nat count
is measured. The total is independently the length of the native typed-event
projection, retaining every RMW occurrence including identical payloads.

These list laws neither authenticate observations nor establish cohort closure,
completion, ordinary-write exclusion, lifecycle, or final RAM. Their event-local
premises must be obtained from the same actual schedule before applying native
history conservation. Client event identifiers and thread names remain arbitrary;
this module does not equate them with scheduler tids or prove their uniqueness.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed.EventCounts
open Counts

/-- One native RMW occurrence contributes one, whatever its issuer or payload. -/
def rmwWeight : Observation → Nat
  | .rmw _ _ => 1
  | _ => 0

/-- The number of all actual RMW labels, before selecting a cell or issuer.
Identical events at different list positions remain separate occurrences. -/
def totalRMW (observations : List Observation) : Nat :=
  (observations.filterMap TSO64History.label).length

@[simp] theorem totalRMW_nil : totalRMW [] = 0 := rfl

@[simp] theorem totalRMW_cons (observation : Observation) (rest : List Observation) :
    totalRMW (observation :: rest) = rmwWeight observation + totalRMW rest := by
  cases observation <;>
    simp [totalRMW, List.filterMap_cons, TSO64History.label, rmwWeight, Nat.add_comm]

theorem totalRMW_append (front back : List Observation) :
    totalRMW (front ++ back) = totalRMW front + totalRMW back := by
  induction front with
  | nil => simp only [List.nil_append, totalRMW_nil, Nat.zero_add]
  | cons head tail ih =>
    simp only [List.cons_append, totalRMW_cons, ih, Nat.add_assoc]

/-- For an RMW label, summing the existing subject weights counts how often its
actual scheduler tid appears in the supplied enumeration. -/
private theorem sum_ownRMW_rmw (tids : List Nat) (tid : Nat)
    (event : Atomics64.FetchAddEvent) :
    (tids.map (fun subject => ownRMW subject (.rmw tid event))).sum = tids.count tid := by
  induction tids with
  | nil => rfl
  | cons subject rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    by_cases same : tid = subject
    · subst subject
      simp only [ownRMW_rmw, ↓reduceIte, List.count_cons_self]
      omega
    · simp only [ownRMW_rmw, ite_eq_right same, List.count_cons_of_ne (Ne.symm same),
        Nat.zero_add]

/-- Distinctness prevents double counting; membership prevents dropping the
actual RMW issuer. Silent labels contribute zero to every listed subject. -/
private theorem sum_ownRMW (tids : List Nat) (observation : Observation)
    (distinct : tids.Nodup)
    (covered : ∀ tid event, observation = .rmw tid event → tid ∈ tids) :
    (tids.map (fun subject => ownRMW subject observation)).sum = rmwWeight observation := by
  cases observation with
  | rmw tid event =>
    exact (sum_ownRMW_rmw tids tid event).trans
      (distinct.count_of_mem (covered tid event rfl))
  | ordinary _tid =>
    simp only [ownRMW, rmwWeight, List.map_const', List.sum_replicate_nat, Nat.mul_zero]
  | returned _tid =>
    simp only [ownRMW, rmwWeight, List.map_const', List.sum_replicate_nat, Nat.mul_zero]
  | blocked _tid =>
    simp only [ownRMW, rmwWeight, List.map_const', List.sum_replicate_nat, Nat.mul_zero]
  | drained _tid _pending =>
    simp only [ownRMW, rmwWeight, List.map_const', List.sum_replicate_nat, Nat.mul_zero]

private theorem sum_countRMW_cons (tids : List Nat) (observation : Observation)
    (rest : List Observation) :
    (tids.map (fun subject => countRMW subject (observation :: rest))).sum =
      (tids.map (fun subject => ownRMW subject observation)).sum +
        (tids.map (fun subject => countRMW subject rest)).sum := by
  induction tids with
  | nil => rfl
  | cons subject tids ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, countRMW_cons]
    omega

/-- An exhaustive distinct enumeration of the observed RMW issuers partitions
all occurrences into the existing full-list subject counts. This does not assume
that event actors are tids, nor that distinct occurrences have distinct payloads. -/
theorem totalRMW_eq_sum_countRMW {tids : List Nat} (distinct : tids.Nodup)
    {observations : List Observation}
    (covered : ∀ tid event, Observation.rmw tid event ∈ observations → tid ∈ tids) :
    totalRMW observations = (tids.map (fun tid => countRMW tid observations)).sum := by
  revert covered
  induction observations with
  | nil =>
    intro _covered
    simp only [totalRMW_nil, countRMW_nil, List.map_const',
      List.sum_replicate_nat, Nat.mul_zero]
  | cons observation rest ih =>
    intro covered
    have headCovered : ∀ tid event, observation = .rmw tid event → tid ∈ tids := by
      intro tid event same
      exact covered tid event (List.mem_cons.mpr (Or.inl same.symm))
    have tailCovered : ∀ tid event, Observation.rmw tid event ∈ rest → tid ∈ tids := by
      intro tid event member
      exact covered tid event (List.mem_cons_of_mem observation member)
    calc
      totalRMW (observation :: rest) = rmwWeight observation + totalRMW rest :=
        totalRMW_cons observation rest
      _ = (tids.map (fun tid => ownRMW tid observation)).sum +
          (tids.map (fun tid => countRMW tid rest)).sum := by
        rw [sum_ownRMW tids observation distinct headCovered, ih tailCovered]
      _ = (tids.map (fun tid => countRMW tid (observation :: rest))).sum :=
        (sum_countRMW_cons tids observation rest).symm

/-- Independently established per-worker counts can replace the observation
counts after cohort partitioning. Requests outside the cohort are irrelevant. -/
theorem totalRMW_eq_sum_of_counts {tids : List Nat} (distinct : tids.Nodup)
    {observations : List Observation}
    (covered : ∀ tid event, Observation.rmw tid event ∈ observations → tid ∈ tids)
    (requested : Nat → Nat)
    (counts : ∀ tid ∈ tids, countRMW tid observations = requested tid) :
    totalRMW observations = (tids.map requested).sum := by
  calc
    totalRMW observations = (tids.map (fun tid => countRMW tid observations)).sum :=
      totalRMW_eq_sum_countRMW distinct covered
    _ = (tids.map requested).sum := congrArg List.sum (List.map_congr_left counts)

/-- The smallest closed cohort: two independent scheduler slots, each counted
once in Nat. No equal-request or bounded-sum hypothesis is required. -/
theorem totalRMW_eq_two {left right : Nat} (distinct : left ≠ right)
    {observations : List Observation}
    (covered : ∀ tid event, Observation.rmw tid event ∈ observations →
      tid = left ∨ tid = right) :
    totalRMW observations = countRMW left observations + countRMW right observations := by
  have unique : [left, right].Nodup := by simp [distinct]
  have members : ∀ tid event, Observation.rmw tid event ∈ observations →
      tid ∈ [left, right] := by
    intro tid event member
    simpa using covered tid event member
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    using totalRMW_eq_sum_countRMW unique members

theorem totalRMW_eq_two_of_counts {left right : Nat} (distinct : left ≠ right)
    {observations : List Observation}
    (covered : ∀ tid event, Observation.rmw tid event ∈ observations →
      tid = left ∨ tid = right)
    {leftCount rightCount : Nat}
    (first : countRMW left observations = leftCount)
    (second : countRMW right observations = rightCount) :
    totalRMW observations = leftCount + rightCount := by
  rw [totalRMW_eq_two distinct covered, first, second]

/-- Bridge the independently selected OS arithmetic calls to the number of
native RMW occurrences. Every RMW must name this target and carry input one;
unit inputs of selected events alone would not exclude other-cell RMWs.

No return-value arithmetic or post-RAM equality is assumed. Arbitrary client
identifiers/thread names do not authenticate issuer provenance or uniqueness. -/
theorem inputSum_selectedCalls_eq_totalRMW {Id Thread : Type}
    (target : Atomics64.CellId64) (identifier : Atomics64.FetchAddEvent → Id)
    (thread : Atomics64.FetchAddEvent → Thread) (observations : List Observation)
    (increments : ∀ tid event, Observation.rmw tid event ∈ observations →
      event.cell = target ∧ event.arithmetic.delta = 1) :
    Concurrency.ModuloCounter.inputSum
      (AtomicFetchAddHistory64.selectedCalls target identifier thread
        (observations.map TSO64History.label)) = totalRMW observations := by
  revert increments
  induction observations with
  | nil =>
    intro _increments
    rfl
  | cons observation rest ih =>
    intro increments
    have tailIncrements : ∀ tid event, Observation.rmw tid event ∈ rest →
        event.cell = target ∧ event.arithmetic.delta = 1 := by
      intro tid event member
      exact increments tid event (List.mem_cons_of_mem observation member)
    have remaining := ih tailIncrements
    cases observation with
    | ordinary _tid =>
      simpa only [List.map_cons, TSO64History.label, AtomicFetchAddHistory64.selectedCalls,
        totalRMW_cons, rmwWeight, Nat.zero_add] using remaining
    | returned _tid =>
      simpa only [List.map_cons, TSO64History.label, AtomicFetchAddHistory64.selectedCalls,
        totalRMW_cons, rmwWeight, Nat.zero_add] using remaining
    | blocked _tid =>
      simpa only [List.map_cons, TSO64History.label, AtomicFetchAddHistory64.selectedCalls,
        totalRMW_cons, rmwWeight, Nat.zero_add] using remaining
    | drained _tid _pending =>
      simpa only [List.map_cons, TSO64History.label, AtomicFetchAddHistory64.selectedCalls,
        totalRMW_cons, rmwWeight, Nat.zero_add] using remaining
    | rmw tid event =>
      obtain ⟨selected, unit⟩ := increments tid event List.mem_cons_self
      have one : event.arithmetic.delta.toNat = 1 := by
        rw [unit]
        rfl
      simp only [List.map_cons, TSO64History.label, AtomicFetchAddHistory64.selectedCalls,
        selected, ↓reduceIte, Concurrency.ModuloCounter.inputSum,
        AtomicFetchAddHistory64.asCall, one, totalRMW_cons, rmwWeight]
      exact congrArg (fun n : Nat => 1 + n) remaining

#print axioms rmwWeight
#print axioms totalRMW
#print axioms totalRMW_nil
#print axioms totalRMW_cons
#print axioms totalRMW_append
#print axioms sum_ownRMW_rmw
#print axioms sum_ownRMW
#print axioms sum_countRMW_cons
#print axioms totalRMW_eq_sum_countRMW
#print axioms totalRMW_eq_sum_of_counts
#print axioms totalRMW_eq_two
#print axioms totalRMW_eq_two_of_counts
#print axioms inputSum_selectedCalls_eq_totalRMW

end EDSL.OS.TSO64.EffectSimulation.Mixed.EventCounts

#audit_edsl
