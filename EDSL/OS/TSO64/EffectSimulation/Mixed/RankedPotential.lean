/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit
import Init.Data.List.FinRange
import Init.Data.List.Nat.Sum

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Finite natural-valued potentials, independent of cohort states and transitions.
Pointwise nonincrease preserves the total bound, and a strict decrease at any
index strictly decreases the total. These algebraic facts do not supply an
execution, scheduling, fairness, OS, hardware, or corpus termination claim.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPotential

universe u

/-- Total natural-valued potential over every index of a finite cohort. -/
def indexedSum {n : Nat} (values : Fin n -> Nat) : Nat :=
  ((List.finRange n).map values).sum

private theorem listSum_le {α : Type u} (indices : List α)
    {before after : α -> Nat} (pointwise : ∀ i, after i ≤ before i) :
    (indices.map after).sum ≤ (indices.map before).sum := by
  induction indices with
  | nil => exact Nat.le_refl 0
  | cons i indices ih =>
      simpa only [List.map_cons, List.sum_cons] using
        Nat.add_le_add (pointwise i) ih

private theorem listSum_lt {α : Type u} (indices : List α)
    {before after : α -> Nat} (pointwise : ∀ i, after i ≤ before i)
    (strict : ∃ i ∈ indices, after i < before i) :
    (indices.map after).sum < (indices.map before).sum := by
  revert strict
  induction indices with
  | nil =>
      intro strict
      obtain ⟨i, member, _⟩ := strict
      cases member
  | cons i indices ih =>
      intro strict
      obtain ⟨j, member, decrease⟩ := strict
      rcases List.mem_cons.mp member with equal | member
      · subst j
        simpa only [List.map_cons, List.sum_cons] using
          Nat.add_lt_add_of_lt_of_le decrease (listSum_le indices pointwise)
      · simpa only [List.map_cons, List.sum_cons] using
          Nat.add_lt_add_of_le_of_lt (pointwise i) (ih ⟨j, member, decrease⟩)

/-- Pointwise nonincrease bounds the total potential, including an empty cohort. -/
theorem indexedSum_le {n : Nat} {before after : Fin n -> Nat}
    (pointwise : ∀ i, after i ≤ before i) : indexedSum after ≤ indexedSum before := by
  exact listSum_le (List.finRange n) pointwise

/-- One strictly decreasing index suffices when every index is nonincreasing. -/
theorem indexedSum_lt {n : Nat} {before after : Fin n -> Nat}
    (pointwise : ∀ i, after i ≤ before i) (strict : ∃ i, after i < before i) :
    indexedSum after < indexedSum before := by
  obtain ⟨i, decrease⟩ := strict
  exact listSum_lt (List.finRange n) pointwise ⟨i, List.mem_finRange i, decrease⟩

/-- A finite total is zero exactly when each natural-valued component is zero. -/
theorem indexedSum_zero_iff {n : Nat} (values : Fin n -> Nat) :
    indexedSum values = 0 ↔ ∀ i, values i = 0 := by
  unfold indexedSum
  rw [List.sum_eq_zero_iff_forall_eq_nat, List.forall_mem_map]
  constructor
  · intro zero i
    exact zero i (List.mem_finRange i)
  · intro zero i _
    exact zero i

#print axioms indexedSum
#print axioms listSum_le
#print axioms listSum_lt
#print axioms indexedSum_le
#print axioms indexedSum_lt
#print axioms indexedSum_zero_iff

end EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPotential

#audit_edsl
