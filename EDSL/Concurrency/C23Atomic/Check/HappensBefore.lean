/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.Reflection

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check
variable {Location Value : Type}

/-- An untrusted finite relation certificate. Extra edges are allowed only
when the resulting over-approximation passes all remaining consistency checks. -/
abbrev Matrix := List (List Bool)

def edge (matrix : Matrix) (first second : Nat) : Bool :=
  (((matrix[first]?).getD [])[second]?).getD false

def MatrixShape (table : Table Location Value) (matrix : Matrix) : Prop :=
  matrix.length = table.events.length ∧
    ∀ index : table.Index, ((matrix[index.val]?).getD []).length = table.events.length

instance (table : Table Location Value) (matrix : Matrix) :
    Decidable (MatrixShape table matrix) := by
  unfold MatrixShape
  infer_instance

/-- The certificate contains the actual generating edges, is transitively
closed, and has no diagonal edge. These are finite, computable obligations. -/
def HBSpec (table : Table Location Value) (matrix : Matrix) : Prop :=
  MatrixShape table matrix ∧
  (∀ index : table.Index, edge matrix index.val index.val = false) ∧
  (∀ first second : table.Index, seq table first second →
    edge matrix first.val second.val = true) ∧
  (∀ first second : table.Index, sync table first second →
    edge matrix first.val second.val = true) ∧
  (∀ first middle last : table.Index,
    edge matrix first.val middle.val = true → edge matrix middle.val last.val = true →
      edge matrix first.val last.val = true)

instance [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (matrix : Matrix) : Decidable (HBSpec table matrix) := by
  unfold HBSpec
  infer_instance

def checkHappensBefore [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (matrix : Matrix) : Bool := decide (HBSpec table matrix)

theorem checkHappensBefore_sound [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (matrix : Matrix)
    (checked : checkHappensBefore table matrix = true) : HBSpec table matrix :=
  of_decide_eq_true checked

/-- Every actual source HB path is present in the checked certificate. No
certificate edge is assumed to be an actual source synchronization edge. -/
theorem HBSpec.covers {table : Table Location Value} {matrix : Matrix}
    (valid : HBSpec table matrix) {first last : Nat}
    (path : HappensBefore table.toCandidate first last) : edge matrix first last = true := by
  obtain ⟨_, _, sequences, synchronizes, closed⟩ := valid
  induction path with
  | @sequenced first last before =>
    have bounded := seq_bound table before
    exact sequences ⟨first, bounded.1⟩ ⟨last, bounded.2⟩
      ((seq_iff table _ _).mp before)
  | @synchronizes first last synchronized =>
    have bounded := sync_bound table synchronized
    exact synchronizes ⟨first, bounded.1⟩ ⟨last, bounded.2⟩
      ((sync_iff table _ _).mp synchronized)
  | @trans first middle last before after ihBefore ihAfter =>
    have left := hb_bound table before
    have right := hb_bound table after
    exact closed ⟨first, left.1⟩ ⟨middle, left.2⟩ ⟨last, right.2⟩ ihBefore ihAfter

/-- A diagonal-free checked superset excludes every actual HB cycle. -/
theorem HBSpec.acyclic {table : Table Location Value} {matrix : Matrix}
    (valid : HBSpec table matrix) : ∀ index, ¬ HappensBefore table.toCandidate index index := by
  intro index cycle
  have bounded := hb_bound table cycle
  have absent := valid.2.1 ⟨index, bounded.1⟩
  have impossible : false = true := absent.symm.trans (valid.covers cycle)
  cases impossible

end EDSL.Concurrency.C23Atomic.Check
