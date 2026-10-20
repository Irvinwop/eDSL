/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.HappensBefore

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check
variable {Location Value : Type}

def RRSource (table : Table Location Value) (first second : table.Index) : Prop :=
  match table.source first.val, table.source second.val with
  | some left, some right => table.rank left ≤ table.rank right
  | _, _ => False

instance (table : Table Location Value) (first second : table.Index) :
    Decidable (RRSource table first second) := by
  unfold RRSource
  split <;> infer_instance

def RWSource (table : Table Location Value) (reader writer : table.Index) : Prop :=
  match table.source reader.val with
  | some observed => table.rank observed < table.rank writer.val
  | none => False

instance (table : Table Location Value) (reader writer : table.Index) :
    Decidable (RWSource table reader writer) := by
  unfold RWSource
  split <;> infer_instance

def WRSource (table : Table Location Value) (writer reader : table.Index) : Prop :=
  match table.source reader.val with
  | some observed => table.rank writer.val ≤ table.rank observed
  | none => False

instance (table : Table Location Value) (writer reader : table.Index) :
    Decidable (WRSource table writer reader) := by
  unfold WRSource
  split <;> infer_instance

/-- Each certified HB edge must respect all applicable coherence directions
on its actual object. RMW events participate in both read and write checks. -/
def PairSpec (table : Table Location Value) (matrix : Matrix)
    (first second : table.Index) : Prop :=
  edge matrix first.val second.val = true →
  (table.node first).object = (table.node second).object →
  (((table.node first).access.writeValue.isSome = true →
      (table.node second).access.writeValue.isSome = true →
      table.rank first.val < table.rank second.val) ∧
    ((table.node first).access.readValue.isSome = true →
      (table.node second).access.readValue.isSome = true → RRSource table first second) ∧
    ((table.node first).access.readValue.isSome = true →
      (table.node second).access.writeValue.isSome = true → RWSource table first second) ∧
    ((table.node first).access.writeValue.isSome = true →
      (table.node second).access.readValue.isSome = true → WRSource table first second))

instance [DecidableEq Location] (table : Table Location Value) (matrix : Matrix)
    (first second : table.Index) : Decidable (PairSpec table matrix first second) := by
  unfold PairSpec
  infer_instance

def NoFuture (table : Table Location Value) (matrix : Matrix) (reader : table.Index) : Prop :=
  match table.source reader.val with
  | none => True
  | some writer => edge matrix reader.val writer = false

instance (table : Table Location Value) (matrix : Matrix) (reader : table.Index) :
    Decidable (NoFuture table matrix reader) := by
  unfold NoFuture
  split <;> infer_instance

/-- The source is the previous actual modification, not the preceding number.
Checking all actual writes admits arbitrary order-preserving gaps in ranks. -/
def RMWSpec (table : Table Location Value) (index : table.Index) : Prop :=
  ∃ writer : table.Index,
    table.source index.val = some writer.val ∧
    (table.node writer).object = (table.node index).object ∧
    (table.node writer).access.writeValue.isSome = true ∧
    table.rank writer.val < table.rank index.val ∧
    ∀ middle : table.Index,
      (table.node middle).object = (table.node index).object →
      (table.node middle).access.writeValue.isSome = true →
      ¬ (table.rank writer.val < table.rank middle.val ∧
        table.rank middle.val < table.rank index.val)

instance [DecidableEq Location] (table : Table Location Value) (index : table.Index) :
    Decidable (RMWSpec table index) := by
  unfold RMWSpec
  infer_instance

def ConditionsSpec (table : Table Location Value) (matrix : Matrix) : Prop :=
  (∀ first second : table.Index, PairSpec table matrix first second) ∧
  (∀ index : table.Index,
    NoFuture table matrix index ∧ ((table.node index).access.isRMW = true → RMWSpec table index))

instance [DecidableEq Location] (table : Table Location Value) (matrix : Matrix) :
    Decidable (ConditionsSpec table matrix) := by
  unfold ConditionsSpec
  infer_instance

def checkConditions [DecidableEq Location] (table : Table Location Value)
    (matrix : Matrix) : Bool := decide (ConditionsSpec table matrix)

theorem checkConditions_spec [DecidableEq Location] (table : Table Location Value)
    (matrix : Matrix) (checked : checkConditions table matrix = true) :
    ConditionsSpec table matrix := of_decide_eq_true checked

end EDSL.Concurrency.C23Atomic.Check
