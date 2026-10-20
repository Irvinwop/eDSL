/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.Table

/-!
An executable structural check over the actual finite event and metadata
tables. Read sources name a live writer with the required object and value;
matching values alone never select or identify a writer. Exact metadata shape
also excludes source entries beyond the event list.

Soundness establishes only `C23Atomic.WellFormed`. Happens-before, coherence
and RMW predecessor legality require separate checks.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check

variable {Location Value : Type}

/-- Finite structural obligations, with no semantic oracle or proof field. -/
def WellFormedSpec (table : Table Location Value) : Prop :=
  table.Shape ∧
  (∀ index : table.Index,
    (table.node index).thread = none ↔ (table.node index).access.isInitial = true) ∧
  (∀ first second : table.Index,
    (table.node first).access.isInitial = true →
    (table.node second).access.isInitial = true →
    (table.node first).object = (table.node second).object → first.val = second.val) ∧
  (∀ index : table.Index, ∃ initial : table.Index,
    (table.node initial).access.isInitial = true ∧
    (table.node initial).object = (table.node index).object) ∧
  (∀ index : table.Index, (table.node index).access.writeValue.isSome = true →
    ((table.node index).access.isInitial = true → table.rank index.val = 0) ∧
    ((table.node index).access.isInitial = false → 0 < table.rank index.val)) ∧
  (∀ first second : table.Index,
    (table.node first).access.writeValue.isSome = true →
    (table.node second).access.writeValue.isSome = true →
    (table.node first).object = (table.node second).object →
    table.rank first.val = table.rank second.val → first.val = second.val) ∧
  (∀ index : table.Index,
    match (table.node index).access.readValue with
    | none => table.source index.val = none
    | some value => ∃ writer : table.Index,
        table.source index.val = some writer.val ∧
        (table.node writer).object = (table.node index).object ∧
        (table.node writer).access.writeValue = some value)

instance [DecidableEq Location] [DecidableEq Value] (table : Table Location Value) :
    Decidable (WellFormedSpec table) := by
  haveI (index : table.Index) : Decidable
      (match (table.node index).access.readValue with
      | none => table.source index.val = none
      | some value => ∃ writer : table.Index,
          table.source index.val = some writer.val ∧
          (table.node writer).object = (table.node index).object ∧
          (table.node writer).access.writeValue = some value) := by
    split <;> infer_instance
  unfold WellFormedSpec
  infer_instance

/-- Decide every structural obligation over the supplied finite tables. -/
def checkWellFormed [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) : Bool :=
  decide (WellFormedSpec table)

private theorem initial_iff (table : Table Location Value) (index : table.Index) :
    IsInitial table.toCandidate index.val ↔ (table.node index).access.isInitial = true := by
  constructor
  · rintro ⟨event, live, initial⟩
    rw [table.node_of_lookup index live]
    exact initial
  · intro initial
    exact ⟨table.node index, table.node_lookup index, initial⟩

private theorem initial_has_write (access : Access Value) (initial : access.isInitial = true) :
    ∃ value, access.writeValue = some value := by
  cases access with
  | «initialize» value => exact ⟨value, rfl⟩
  | load _ _ => cases initial
  | store _ _ => cases initial
  | rmw _ _ _ => cases initial

/-- Every finite obligation yields the corresponding semantic structural field,
including absence of read sources at indices outside the event list. -/
theorem WellFormedSpec.sound {table : Table Location Value} (spec : WellFormedSpec table) :
    C23Atomic.WellFormed table.toCandidate := by
  rcases spec with
    ⟨shape, threadKind, initialUnique, initialExists, initialRank, rankUnique, readsSource⟩
  refine {
    threadKind := ?_
    initialUnique := ?_
    initialExists := ?_
    initialRank := ?_
    rankUnique := ?_
    readsSource := ?_
    noReadSource := ?_
  }
  · intro index event live
    obtain ⟨actual, _, sameEvent⟩ := table.live_index live
    have kind := threadKind actual
    rw [sameEvent] at kind
    exact kind
  · intro i j location before after firstWrite secondWrite firstInitial secondInitial
    let first : table.Index := ⟨i, table.writes_bound firstWrite⟩
    let second : table.Index := ⟨j, table.writes_bound secondWrite⟩
    have firstData := (table.writes_iff first location before).mp firstWrite
    have secondData := (table.writes_iff second location after).mp secondWrite
    exact initialUnique first second
      ((initial_iff table first).mp firstInitial)
      ((initial_iff table second).mp secondInitial)
      (firstData.1.trans secondData.1.symm)
  · intro index event live
    obtain ⟨actual, _, sameEvent⟩ := table.live_index live
    obtain ⟨initial, initialFlag, sameObject⟩ := initialExists actual
    obtain ⟨value, stored⟩ := initial_has_write (table.node initial).access initialFlag
    rw [sameEvent] at sameObject
    exact ⟨initial.val, value,
      (table.writes_iff initial event.object value).mpr ⟨sameObject, stored⟩,
      (initial_iff table initial).mpr initialFlag⟩
  · intro index location value written
    let actual : table.Index := ⟨index, table.writes_bound written⟩
    have stored := ((table.writes_iff actual location value).mp written).2
    have isWrite : (table.node actual).access.writeValue.isSome = true :=
      congrArg Option.isSome stored
    have ranks := initialRank actual isWrite
    constructor
    · intro initial
      exact ranks.1 ((initial_iff table actual).mp initial)
    · intro notInitial
      have noninitialFlag : (table.node actual).access.isInitial = false := by
        cases flag : (table.node actual).access.isInitial with
        | false => rfl
        | true => exact False.elim (notInitial ((initial_iff table actual).mpr flag))
      exact ranks.2 noninitialFlag
  · intro i j location before after firstWrite secondWrite equalRank
    let first : table.Index := ⟨i, table.writes_bound firstWrite⟩
    let second : table.Index := ⟨j, table.writes_bound secondWrite⟩
    have firstData := (table.writes_iff first location before).mp firstWrite
    have secondData := (table.writes_iff second location after).mp secondWrite
    have firstIsWrite : (table.node first).access.writeValue.isSome = true :=
      congrArg Option.isSome firstData.2
    have secondIsWrite : (table.node second).access.writeValue.isSome = true :=
      congrArg Option.isSome secondData.2
    exact rankUnique first second firstIsWrite secondIsWrite
      (firstData.1.trans secondData.1.symm) equalRank
  · intro reader location value read
    let actual : table.Index := ⟨reader, table.reads_bound read⟩
    have readData := (table.reads_iff actual location value).mp read
    have selected := readsSource actual
    rw [readData.2] at selected
    obtain ⟨writer, source, sameObject, stored⟩ := selected
    refine ⟨writer.val, source, location, value, read, ?_⟩
    exact (table.writes_iff writer location value).mpr
      ⟨sameObject.trans readData.1, stored⟩
  · intro index noRead
    by_cases bound : index < table.events.length
    · let actual : table.Index := ⟨index, bound⟩
      have noneRead : (table.node actual).access.readValue = none := by
        cases observed : (table.node actual).access.readValue with
        | none => rfl
        | some value =>
          exact False.elim (noRead (table.node actual).object value
            ((table.reads_iff actual (table.node actual).object value).mpr ⟨rfl, observed⟩))
      have source := readsSource actual
      rw [noneRead] at source
      exact source
    · exact table.source_outside shape (Nat.le_of_not_lt bound)

/-- Successful evaluation certifies structural well-formedness only. -/
theorem checkWellFormed_sound [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (checked : checkWellFormed table = true) :
    C23Atomic.WellFormed table.toCandidate := by
  have spec : WellFormedSpec table := of_decide_eq_true checked
  exact spec.sound

end EDSL.Concurrency.C23Atomic.Check
