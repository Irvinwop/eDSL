/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.Conditions
import EDSL.Concurrency.C23Atomic.Check.WellFormed

/-!
Soundness of the finite table and happens-before certificate checks for the
supplied atomic-only fragment. The certificate may over-approximate actual
happens-before; certified edges are subject to the finite coherence and
no-future checks. This supplies no completeness, source frontend or native-code
claim.

RMW predecessor checking concerns actual modifications on the same object.
Ranks may have gaps, and RF writer identities come from the source table,
independently of equal values or event-list order.
-/

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check

variable {Location Value : Type}

/-- Transfer finite consistency obligations through a checked HB superset to
every semantic legality field, retaining structural well-formedness. -/
theorem ConditionsSpec.sound {table : Table Location Value} {matrix : Matrix}
    (conditions : ConditionsSpec table matrix) (hb : HBSpec table matrix)
    (wf : C23Atomic.WellFormed table.toCandidate) : Legal table.toCandidate := by
  obtain ⟨pairs, perIndex⟩ := conditions
  refine {
    wellFormed := wf
    coherent := {
      writeWrite := ?_
      readRead := ?_
      readWrite := ?_
      writeRead := ?_
    }
    acyclic := hb.acyclic
    noFutureRead := ?_
    rmwPredecessor := ?_
  }
  · intro first second location a b firstWrite secondWrite before
    let firstIndex : table.Index := ⟨first, table.writes_bound firstWrite⟩
    let secondIndex : table.Index := ⟨second, table.writes_bound secondWrite⟩
    have firstData := (table.writes_iff firstIndex location a).mp firstWrite
    have secondData := (table.writes_iff secondIndex location b).mp secondWrite
    have applicable := pairs firstIndex secondIndex (hb.covers before)
      (firstData.1.trans secondData.1.symm)
    exact applicable.1 (congrArg Option.isSome firstData.2)
      (congrArg Option.isSome secondData.2)
  · intro first second left right location a b firstRead secondRead firstRF secondRF before
    let firstIndex : table.Index := ⟨first, table.reads_bound firstRead⟩
    let secondIndex : table.Index := ⟨second, table.reads_bound secondRead⟩
    have firstData := (table.reads_iff firstIndex location a).mp firstRead
    have secondData := (table.reads_iff secondIndex location b).mp secondRead
    have applicable := pairs firstIndex secondIndex (hb.covers before)
      (firstData.1.trans secondData.1.symm)
    have ordered := applicable.2.1 (congrArg Option.isSome firstData.2)
      (congrArg Option.isSome secondData.2)
    have firstSource : table.source firstIndex.val = some left := firstRF.1
    have secondSource : table.source secondIndex.val = some right := secondRF.1
    unfold RRSource at ordered
    rw [firstSource, secondSource] at ordered
    exact ordered
  · intro reader observed writer location a b read actualRF written before
    let readIndex : table.Index := ⟨reader, table.reads_bound read⟩
    let writeIndex : table.Index := ⟨writer, table.writes_bound written⟩
    have readData := (table.reads_iff readIndex location a).mp read
    have writeData := (table.writes_iff writeIndex location b).mp written
    have applicable := pairs readIndex writeIndex (hb.covers before)
      (readData.1.trans writeData.1.symm)
    have ordered := applicable.2.2.1 (congrArg Option.isSome readData.2)
      (congrArg Option.isSome writeData.2)
    have selected : table.source readIndex.val = some observed := actualRF.1
    unfold RWSource at ordered
    rw [selected] at ordered
    exact ordered
  · intro writer reader observed location a b written read actualRF before
    let writeIndex : table.Index := ⟨writer, table.writes_bound written⟩
    let readIndex : table.Index := ⟨reader, table.reads_bound read⟩
    have writeData := (table.writes_iff writeIndex location a).mp written
    have readData := (table.reads_iff readIndex location b).mp read
    have applicable := pairs writeIndex readIndex (hb.covers before)
      (writeData.1.trans readData.1.symm)
    have ordered := applicable.2.2.2 (congrArg Option.isSome writeData.2)
      (congrArg Option.isSome readData.2)
    have selected : table.source readIndex.val = some observed := actualRF.1
    unfold WRSource at ordered
    rw [selected] at ordered
    exact ordered
  · intro reader writer actualRF future
    obtain ⟨_, _, read, _⟩ := actualRF.2
    let actual : table.Index := ⟨reader, table.reads_bound read⟩
    have selected : table.source actual.val = some writer := actualRF.1
    have absent := (perIndex actual).1
    unfold NoFuture at absent
    rw [selected] at absent
    have impossible : false = true := absent.symm.trans (hb.covers future)
    cases impossible
  · intro index writer actualRMW actualRF
    obtain ⟨_, _, actualRead, _⟩ := actualRF.2
    let actual : table.Index := ⟨index, table.reads_bound actualRead⟩
    have checkedRMW : RMWSpec table actual :=
      (perIndex actual).2 ((isRMW_iff table actual).mp actualRMW)
    obtain ⟨selected, selectedSource, _, _, selectedBefore, noMiddle⟩ := checkedRMW
    have actualSource : table.source actual.val = some writer := actualRF.1
    have writerIdentity : selected.val = writer :=
      Option.some.inj (selectedSource.symm.trans actualSource)
    obtain ⟨before, after, currentRead, currentWrite⟩ := rmw_values table actual actualRMW
    have sourceWrite : Writes table.toCandidate writer (table.node actual).object before :=
      actualRF.source currentRead
    have rankBefore : table.rank writer < table.rank index := by
      rw [← writerIdentity]
      exact selectedBefore
    refine ⟨⟨(table.node actual).object, before, after, sourceWrite, currentWrite,
      rankBefore⟩, ?_⟩
    intro middle sourceBeforeMiddle middleBeforeCurrent
    obtain ⟨object, _, middleValue, sourceAtObject, middleAtObject, lower⟩ :=
      sourceBeforeMiddle
    obtain ⟨_, _, _, _, _, upper⟩ := middleBeforeCurrent
    have sameObject : object = (table.node actual).object :=
      (Writes.unique sourceAtObject sourceWrite).1
    obtain ⟨event, live, eventObject, stored⟩ := middleAtObject
    obtain ⟨middleIndex, sameMiddle, _⟩ := table.live_index live
    have finiteMiddle : Writes table.toCandidate middleIndex.val object middleValue := by
      rw [sameMiddle]
      exact ⟨event, live, eventObject, stored⟩
    have middleData := (table.writes_iff middleIndex object middleValue).mp finiteMiddle
    apply noMiddle middleIndex (middleData.1.trans sameObject)
      (congrArg Option.isSome middleData.2)
    constructor
    · rw [writerIdentity, sameMiddle]
      exact lower
    · rw [sameMiddle]
      exact upper

/-- Evaluate structural, HB-certificate and consistency obligations on the
supplied finite tables. Rejection need not establish semantic illegality. -/
def check [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (matrix : Matrix) : Bool :=
  checkWellFormed table && checkHappensBefore table matrix && checkConditions table matrix

/-- The only substantive premise is successful evaluation of the checker. -/
theorem check_sound [DecidableEq Location] [DecidableEq Value]
    (table : Table Location Value) (matrix : Matrix) (checked : check table matrix = true) :
    Legal table.toCandidate := by
  simp only [check, Bool.and_eq_true] at checked
  obtain ⟨⟨wellFormed, happensBefore⟩, conditions⟩ := checked
  exact (checkConditions_spec table matrix conditions).sound
    (checkHappensBefore_sound table matrix happensBefore)
    (checkWellFormed_sound table wellFormed)

end EDSL.Concurrency.C23Atomic.Check
