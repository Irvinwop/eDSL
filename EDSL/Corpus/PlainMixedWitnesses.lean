/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainWitnesses
import EDSL.OS.PlainCallWitness64.Mixed
import EDSL.OS.PlainCallWitness64.ReadFrom

/-!
Adapt the shared mixed execution and actual-source theorem to the unchanged
UsefulMixed gate. Worker indices identify original invocations; the retained
machine-event ordering separately establishes the two graph-slot indices.
The real buffered publication, delayed timing and reads-from edge all belong
to the same independently derived ClosedPost.

The frozen adapters retain the complete original GCC and Clang ELF files and
reuse one proof for both. Values, allocation counters and logical occurrences
remain arbitrary, including equal initial and stored words. Cohort certificates
combine the existing universal claim with homogeneous high-word executions and
the actual mixed execution. Corpus accounting is a separate integration step.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.Plain
open X86 OS OS.TSO64 Grading.ConcurrentTask.Plain64

/-- UsefulMixed is constructed from present loaded resources. Static shapes,
worker population, the two actual input kinds and persistent target identity
are the only additional premises. No desired run, publication, source, graph,
slot list or expected result is an input. -/
theorem usefulMixed {file : List Byte} {named : List (NamedImage file)}
    (batch : LoadedBatch file named)
    (static : PlainCallAdmission64.StaticShapes (named.map NamedImage.site))
    (population : batch.before.workers.length = 2)
    (writing : (batch.inputs (PlainCallWitness64.slot0 population)).site.kind = .storeRelease)
    (reading : (batch.inputs (PlainCallWitness64.slot1 population)).site.kind = .loadAcquire)
    (sameCell : (batch.inputs (PlainCallWitness64.slot0 population)).target =
      (batch.inputs (PlainCallWitness64.slot1 population)).target)
    (choices : Nat → Nat → Bool := fun _ _ => false) : Nonempty (UsefulMixed named) := by
  let writer := PlainCallAdmission64.invocations static batch.pre.1
    (PlainCallWitness64.slot0 population)
  obtain ⟨execution⟩ := PlainCallWitness64.closed_mixed static batch.pre.1 batch.pre.2
    population writing choices
  have accessOrder :
      (execution.post.calls.outcomes (PlainCallWitness64.slot0 population)).performed <
        (execution.post.calls.outcomes (PlainCallWitness64.slot1 population)).performed :=
    Nat.lt_trans (execution.post.calls.outcomes (PlainCallWitness64.slot0 population)).beforeReturn
      (Nat.lt_trans execution.returnedBeforeStamp execution.stampBeforeReader)
  have slots := execution.post.slots_pair population
    (PlainCallWitness64.slot0 population) (PlainCallWitness64.slot1 population)
    rfl rfl accessOrder
  have slotCount : execution.post.calls.slots.length = 2 := by
    rw [slots]
    rfl
  let writerSlot : Fin execution.post.calls.slots.length := ⟨0, by omega⟩
  let readerSlot : Fin execution.post.calls.slots.length := ⟨1, by omega⟩
  have writerAt : execution.post.calls.slots[0]? =
      some (PlainCallWitness64.slot0 population) := by
    rw [slots]
    rfl
  have readerAt : execution.post.calls.slots[1]? =
      some (PlainCallWitness64.slot1 population) := by
    rw [slots]
    rfl
  have writerEntry : execution.post.calls.slots[writerSlot.val] =
      PlainCallWitness64.slot0 population := (List.getElem_of_getElem? writerAt).2
  have readerEntry : execution.post.calls.slots[readerSlot.val] =
      PlainCallWitness64.slot1 population := (List.getElem_of_getElem? readerAt).2
  have others : ∀ tid, tid ≠ PlainCallWitness64.slot0 population →
      (batch.inputs tid).site.kind = .loadAcquire := by
    intro tid different
    have bound := tid.isLt
    have nonzero : tid.val ≠ 0 := by
      intro zero
      exact different (Fin.ext zero)
    have same : tid = PlainCallWitness64.slot1 population := Fin.ext (by
      change tid.val = 1
      omega)
    simpa only [same] using reading
  have selected := execution.post.readsFrom_published_before static batch.pre
    (PlainCallWitness64.slot0 population) (PlainCallWitness64.slot1 population)
    writing reading others sameCell execution.stampMember execution.publication
    execution.stampBeforeReader writerAt readerAt
  exact ⟨{
    batch := batch
    population := population
    actions := PlainCallWitness64.mixedPrefixActions writer (choices 0) execution.writerResult ++
      execution.suffix
    actual := execution.actual
    scheduled := execution.scheduled
    finished := execution.finished
    post := execution.post
    writerSlot := writerSlot
    readerSlot := readerSlot
    writerKind := by
      rw [writerEntry]
      exact writing
    readerKind := by
      rw [readerEntry]
      exact reading
    selectedRF := selected
    delayed := ⟨execution.stamp, execution.stampMember, by
        rw [writerEntry]
        exact execution.publication, by
        rw [writerEntry]
        exact execution.returnedBeforeStamp, by
        rw [readerEntry]
        exact execution.stampBeforeReader⟩ }⟩

end EDSL.Corpus.Plain

namespace EDSL.Corpus.PlainMixedWitnesses
open X86 OS OS.TSO64 Grading.ConcurrentTask.Plain64
open PlainResources

abbrev Compiler := V1.PlainInputs.Compiler

private theorem cohort_target {original : AddressSpace.Space} {catalog : Catalog} {layout : Layout}
    {old : Word} {first second : Choice} (current : Cohort original catalog layout old first second)
    (tid : Fin current.state.workers.length) :
    (current.inputs tid).target = current.resources.target := by
  unfold Cohort.inputs pairInputs
  split <;> exact input_target _ _ _

/-- One proof supplies either unchanged final ELF's mixed store/load execution.
All data and labels remain arbitrary; equal initial/stored words cannot create
an assumed source identity or graph edge. -/
theorem mixed (compiler : Compiler) (old storeValue unusedLoadValue : Word)
    (storeCounter loadCounter storeOccurrence loadOccurrence : Nat)
    (choices : Nat → Nat → Bool := fun _ _ => false) :
    Nonempty (Plain.UsefulMixed (V1.PlainInputs.images compiler)) := by
  let current := Inputs.cohort compiler .storeRelease .loadAcquire old storeValue unusedLoadValue
    storeCounter loadCounter storeOccurrence loadOccurrence
  let batch := Inputs.mixed compiler old storeValue unusedLoadValue
    storeCounter loadCounter storeOccurrence loadOccurrence
  have population : batch.before.workers.length = 2 := rfl
  refine Plain.usefulMixed batch (V1.PlainInputs.staticShapes compiler) population ?_ ?_ ?_ choices
  · change (input (Frozen.choice compiler .storeRelease storeValue storeCounter storeOccurrence)
      current.resources.target current.resources.cell).site.kind = .storeRelease
    rw [input_site]
    rfl
  · change (input (Frozen.choice compiler .loadAcquire unusedLoadValue loadCounter loadOccurrence)
      current.resources.target current.resources.cell).site.kind = .loadAcquire
    rw [input_site]
    rfl
  · change (current.inputs (PlainCallWitness64.slot0 population)).target =
      (current.inputs (PlainCallWitness64.slot1 population)).target
    exact (cohort_target current _).trans (cohort_target current _).symm

/-- All original certificate gates are retained: universal mixed-catalog Claim,
high-word homogeneous witnesses for each registered kind, and the actual mixed
publication/source execution over the same complete file. -/
def cohortCertificate (compiler : Compiler)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Plain.CohortCertificate (V1.PlainWindows.file compiler) where
  named := V1.PlainInputs.named compiler
  registeredKinds := fun _kind => rfl
  claim := V1.PlainClaims.cohort compiler
  homogeneous := fun kind => PlainWitnesses.high_homogeneous compiler kind
    counterA counterB occurrenceA occurrenceB
  mixed := mixed compiler PlainWitnesses.highInitial PlainWitnesses.highStoreA PlainWitnesses.highStoreB
    counterA counterB occurrenceA occurrenceB

def gcc : Plain.CohortCertificate (V1.PlainWindows.file .defaultGCC) :=
  cohortCertificate .defaultGCC 17 29 101 202

def clang : Plain.CohortCertificate (V1.PlainWindows.file .defaultClang) :=
  cohortCertificate .defaultClang 17 29 101 202

end EDSL.Corpus.PlainMixedWitnesses

#audit_edsl
