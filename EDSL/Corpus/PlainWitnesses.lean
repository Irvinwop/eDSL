/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallWitness64.Overlap
import EDSL.Corpus.PlainCertificate
import EDSL.Corpus.PlainResources.Inputs
import EDSL.Corpus.V1.PlainClaims

/-!
Thin adapters from actual present loaded resources to the unchanged UsefulNamed
gate. Execution and independent outcome positions come from the shared OS
overlap construction; the adapter accepts only current population, persistent
target identity, initial RAM and store-request facts.

The frozen adapter reuses Inputs.homogeneous and the existing static shapes and
universal PlainClaims. Both compilers and both kinds use the same proof, with
arbitrary full64 words, allocation counters and logical occurrence labels.
The high-word instances retain the complete original files and use nonzero
17/29 counters and 101/202 logical occurrences. This module supplies no mixed
publication/read-from witness, CohortCertificate or corpus accounting change.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.Plain
open X86 OS OS.TSO64 Grading.ConcurrentTask.Plain64

/-- Restrict existing checked shapes by actual catalog membership, preserving
the original padding function and byte-check evidence. -/
def singletonShapes {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    (site : Site) (member : site ∈ catalog) : PlainCallAdmission64.StaticShapes [site] where
  padding := static.padding
  checked := by
    intro selected selectedMember
    have same : selected = site := List.mem_singleton.mp selectedMember
    subst selected
    exact static.checked site member

/-- Generic UsefulNamed inhabitance from an actual whole-loaded-file batch.
All additional inputs describe its current resources. The finished execution,
ClosedPost and three strict overlap inequalities are constructed outputs. -/
theorem usefulNamed {file : List Byte} {named : NamedImage file}
    (batch : LoadedBatch file [named]) (static : PlainCallAdmission64.StaticShapes [named.site])
    (population : batch.before.workers.length = 2)
    (sameCell : ∀ i j, (batch.inputs i).target = (batch.inputs j).target)
    (initialHighWord : ∃ tid value,
      loadQWord (published batch.before.world) (batch.inputs tid).cell.address = .ok value ∧
        2^32 ≤ value.toNat)
    (storeHighWords : ∀ tid, named.kind = .storeRelease →
      ∃ value, (batch.inputs tid).request = .storeRelease (batch.inputs tid).target value ∧
        2^32 ≤ value.toNat)
    (choices : Nat → Nat → Bool := fun _ _ => false) : Nonempty (UsefulNamed named) := by
  let first := PlainCallAdmission64.invocations static batch.pre.1
    (PlainCallWitness64.slot0 population)
  let second := PlainCallAdmission64.invocations static batch.pre.1
    (PlainCallWitness64.slot1 population)
  obtain ⟨execution⟩ := PlainCallWitness64.closed_overlap static batch.pre.1 batch.pre.2
    population choices
  exact ⟨{
    batch := batch
    population := population
    sameCell := sameCell
    initialHighWord := initialHighWord
    storeHighWords := storeHighWords
    actions := X86.VCGen.PlainMethods.overlapActions first second (choices 0) (choices 1) ++
      execution.suffix
    actual := execution.actual
    scheduled := execution.scheduled
    finished := execution.finished
    post := execution.post
    overlap := ⟨PlainCallWitness64.slot0 population, PlainCallWitness64.slot1 population,
      PlainCallWitness64.slots_distinct population, execution.overlap⟩ }⟩

end EDSL.Corpus.Plain

namespace EDSL.Corpus.PlainWitnesses
open X86 OS OS.TSO64 Grading.ConcurrentTask.Plain64
open PlainResources

abbrev Compiler := V1.PlainInputs.Compiler

def homogeneousShapes (compiler : Compiler) (kind : Kind) :
    PlainCallAdmission64.StaticShapes [(V1.PlainInputs.named compiler kind).site] :=
  Plain.singletonShapes (V1.PlainInputs.staticShapes compiler) (V1.PlainInputs.site compiler kind)
    (by cases kind <;> simp [V1.PlainInputs.catalog])

private theorem cohort_target {original : AddressSpace.Space} {catalog : Catalog} {layout : Layout}
    {old : Word} {first second : Choice} (current : Cohort original catalog layout old first second)
    (tid : Fin current.state.workers.length) :
    (current.inputs tid).target = current.resources.target := by
  unfold Cohort.inputs pairInputs
  split <;> exact input_target _ _ _

/-- A single resource proof covers either kind in either compiler's unchanged
complete ELF. No schedule, final position, result or history is a premise.
Counters and logical occurrences are independent and unrestricted. -/
theorem homogeneous (compiler : Compiler) (kind : Kind) (old valueA valueB : Word)
    (counterA counterB occurrenceA occurrenceB : Nat)
    (oldHigh : 2^32 ≤ old.toNat) (firstHigh : 2^32 ≤ valueA.toNat)
    (secondHigh : 2^32 ≤ valueB.toNat)
    (choices : Nat → Nat → Bool := fun _ _ => false) :
    Nonempty (Plain.UsefulNamed (V1.PlainInputs.named compiler kind)) := by
  let current := Inputs.cohort compiler kind kind old valueA valueB
    counterA counterB occurrenceA occurrenceB
  let batch := Inputs.homogeneous compiler kind old valueA valueB
    counterA counterB occurrenceA occurrenceB
  have population : batch.before.workers.length = 2 := rfl
  refine Plain.usefulNamed batch (homogeneousShapes compiler kind) population ?_ ?_ ?_ choices
  · intro i j
    change (current.inputs i).target = (current.inputs j).target
    exact (cohort_target current i).trans (cohort_target current j).symm
  · refine ⟨PlainCallWitness64.slot0 population, old, ?_, oldHigh⟩
    change loadQWord (published current.state.world)
      (current.inputs (PlainCallWitness64.slot0 population)).cell.address = .ok old
    rw [Inputs.target_address]
    exact Frozen.initial_read compiler (Inputs.windowKind kind) (Inputs.windowKind kind) old
  · intro tid kindStore
    change kind = .storeRelease at kindStore
    subst kind
    change ∃ value, (current.inputs tid).request =
      .storeRelease (current.inputs tid).target value ∧ 2^32 ≤ value.toNat
    unfold Cohort.inputs pairInputs
    by_cases first : tid.val = 0
    · simp only [first, ite_true]
      exact ⟨valueA, rfl, firstHigh⟩
    · simp only [first, ite_false]
      exact ⟨valueB, rfl, secondHigh⟩

def highInitial : Word := 0x100000001
def highStoreA : Word := 0x200000003
def highStoreB : Word := 0x300000005

theorem highInitial_above32 : 2^32 < highInitial.toNat := by decide
theorem highStoreA_above32 : 2^32 < highStoreA.toNat := by decide
theorem highStoreB_above32 : 2^32 < highStoreB.toNat := by decide

/-- Full64 instances for every compiler/kind and arbitrary labels, including
all nonzero choices. No compiler-specific execution or byte case is needed. -/
theorem high_homogeneous (compiler : Compiler) (kind : Kind)
    (counterA counterB occurrenceA occurrenceB : Nat)
    (choices : Nat → Nat → Bool := fun _ _ => false) :
    Nonempty (Plain.UsefulNamed (V1.PlainInputs.named compiler kind)) :=
  homogeneous compiler kind highInitial highStoreA highStoreB
    counterA counterB occurrenceA occurrenceB
    (Nat.le_of_lt highInitial_above32) (Nat.le_of_lt highStoreA_above32)
    (Nat.le_of_lt highStoreB_above32) choices

/-- Attach the unchanged universal claim only after constructing the useful
resource/run inhabitant. This remains the existing named certificate gate. -/
def namedCertificate (compiler : Compiler) (kind : Kind)
    (counterA counterB occurrenceA occurrenceB : Nat) :
    Plain.NamedCertificate kind (V1.PlainWindows.file compiler) where
  named := V1.PlainInputs.named compiler kind
  registeredKind := rfl
  claim := V1.PlainClaims.named compiler kind
  inhabited := high_homogeneous compiler kind counterA counterB occurrenceA occurrenceB

def gcc (kind : Kind) : Plain.NamedCertificate kind (V1.PlainWindows.file .defaultGCC) :=
  namedCertificate .defaultGCC kind 17 29 101 202

def clang (kind : Kind) : Plain.NamedCertificate kind (V1.PlainWindows.file .defaultClang) :=
  namedCertificate .defaultClang kind 17 29 101 202

end EDSL.Corpus.PlainWitnesses

#audit_edsl
