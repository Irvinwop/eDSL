/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterGCC
import EDSL.Corpus.V1.CounterClang
import EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Construct a cohort directly from independently admitted frozen counter calls.
Each subject selects its checked GCC or Clang annotation from current input
data. Clients provide present slot coverage and initial empty queues; they do
not supply generated blocks, future no-enqueue facts or successful completion
as admission. The resulting closure is generic in the collection's index type.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Select the existing checked annotation using only present call admission. -/
def checkedAnnotations {c : Compiler} {site : Site c} {call : Call} {initial : S}
    (pre : Pre site call initial) : Mixed.Annotations (descriptor site call) (Post site call) := by
  cases c with
  | defaultGCC => exact CounterGCC.annotations site call pre.callerCanonical
  | defaultClang => exact CounterClang.annotations site call pre.callerCanonical pre.stack

/-- Admission initializes the selected annotation without a future-run premise. -/
theorem checkedEntry {c : Compiler} {site : Site c} {call : Call} {initial : S}
    (pre : Pre site call initial) :
    ∃ node, Mixed.Entry (checkedAnnotations pre) initial node := by
  cases c with
  | defaultGCC => exact ⟨_, CounterGCC.entry_of_pre pre⟩
  | defaultClang => exact ⟨_, CounterClang.entry_of_pre pre⟩

/-- One presently admitted worker; compiler and scheduler slot are explicit.
Resource actors and managed targets remain those independently named by Pre. -/
structure CohortSubject (initial : S) where
  compiler : Compiler
  site : Site compiler
  call : Call
  pre : Pre site call initial
  ownedOnly : site.profile = .ownedOnly

/-- Any collection of admitted calls supplies all local rules and policy laws.
Exhaustive slot coverage and initial empty FIFOs remain separate current inputs. -/
def counterCohort {ι : Type} {initial : S} (subjects : ι → CohortSubject initial) :
    Mixed.Cohort ι .ownedOnly .arithmetic where
  descriptor subject := descriptor (subjects subject).site (subjects subject).call
  post subject := Post (subjects subject).site (subjects subject).call
  annotations subject := checkedAnnotations (subjects subject).pre
  profile_eq subject := (subjects subject).ownedOnly
  family_eq _subject := rfl
  callerPolicy subject state :=
    descriptor_policy (subjects subject).site (subjects subject).call state

/-- The initial Entries follow from the actual GCC/Clang proofs for every call. -/
theorem counterCohort_entries {ι : Type} {initial : S}
    (subjects : ι → CohortSubject initial) : (counterCohort subjects).Entries initial :=
  fun subject => checkedEntry (subjects subject).pre

/-- A successful actual run of an exhaustively covered counter cohort with
empty initial FIFOs retains empty FIFOs and checked current relatedness; every
original action/observation position is an ordinary, RET or native RMW issue.
This does not establish completion, resource release or a final counter sum. -/
theorem counterCohort_closed {ι : Type} {initial final : S}
    (subjects : ι → CohortSubject initial)
    (covered : (counterCohort subjects).Covers initial) (empty : Quiescent initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations)) :
    Quiescent final ∧ (counterCohort subjects).Covers final ∧
      (counterCohort subjects).Current initial final ∧
      (counterCohort subjects).RetirementTrace actions observations :=
  (counterCohort subjects).schedule covered (counterCohort_entries subjects) empty actual

#print axioms checkedAnnotations
#print axioms checkedEntry
#print axioms CohortSubject
#print axioms counterCohort
#print axioms counterCohort_entries
#print axioms counterCohort_closed

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
