/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallWitness64.Overlap
import EDSL.OS.PlainCallWitness64.Publication

/-!
Construct a mixed execution with publication between the writer's RET and the
reader's MOV64 access. The original writer runs its complete issue-only block.
Production drain closure then empties the actual FIFOs before any reader issue;
production cohort completion and closure finish the remaining workers.

The independent closed Post and its actual buffered publication are outputs.
Its writer and reader positions are identified from actual dispatch/response
observations, and the stamp bounds follow from the real intermediate quiet cut.
No desired source, reads-from edge, stamp position or future success is assumed.

The present Pre, static instruction shapes, fixed population, initial empty
FIFOs and the original method environmental assumptions remain explicit. This
constructs one finite modeled execution, without a fairness or physical claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.OS.PlainCallWitness64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open X86.VCGen PlainMethods

/-- The original worker 0 executes its padding, MOV64 and real RET. -/
def writerActions {before : TSO64.State} (writer : Invocation before 0)
    (choices : Nat → Bool) : List Action :=
  remainingIssues 0 (writer.padding.length + 2) choices

/-- The drain list is computed from the actual state after writer completion. -/
def mixedPrefixActions {before : TSO64.State} (writer : Invocation before 0)
    (choices : Nat → Bool) (writerResult : TSO64.State × List Observation) : List Action :=
  writerActions writer choices ++ DrainClosure.actions writerResult.1

private theorem remainingIssues_take (tid count cut : Nat) (choices : Nat → Bool)
    (within : cut ≤ count) :
    (remainingIssues tid count choices).take cut = remainingIssues tid cut choices := by
  unfold remainingIssues
  rw [← List.map_take, List.take_range, Nat.min_eq_left within]

/-- Positions belong to this independent Post. Its own-issue counts identify
both writer operations; the actual drain-only block excludes a reader issue
before the quiet cut. No completed-call record equality is required. -/
theorem mixed_post_positions {before : TSO64.State}
    {inputs : Fin before.workers.length → Input}
    (population : before.workers.length = 2) (writer : Invocation before 0)
    (choices : Nat → Bool) {drains suffix : List Action}
    (onlyDrains : DrainClosure.DrainOnly drains)
    {actual : TSO64.State × List Observation}
    (post : Post before inputs ((writerActions writer choices ++ drains) ++ suffix) actual) :
    (post.outcomes (slot0 population)).performed = writer.padding.length ∧
      (post.outcomes (slot0 population)).returned = writer.padding.length + 1 ∧
      (writerActions writer choices ++ drains).length ≤
        (post.outcomes (slot1 population)).performed := by
  let p := writer.padding.length
  let block := writerActions writer choices
  have blockLength : block.length = p + 2 := remainingIssues_length _ _ _
  have prefixLength : (block ++ drains).length = p + 2 + drains.length := by
    rw [List.length_append, blockLength]
  have selected (index : Nat) (within : index < p + 2) :
      ((block ++ drains) ++ suffix)[index]? = some (.issue 0 (choices index)) := by
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact remainingIssues_at 0 (p + 2) index choices within
  have preceding (index : Nat) (within : index ≤ p + 2) :
      AtomicMethods.ownIssues 0 (((block ++ drains) ++ suffix).take index) = index := by
    rw [List.take_append_of_le_length (by omega),
      List.take_append_of_le_length (by omega)]
    change AtomicMethods.ownIssues 0 ((remainingIssues 0 (p + 2) choices).take index) = index
    rw [remainingIssues_take 0 (p + 2) index choices within, remainingIssues_ownIssues]
  obtain ⟨performedCount, returnedCount⟩ :=
    outcome_ownIssues writer (post.outcomes (slot0 population)) post.scheduled
  obtain ⟨_performedAF, performedAt⟩ := outcome_performed_issue (post.outcomes (slot0 population))
  obtain ⟨_returnedAF, returnedAt⟩ := outcome_returned_issue (post.outcomes (slot0 population))
  have performed : (post.outcomes (slot0 population)).performed = p :=
    own_issue_index_unique performedAt (selected p (by omega))
      (performedCount.trans (preceding p (by omega)).symm)
  have returned : (post.outcomes (slot0 population)).returned = p + 1 :=
    own_issue_index_unique returnedAt (selected (p + 1) (by omega))
      (returnedCount.trans (preceding (p + 1) (by omega)).symm)
  have readerAfter : (block ++ drains).length ≤
      (post.outcomes (slot1 population)).performed := by
    obtain ⟨readerAF, readerAt⟩ := outcome_performed_issue (post.outcomes (slot1 population))
    apply Nat.le_of_not_gt
    intro inside
    have member : Action.issue 1 readerAF ∈ block ++ drains := by
      have selected : (block ++ drains)[(post.outcomes (slot1 population)).performed]? =
          some (.issue 1 readerAF) := by
        rw [← List.getElem?_append_left inside (l₂ := suffix)]
        exact readerAt
      exact List.mem_of_getElem? selected
    rcases List.mem_append.mp member with inWriter | inDrains
    · obtain ⟨_af, impossible⟩ := remainingIssues_only 0 (p + 2) choices
        (.issue 1 readerAF) inWriter
      cases impossible
    · obtain ⟨_tid, impossible⟩ := onlyDrains (.issue 1 readerAF) inDrains
      cases impossible
  exact ⟨performed, returned, readerAfter⟩

/-- Actual writer completion, actual middle FIFO closure and a finished
extension. The publication belongs to the same Post and the same full run. -/
structure ClosedMixed {before : TSO64.State} (inputs : Fin before.workers.length → Input)
    (population : before.workers.length = 2) (writer : Invocation before 0)
    (choices : Nat → Bool) where
  writerResult : TSO64.State × List Observation
  writerRun : schedule before (writerActions writer choices) .sharedCell = .ok writerResult
  drainResult : TSO64.State × List Observation
  drained : DrainClosure.Certificate writerResult.1 drainResult .sharedCell
  prefixRun : schedule before (mixedPrefixActions writer choices writerResult) .sharedCell =
    .ok (drainResult.1, writerResult.2 ++ drainResult.2)
  suffix : List Action
  actual : TSO64.State × List Observation
  scheduled : schedule before (mixedPrefixActions writer choices writerResult ++ suffix)
    .sharedCell = .ok actual
  finished : Finished actual.1
  post : ClosedPost before inputs
    (mixedPrefixActions writer choices writerResult ++ suffix) actual 0
  performedWriter : (post.calls.outcomes (slot0 population)).performed = writer.padding.length
  returnedWriter : (post.calls.outcomes (slot0 population)).returned = writer.padding.length + 1
  readerAfterCut : (mixedPrefixActions writer choices writerResult).length ≤
    (post.calls.outcomes (slot1 population)).performed
  stamp : PublishedHistory.Stamp
  stampMember : stamp ∈ C23Projection.writes 0 actual.2
  publication : C23Projection.AtomicTrace.Graph.Publication
    ((post.calls.outcomes (slot0 population)).machineEvent (post.sources (slot0 population)) 0)
    stamp
  stampAfterIssues : (writerActions writer choices).length ≤ stamp.position
  stampBeforeCut : stamp.position < (mixedPrefixActions writer choices writerResult).length
  returnedBeforeStamp : (post.calls.outcomes (slot0 population)).returned < stamp.position
  stampBeforeReader : stamp.position < (post.calls.outcomes (slot1 population)).performed

/-- Every schedule result, closed Post and publication is constructed from
present independent admission. The two original methods may have different
padding and resources. Full64 words, counters and logical occurrences remain
arbitrary. The reader's actual source and graph edge are left for the separate
history lemmas; they are not assumptions of this construction. -/
theorem closed_mixed {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (initialEmpty : Quiescent before)
    (population : before.workers.length = 2)
    (writing : (inputs (slot0 population)).site.kind = .storeRelease)
    (choices : Nat → Nat → Bool) :
    Nonempty (ClosedMixed inputs population
      (PlainCallAdmission64.invocations static pre (slot0 population)) (choices 0)) := by
  let invocations := PlainCallAdmission64.invocations static pre
  let writer : Invocation before 0 := invocations (slot0 population)
  obtain ⟨actions, writerResult, _after, _reply, planned, _length, _only, runWriter,
      _writerLive, _writerDone⟩ :=
    complete writer.current writer.live writer.entry (choices 0)
  have writerRun : schedule before (writerActions writer (choices 0)) .sharedCell =
      .ok writerResult := by
    simpa only [planned, writerActions, remainingIssues, Point.remaining] using runWriter
  obtain ⟨drainResult, _drainRun, drained⟩ :=
    DrainClosure.drainAll_complete (schedule_wellFormed pre.valid writerRun)
  let middlePrefix := mixedPrefixActions writer (choices 0) writerResult
  let prefixResult : TSO64.State × List Observation :=
    (drainResult.1, writerResult.2 ++ drainResult.2)
  have prefixRun : schedule before middlePrefix .sharedCell = .ok prefixResult :=
    completion_schedule_append writerRun drained.scheduled
  obtain ⟨cuts, returned, closed, _completion, _drained, _certificate,
      scheduled, finished, _responses⟩ :=
    cohort_closed_after_prefix invocations pre.valid prefixRun choices
  let suffix := cohortActions (fun tid => (cuts tid).cut.point) choices ++
    DrainClosure.actions returned.1
  let actual : TSO64.State × List Observation :=
    (closed.1, prefixResult.2 ++ (returned.2 ++ closed.2))
  have full : schedule before (middlePrefix ++ suffix) .sharedCell = .ok actual := scheduled
  obtain ⟨post⟩ := PlainCallClosed64.post static ⟨pre, initialEmpty⟩ full finished
  obtain ⟨performedWriter, returnedWriter, readerAfterCut⟩ :=
    mixed_post_positions population writer (choices 0) drained.drainOnly post.calls
  change middlePrefix.length ≤ (post.calls.outcomes (slot1 population)).performed
    at readerAfterCut
  have writerLength : (writerActions writer (choices 0)).length = writer.padding.length + 2 :=
    remainingIssues_length _ _ _
  have prefixLength : middlePrefix.length = (writerActions writer (choices 0)).length +
      (DrainClosure.actions writerResult.1).length := by
    change (writerActions writer (choices 0) ++ DrainClosure.actions writerResult.1).length = _
    exact List.length_append
  have earlier : (post.calls.outcomes (slot0 population)).performed < middlePrefix.length := by
    omega
  have quietPrefix : schedule before ((middlePrefix ++ suffix).take middlePrefix.length) .sharedCell =
      .ok prefixResult := by
    rw [List.take_append_length]
    exact prefixRun
  have initialIssueOnly :
      ∀ action ∈ (middlePrefix ++ suffix).take (writerActions writer (choices 0)).length,
        ∃ issuer af, action = .issue issuer af := by
    intro action member
    have takeWriter :
        (middlePrefix ++ suffix).take (writerActions writer (choices 0)).length =
          writerActions writer (choices 0) := by
      rw [List.take_append_of_le_length (by omega)]
      exact List.take_append_length
    rw [takeWriter] at member
    obtain ⟨af, own⟩ := remainingIssues_only 0 (writer.padding.length + 2) (choices 0) action member
    exact ⟨0, af, own⟩
  obtain ⟨stamp, member, publication, afterIssues, beforeCut⟩ :=
    post.store_published_between_cuts (slot0 population) writing earlier quietPrefix
      drained.quiescent initialIssueOnly
  have returnedBefore : (post.calls.outcomes (slot0 population)).returned < stamp.position := by
    omega
  have beforeReader : stamp.position < (post.calls.outcomes (slot1 population)).performed := by
    omega
  exact ⟨{
    writerResult := writerResult
    writerRun := writerRun
    drainResult := drainResult
    drained := drained
    prefixRun := prefixRun
    suffix := suffix
    actual := actual
    scheduled := full
    finished := finished
    post := post
    performedWriter := performedWriter
    returnedWriter := returnedWriter
    readerAfterCut := readerAfterCut
    stamp := stamp
    stampMember := member
    publication := publication
    stampAfterIssues := afterIssues
    stampBeforeCut := beforeCut
    returnedBeforeStamp := returnedBefore
    stampBeforeReader := beforeReader }⟩

end EDSL.OS.PlainCallWitness64

#audit_edsl
