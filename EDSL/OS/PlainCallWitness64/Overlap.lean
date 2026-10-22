/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Overlap
import EDSL.OS.PlainCallClosed64

/-!
Construct an overlapping finished execution from independent present admission.
The original invocations at slots 0 and 1 each run their padding and MOV64,
leaving both workers at their real RETs. Production cohort completion and drain
closure finish that prefix; the independent closed Post is then derived.

The position bridge uses that Post's own dispatch and response observations.
Equal preceding own-issue counts identify the two actual access positions;
strict growth across an own issue excludes either RET from the prefix. No
desired Post, future position, reply, graph or history is an input.

Initial quiescence is the existing closed-Post boundary. The independent Pre
retains scalar RAM, managed authority, stable translation/no hidden aliases,
protected original callers/code, long mode, CET off and fixed worker population.
This is finite modeled execution, without fairness or physical/compiler claims.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.OS.PlainCallWitness64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open X86.VCGen PlainMethods

def slot0 {n : Nat} (population : n = 2) : Fin n := ⟨0, by omega⟩

def slot1 {n : Nat} (population : n = 2) : Fin n := ⟨1, by omega⟩

theorem slots_distinct {n : Nat} (population : n = 2) :
    slot0 population ≠ slot1 population := by
  intro same
  have values := congrArg Fin.val same
  change (0 : Nat) = 1 at values
  omega

/-- These counts concern the independently returned Outcome itself. -/
theorem outcome_ownIssues {before : TSO64.State} {input : Input} {tid : Nat}
    (invocation : Invocation before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (outcome : Outcome input before actions actual tid)
    (success : schedule before actions .sharedCell = .ok actual) :
    AtomicMethods.ownIssues tid (actions.take outcome.performed) = invocation.padding.length ∧
      AtomicMethods.ownIssues tid (actions.take outcome.returned) =
        invocation.padding.length + 1 := by
  exact ⟨invocation.dispatched_ownIssues success
      (PlainCallBehavior64.data_access_dispatched outcome.dispatched),
    invocation.returned_ownIssues success
      (outcome.responseBoundary.observed.trans (congrArg some outcome.responseObserved))⟩

theorem outcome_performed_issue {before : TSO64.State} {input : Input} {tid : Nat}
    {actions : List Action} {actual : TSO64.State × List Observation}
    (outcome : Outcome input before actions actual tid) :
    ∃ af, actions[outcome.performed]? = some (.issue tid af) := by
  obtain ⟨boundary, _worker, _instruction, af, issued, _⟩ := outcome.dispatched
  exact ⟨af, boundary.selected.trans (congrArg some issued)⟩

theorem outcome_returned_issue {before : TSO64.State} {input : Input} {tid : Nat}
    {actions : List Action} {actual : TSO64.State × List Observation}
    (outcome : Outcome input before actions actual tid) :
    ∃ af, actions[outcome.returned]? = some (.issue tid af) := by
  obtain ⟨af, _worker, _output, _observation, issued, _⟩ := outcome.response
  exact ⟨af, outcome.responseBoundary.selected.trans (congrArg some issued)⟩

private theorem ownIssues_append (tid : Nat) (first second : List Action) :
    AtomicMethods.ownIssues tid (first ++ second) =
      AtomicMethods.ownIssues tid first + AtomicMethods.ownIssues tid second := by
  induction first with
  | nil => simp only [List.nil_append, AtomicMethods.ownIssues, Nat.zero_add]
  | cons action rest ih =>
    simp only [List.cons_append, AtomicMethods.ownIssues, ih, Nat.add_assoc]

private theorem remainingIssues_peer (tid peer count : Nat) (choices : Nat → Bool)
    (different : tid ≠ peer) :
    AtomicMethods.ownIssues peer (remainingIssues tid count choices) = 0 := by
  induction count generalizing choices with
  | zero => rfl
  | succ count ih =>
    rw [remainingIssues_succ]
    simp only [AtomicMethods.ownIssues, AtomicMethods.ownIssue, ite_eq_right different,
      Nat.zero_add, ih]

private theorem remainingIssues_take (tid count cut : Nat) (choices : Nat → Bool)
    (within : cut ≤ count) :
    (remainingIssues tid count choices).take cut = remainingIssues tid cut choices := by
  unfold remainingIssues
  rw [← List.map_take, List.take_range, Nat.min_eq_left within]

/-- Exact positions of any independent Post for the two blocks plus any
successful suffix. No equality with an engine completed-call record is used.
The return bounds follow from own-issue strictness, including when padding is
empty or the suffix interleaves issues and drains. -/
theorem overlap_post_positions {before : TSO64.State}
    {inputs : Fin before.workers.length → Input}
    (population : before.workers.length = 2)
    (first : Invocation before 0) (second : Invocation before 1)
    (firstAF secondAF : Nat → Bool) {suffix : List Action}
    {actual : TSO64.State × List Observation}
    (post : Post before inputs (overlapActions first second firstAF secondAF ++ suffix) actual) :
    (post.outcomes (slot0 population)).performed = first.padding.length ∧
      (post.outcomes (slot1 population)).performed =
        first.padding.length + 1 + second.padding.length ∧
      (overlapActions first second firstAF secondAF).length ≤
        (post.outcomes (slot0 population)).returned ∧
      (overlapActions first second firstAF secondAF).length ≤
        (post.outcomes (slot1 population)).returned := by
  let p := first.padding.length
  let q := second.padding.length
  let block0 := remainingIssues 0 (p + 1) firstAF
  let block1 := remainingIssues 1 (q + 1) secondAF
  let accessPrefix := block0 ++ block1
  have length0 : block0.length = p + 1 := remainingIssues_length _ _ _
  have length1 : block1.length = q + 1 := remainingIssues_length _ _ _
  have lengthPrefix : accessPrefix.length = p + 1 + (q + 1) := by
    change (block0 ++ block1).length = _
    rw [List.length_append, length0, length1]
  have selected0 : (accessPrefix ++ suffix)[p]? = some (.issue 0 (firstAF p)) := by
    rw [List.getElem?_append_left (by omega)]
    change (block0 ++ block1)[p]? = _
    rw [List.getElem?_append_left (by omega)]
    exact remainingIssues_at 0 (p + 1) p firstAF (by omega)
  have selected1 : (accessPrefix ++ suffix)[p + 1 + q]? = some (.issue 1 (secondAF q)) := by
    rw [List.getElem?_append_left (by omega)]
    change (block0 ++ block1)[p + 1 + q]? = _
    rw [List.getElem?_append_right (by omega), length0, Nat.add_sub_cancel_left]
    exact remainingIssues_at 1 (q + 1) q secondAF (by omega)
  have preceding0 : AtomicMethods.ownIssues 0 ((accessPrefix ++ suffix).take p) = p := by
    rw [List.take_append_of_le_length (by omega)]
    change AtomicMethods.ownIssues 0 ((block0 ++ block1).take p) = p
    rw [List.take_append_of_le_length (by omega)]
    change AtomicMethods.ownIssues 0 ((remainingIssues 0 (p + 1) firstAF).take p) = p
    rw [remainingIssues_take 0 (p + 1) p firstAF (by omega), remainingIssues_ownIssues]
  have preceding1 : AtomicMethods.ownIssues 1 ((accessPrefix ++ suffix).take (p + 1 + q)) = q := by
    rw [List.take_append_of_le_length (by omega)]
    change AtomicMethods.ownIssues 1 ((block0 ++ block1).take (p + 1 + q)) = q
    have offset : p + 1 + q = block0.length + q := by omega
    rw [offset, List.take_length_add_append, ownIssues_append]
    rw [remainingIssues_peer 0 1 (p + 1) firstAF (by omega), Nat.zero_add]
    change AtomicMethods.ownIssues 1 ((remainingIssues 1 (q + 1) secondAF).take q) = q
    rw [remainingIssues_take 1 (q + 1) q secondAF (by omega), remainingIssues_ownIssues]
  have total0 : AtomicMethods.ownIssues 0 accessPrefix = p + 1 := by
    change AtomicMethods.ownIssues 0 (block0 ++ block1) = p + 1
    rw [ownIssues_append, remainingIssues_ownIssues,
      remainingIssues_peer 1 0 (q + 1) secondAF (by omega), Nat.add_zero]
  have total1 : AtomicMethods.ownIssues 1 accessPrefix = q + 1 := by
    change AtomicMethods.ownIssues 1 (block0 ++ block1) = q + 1
    rw [ownIssues_append, remainingIssues_peer 0 1 (p + 1) firstAF (by omega),
      remainingIssues_ownIssues, Nat.zero_add]
  obtain ⟨count0, returnCount0⟩ :=
    outcome_ownIssues first (post.outcomes (slot0 population)) post.scheduled
  obtain ⟨count1, returnCount1⟩ :=
    outcome_ownIssues second (post.outcomes (slot1 population)) post.scheduled
  change AtomicMethods.ownIssues 0 ((accessPrefix ++ suffix).take
    (post.outcomes (slot0 population)).returned) = p + 1 at returnCount0
  change AtomicMethods.ownIssues 1 ((accessPrefix ++ suffix).take
    (post.outcomes (slot1 population)).returned) = q + 1 at returnCount1
  obtain ⟨_af0, actual0⟩ := outcome_performed_issue (post.outcomes (slot0 population))
  obtain ⟨_af1, actual1⟩ := outcome_performed_issue (post.outcomes (slot1 population))
  have position0 : (post.outcomes (slot0 population)).performed = p :=
    own_issue_index_unique actual0 selected0 (count0.trans preceding0.symm)
  have position1 : (post.outcomes (slot1 population)).performed = p + 1 + q :=
    own_issue_index_unique actual1 selected1 (count1.trans preceding1.symm)
  obtain ⟨_returnAF0, returnedAt0⟩ := outcome_returned_issue (post.outcomes (slot0 population))
  obtain ⟨_returnAF1, returnedAt1⟩ := outcome_returned_issue (post.outcomes (slot1 population))
  have return0 : accessPrefix.length ≤ (post.outcomes (slot0 population)).returned := by
    apply Nat.le_of_not_gt
    intro inside
    have strict := own_issue_count_lt_of_lt returnedAt0 inside
    change AtomicMethods.ownIssues 0 ((accessPrefix ++ suffix).take
      (post.outcomes (slot0 population)).returned) <
      AtomicMethods.ownIssues 0 ((accessPrefix ++ suffix).take accessPrefix.length) at strict
    rw [returnCount0, List.take_append_length, total0] at strict
    omega
  have return1 : accessPrefix.length ≤ (post.outcomes (slot1 population)).returned := by
    apply Nat.le_of_not_gt
    intro inside
    have strict := own_issue_count_lt_of_lt returnedAt1 inside
    change AtomicMethods.ownIssues 1 ((accessPrefix ++ suffix).take
      (post.outcomes (slot1 population)).returned) <
      AtomicMethods.ownIssues 1 ((accessPrefix ++ suffix).take accessPrefix.length) at strict
    rw [returnCount1, List.take_append_length, total1] at strict
    omega
  exact ⟨position0, position1, return0, return1⟩

/-- Retains the actual two blocks, including both final RET locations, plus
the finished extension and its independently derived complete closed Post. -/
structure ClosedOverlap {before : TSO64.State} (inputs : Fin before.workers.length → Input)
    (population : before.workers.length = 2)
    (first : Invocation before 0) (second : Invocation before 1)
    (firstAF secondAF : Nat → Bool) where
  accessPrefix : PlainMethods.Overlap first second firstAF secondAF
  suffix : List Action
  actual : TSO64.State × List Observation
  scheduled : schedule before (overlapActions first second firstAF secondAF ++ suffix)
    .sharedCell = .ok actual
  finished : Finished actual.1
  post : ClosedPost before inputs (overlapActions first second firstAF secondAF ++ suffix) actual
  performed0 : (post.calls.outcomes (slot0 population)).performed = first.padding.length
  performed1 : (post.calls.outcomes (slot1 population)).performed =
    first.padding.length + 1 + second.padding.length
  returned0 : (overlapActions first second firstAF secondAF).length ≤
    (post.calls.outcomes (slot0 population)).returned
  returned1 : (overlapActions first second firstAF secondAF).length ≤
    (post.calls.outcomes (slot1 population)).returned

theorem ClosedOverlap.overlap {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {population : before.workers.length = 2}
    {first : Invocation before 0} {second : Invocation before 1}
    {firstAF secondAF : Nat → Bool}
    (execution : ClosedOverlap inputs population first second firstAF secondAF) :
    (execution.post.calls.outcomes (slot0 population)).performed <
        (execution.post.calls.outcomes (slot1 population)).performed ∧
      (execution.post.calls.outcomes (slot1 population)).performed <
        (execution.post.calls.outcomes (slot0 population)).returned ∧
      (execution.post.calls.outcomes (slot1 population)).performed <
        (execution.post.calls.outcomes (slot1 population)).returned := by
  have lengthPrefix : (overlapActions first second firstAF secondAF).length =
      first.padding.length + 1 + (second.padding.length + 1) := by
    simp only [overlapActions, List.length_append, remainingIssues_length]
  have firstPosition := execution.performed0
  have secondPosition := execution.performed1
  have firstReturn := execution.returned0
  have secondReturn := execution.returned1
  omega

/-- Coverage and population transport the two strict own-count bounds to
every actual RET observation, including responses identified independently. -/
theorem ClosedOverlap.no_return_in_prefix {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} {population : before.workers.length = 2}
    {first : Invocation before 0} {second : Invocation before 1}
    {firstAF secondAF : Nat → Bool}
    (execution : ClosedOverlap inputs population first second firstAF secondAF)
    (index tid : Nat) (inside : index < (overlapActions first second firstAF secondAF).length) :
    execution.actual.2[index]? ≠ some (.returned tid) := by
  intro observed
  obtain ⟨slot, _thread, position⟩ := execution.post.calls.allReturns tid index observed
  have alternatives : slot = slot0 population ∨ slot = slot1 population := by
    have bound := slot.isLt
    have values : slot.val = 0 ∨ slot.val = 1 := by omega
    rcases values with zero | one
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext one)
  rcases alternatives with rfl | rfl
  · have afterPrefix := execution.returned0
    omega
  · have afterPrefix := execution.returned1
    omega

/-- All dynamic objects are outputs. The only premises are independent
present admission, initial empty FIFOs, static byte shapes and population 2.
The same original admitted invocations construct the prefix and feed the
production completion theorem; arbitrary AF choices are retained. -/
theorem closed_overlap {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (initialEmpty : Quiescent before)
    (population : before.workers.length = 2) (choices : Nat → Nat → Bool) :
    Nonempty (ClosedOverlap inputs population
      (PlainCallAdmission64.invocations static pre (slot0 population))
      (PlainCallAdmission64.invocations static pre (slot1 population))
      (choices 0) (choices 1)) := by
  let invocations := PlainCallAdmission64.invocations static pre
  let first : Invocation before 0 := invocations (slot0 population)
  let second : Invocation before 1 := invocations (slot1 population)
  obtain ⟨accessPrefix⟩ := overlap_prefixes first second (choices 0) (choices 1)
  obtain ⟨cuts, returned, closed, _completion, _drained, _certificate,
      scheduled, finished, _responses⟩ :=
    cohort_closed_after_prefix invocations pre.valid accessPrefix.actual choices
  let suffix := cohortActions (fun tid => (cuts tid).cut.point) choices ++
    DrainClosure.actions returned.1
  let actual : TSO64.State × List Observation :=
    (closed.1, accessPrefix.result.2 ++ (returned.2 ++ closed.2))
  have full : schedule before (overlapActions first second (choices 0) (choices 1) ++ suffix)
      .sharedCell = .ok actual := scheduled
  obtain ⟨post⟩ := PlainCallClosed64.post static ⟨pre, initialEmpty⟩ full finished
  obtain ⟨performed0, performed1, returned0, returned1⟩ :=
    overlap_post_positions population first second (choices 0) (choices 1) post.calls
  exact ⟨{
    accessPrefix := accessPrefix
    suffix := suffix
    actual := actual
    scheduled := full
    finished := finished
    post := post
    performed0 := performed0
    performed1 := performed1
    returned0 := returned0
    returned1 := returned1 }⟩

end EDSL.OS.PlainCallWitness64

#audit_edsl
