/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Completion
import EDSL.OS.PlainCallProgress64
import EDSL.OS.PlainCallBehavior64

/-!
Construct chosen finite completions from independent present admission and an
actual successful prefix. The shared engine derives current points and exact
remaining counts, including zero for already-returned workers and saved replies.
Thread-local AF indexing is proved for the actual issue-only suffix. Publication
closure separately appends production drains and preserves CPU responses.
There is no fairness, native/source correspondence or corpus certificate claim.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallCompletion64
open X86 TSO64 Grading.ConcurrentTask.Plain64 X86.VCGen

theorem issues_append (tid : Nat) (first second : List Action) :
    issues tid (first ++ second) = issues tid first + issues tid second := by
  simp only [issues, List.filter_append, List.length_append]

/-- Count a list known to consist entirely of this worker's own issues. -/
theorem issues_of_only {tid : Nat} {actions : List Action}
    (only : ∀ action ∈ actions, ∃ af, action = .issue tid af) :
    issues tid actions = actions.length := by
  unfold issues
  have filtered : actions.filter (fun action => match action with
      | .issue thread _ => decide (thread = tid)
      | .drain _ => false) = actions := by
    apply List.filter_eq_self.mpr
    intro action member
    obtain ⟨af, rfl⟩ := only action member
    simp
  exact congrArg List.length filtered

theorem issues_of_absent {tid : Nat} {actions : List Action}
    (absent : ∀ af, Action.issue tid af ∉ actions) : issues tid actions = 0 := by
  unfold issues
  have filtered : actions.filter (fun action => match action with
      | .issue thread _ => decide (thread = tid)
      | .drain _ => false) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro action member
    cases action with
    | issue thread af =>
      have different : thread ≠ tid := by
        intro same
        subst thread
        exact absent af member
      simpa only [decide_eq_true_eq] using different
    | drain thread =>
      intro impossible
      cases impossible
  exact congrArg List.length filtered

/-- Concatenating disjoint-thread plans retains suffix-local own AF indices. -/
theorem chosen_append {choices : Nat → Nat → Bool} {first second : List Action}
    (left : ChosenIssues choices first) (right : ChosenIssues choices second)
    (fresh : ∀ tid af, Action.issue tid af ∈ second → issues tid first = 0) :
    ChosenIssues choices (first ++ second) := by
  constructor
  · intro action member
    rcases List.mem_append.mp member with member | member
    · exact left.1 action member
    · exact right.1 action member
  · intro index tid af selected
    by_cases inside : index < first.length
    · have located : first[index]? = some (.issue tid af) :=
        (List.getElem?_append_left inside).symm.trans selected
      rw [List.take_append_of_le_length (Nat.le_of_lt inside)]
      exact left.2 index tid af located
    · have after : first.length ≤ index := by omega
      have located : second[index - first.length]? = some (.issue tid af) :=
        (List.getElem?_append_right after).symm.trans selected
      have noPrior : issues tid first = 0 :=
        fresh tid af (List.mem_of_getElem? located)
      rw [List.take_append, List.take_of_length_le after, issues_append, noPrior,
        Nat.zero_add]
      exact right.2 (index - first.length) tid af located

theorem remaining_only (tid count : Nat) (choices : Nat → Bool)
    {action : Action} (member : action ∈ PlainMethods.remainingIssues tid count choices) :
    ∃ af, action = .issue tid af := by
  obtain ⟨index, _within, same⟩ := List.mem_map.mp member
  exact ⟨choices index, same.symm⟩

/-- A single worker block has precisely its range index as prior own count. -/
theorem chosen_remaining (tid count : Nat) (choices : Nat → Nat → Bool) :
    ChosenIssues choices (PlainMethods.remainingIssues tid count (choices tid)) := by
  constructor
  · intro action member
    obtain ⟨af, same⟩ := remaining_only tid count (choices tid) member
    exact ⟨tid, af, same⟩
  · intro index thread af selected
    have within : index < count := by
      have bound := (List.getElem_of_getElem? selected).1
      simpa only [PlainMethods.remainingIssues_length] using bound
    have actual := PlainMethods.remainingIssues_at tid count index (choices tid) within
    have same : Action.issue tid (choices tid index) = .issue thread af :=
      Option.some.inj (actual.symm.trans selected)
    cases same
    have countPrior : issues tid
        ((PlainMethods.remainingIssues tid count (choices tid)).take index) = index := by
      rw [issues_of_only (fun action member =>
        remaining_only tid count (choices tid) (List.mem_of_mem_take member))]
      apply List.length_take_of_le
      rw [PlainMethods.remainingIssues_length]
      omega
    rw [countPrior]

/-- Every cohort action belongs to one actual listed slot. -/
theorem cohort_member {n : Nat} {operations : Fin n → PlainMethods.Operation}
    (points : (tid : Fin n) → PlainMethods.Point (operations tid))
    (slots : List (Fin n)) (choices : Nat → Nat → Bool) {action : Action}
    (member : action ∈ PlainMethods.cohortActionsFor points slots choices) :
    ∃ slot ∈ slots, ∃ af, action = .issue slot.val af := by
  obtain ⟨slot, present, inside⟩ := List.mem_flatMap.mp member
  obtain ⟨af, same⟩ := remaining_only slot.val (points slot).remaining (choices slot.val) inside
  exact ⟨slot, present, af, same⟩

/-- Distinct actual slots each occur once, so every worker's own counter starts
at zero in its only suffix block regardless of preceding peer block lengths. -/
theorem chosen_cohort_for {n : Nat} {operations : Fin n → PlainMethods.Operation}
    (points : (tid : Fin n) → PlainMethods.Point (operations tid))
    (slots : List (Fin n)) (choices : Nat → Nat → Bool) (unique : slots.Nodup) :
    ChosenIssues choices (PlainMethods.cohortActionsFor points slots choices) := by
  induction slots with
  | nil =>
    constructor
    · intro action member
      cases member
    · intro index tid af selected
      simp only [PlainMethods.cohortActionsFor, List.flatMap_nil, List.getElem?_nil] at selected
      cases selected
  | cons slot rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    change ChosenIssues choices
      (PlainMethods.remainingIssues slot.val (points slot).remaining (choices slot.val) ++
        PlainMethods.cohortActionsFor points rest choices)
    apply chosen_append (chosen_remaining slot.val (points slot).remaining choices) (ih tailUnique)
    intro tid af member
    obtain ⟨other, present, _choice, same⟩ := cohort_member points rest choices member
    have thread : tid = other.val := (Action.issue.inj same).1
    apply issues_of_absent
    intro choice incoming
    obtain ⟨_otherChoice, equal⟩ :=
      remaining_only slot.val (points slot).remaining (choices slot.val) incoming
    have sameSlot : other = slot := Fin.ext (thread.symm.trans (Action.issue.inj equal).1)
    exact absent (sameSlot ▸ present)

theorem chosen_cohort {n : Nat} {operations : Fin n → PlainMethods.Operation}
    (points : (tid : Fin n) → PlainMethods.Point (operations tid))
    (choices : Nat → Nat → Bool) :
    ChosenIssues choices (PlainMethods.cohortActions points choices) :=
  chosen_cohort_for points (List.finRange n) choices (List.nodup_finRange n)

/-- The independent count is exactly each actual recovered point's remaining
own-issue count. Drains and preceding peer blocks never contribute to it. -/
theorem issue_count {n : Nat} {methods : Fin n → PlainMethods.Method} {state : TSO64.State}
    {cuts : (tid : Fin n) → PlainMethods.CompletionCut (methods tid) tid.val state}
    {choices : Nat → Nat → Bool} {result : TSO64.State × List Observation}
    (completed : PlainMethods.CohortCompletion cuts choices result) (tid : Fin n) :
    issues tid.val (PlainMethods.cohortActions (fun slot => (cuts slot).point) choices) =
      (cuts tid).point.remaining := by
  rw [PlainCallProgress64.issues_eq]
  exact completed.issueCount tid

theorem returned_issues_zero {n : Nat} {methods : Fin n → PlainMethods.Method}
    {state : TSO64.State}
    {cuts : (tid : Fin n) → PlainMethods.CompletionCut (methods tid) tid.val state}
    {choices : Nat → Nat → Bool} {result : TSO64.State × List Observation}
    (completed : PlainMethods.CohortCompletion cuts choices result) (tid : Fin n)
    (returned : (cuts tid).worker.phase = .returned) :
    issues tid.val (PlainMethods.cohortActions (fun slot => (cuts slot).point) choices) = 0 := by
  rw [PlainCallProgress64.issues_eq]
  exact completed.returned_ownIssues_zero tid returned

/-- Derive all current cuts from the real prefix, then construct the chosen
suffix. The retained completion certificate gives exact remaining counts,
already-returned skipping and saved prefix replies through its shared APIs.
The independent Post concerns the same concatenated original action list. -/
theorem complete {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {prior : List Action}
    {actual : TSO64.State × List Observation}
    (success : schedule before prior .sharedCell = .ok actual)
    (choices : Nat → Nat → Bool) :
    ∃ (cuts : (tid : Fin before.workers.length) →
        PlainMethods.InvocationCut (PlainCallAdmission64.invocations static pre tid) prior actual),
      ∃ result,
        PlainMethods.CohortCompletion (fun tid => (cuts tid).cut) choices result ∧
        ChosenIssues choices
          (PlainMethods.cohortActions (fun tid => (cuts tid).cut.point) choices) ∧
        schedule before
          (prior ++ PlainMethods.cohortActions (fun tid => (cuts tid).cut.point) choices)
          .sharedCell = .ok (result.1, actual.2 ++ result.2) ∧
        Nonempty (Post before inputs
          (prior ++ PlainMethods.cohortActions (fun tid => (cuts tid).cut.point) choices)
          (result.1, actual.2 ++ result.2)) := by
  obtain ⟨cuts, result, completed, appended, _batch⟩ :=
    PlainMethods.cohort_complete_after_prefix
      (PlainCallAdmission64.invocations static pre) success choices
  exact ⟨cuts, result, completed, chosen_cohort _ choices, appended,
    PlainCallBehavior64.post static pre appended completed.returned⟩

/-- Independent chosen finite completion from current-only admission and an
actual prefix. No future current point or successful step is a premise. -/
theorem completion {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {prior : List Action}
    {actual : TSO64.State × List Observation}
    (success : schedule before prior .sharedCell = .ok actual)
    (choices : Nat → Nat → Bool) :
    ∃ suffix result, ChosenIssues choices suffix ∧
      schedule actual.1 suffix .sharedCell = .ok result ∧ Returned result.1 := by
  obtain ⟨_cuts, result, completed, chosen, _appended, _post⟩ :=
    complete static pre success choices
  exact ⟨_, result, chosen, completed.scheduled, completed.returned⟩

/-- Publication closure is a separately constructed actual drain schedule.
Every CPU response is unchanged although these drains can change shared RAM.
The independent Post retains the entire original execution and drain suffix. -/
theorem closure {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok actual)
    (returned : Returned actual.1) :
    ∃ closed,
      DrainClosure.drainAll actual.1 .sharedCell = .ok closed ∧
      DrainClosure.Certificate actual.1 closed .sharedCell ∧ Finished closed.1 ∧
      schedule before (actions ++ DrainClosure.actions actual.1) .sharedCell =
        .ok (closed.1, actual.2 ++ closed.2) ∧
      Nonempty (Post before inputs (actions ++ DrainClosure.actions actual.1)
        (closed.1, actual.2 ++ closed.2)) ∧
      (∀ tid, TSO64.Return.returnValue (closed.1, .returned tid) =
        TSO64.Return.returnValue (actual.1, .returned tid)) := by
  obtain ⟨closed, drained, certificate⟩ :=
    DrainClosure.drainAll_complete (schedule_wellFormed pre.valid success)
  have finished : Finished closed.1 :=
    ⟨PlainMethods.completion_drain_returned certificate returned, certificate.quiescent⟩
  have appended := PlainMethods.completion_schedule_append success certificate.scheduled
  exact ⟨closed, drained, certificate, finished, appended,
    PlainCallBehavior64.post static pre appended finished.1,
    PlainMethods.completion_drain_responses certificate⟩

end EDSL.OS.PlainCallCompletion64

#audit_edsl
