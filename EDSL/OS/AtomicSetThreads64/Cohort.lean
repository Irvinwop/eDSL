/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Lifecycle
import EDSL.OS.AtomicSetThreads64.Scheduling
import EDSL.OS.AtomicSetThreads64.History

set_option warningAsError true

namespace EDSL.OS.AtomicSetThreads64

/-- The current finite cohort includes running and completed workers. Removed
identities are skipped; the frontier is not a bound on instruction counts. -/
def currentCohort (state : State) : List Nat :=
  (List.range state.nextThread).filter fun identifier => (state.workers identifier).isSome

theorem mem_currentCohort (state : State) (identifier : Nat) :
    identifier ∈ currentCohort state ↔
      identifier < state.nextThread ∧ ∃ worker, state.workers identifier = some worker := by
  simp only [currentCohort, List.mem_filter, List.mem_range]
  cases state.workers identifier <;> simp

theorem currentCohort_nodup (state : State) : (currentCohort state).Nodup := by
  exact List.nodup_range.filter _

theorem mem_currentCohort_iff_live (state : State) (valid : WellFormed state) (identifier : Nat) :
    identifier ∈ currentCohort state ↔ ∃ worker, state.workers identifier = some worker := by
  rw [mem_currentCohort]
  exact ⟨And.right, fun ⟨worker, live⟩ => ⟨(valid.2 _ _ live).1, worker, live⟩⟩

theorem currentCohort_replace_some (state : State) (identifier : Nat) (worker next : Worker)
    (live : state.workers identifier = some worker) :
    currentCohort (replace state identifier (some next)) = currentCohort state := by
  simp only [currentCohort, replace]
  apply List.filter_congr
  intro query _
  by_cases own : query = identifier
  · subst query; simp [live]
  · simp [own]

/-- Exactly the supplied finite number of own selections, with an arbitrary
undefined-AF choice at every offset, including the eventual RET. -/
def remainingSelections (identifier rank : Nat) (af : Nat → Bool) : List (Nat × Bool) :=
  (List.range rank).map fun offset => (identifier, af offset)

theorem remainingSelections_length (identifier rank : Nat) (af : Nat → Bool) :
    (remainingSelections identifier rank af).length = rank := by
  simp [remainingSelections]

theorem remainingSelections_at (identifier rank offset : Nat) (af : Nat → Bool)
    (within : offset < rank) :
    (remainingSelections identifier rank af)[offset]? = some (identifier, af offset) := by
  simp only [remainingSelections, List.getElem?_map, List.getElem?_range within, Option.map_some]

theorem remainingSelections_identifiers (identifier rank : Nat) (af : Nat → Bool) :
    (remainingSelections identifier rank af).map Prod.fst = List.replicate rank identifier := by
  simp only [remainingSelections, List.map_map, Function.comp_def]
  exact (List.map_const' ..).trans (by rw [List.length_range])

theorem remainingSelections_count (identifier rank query : Nat) (af : Nat → Bool) :
    ((remainingSelections identifier rank af).map Prod.fst).count query =
      if identifier = query then rank else 0 := by
  rw [remainingSelections_identifiers, List.count_replicate]
  simp

/-- A plan for a supplied list of current identities. A missing identity has
no selections; membership and exact counts are proved separately. -/
def cohortSelectionsFor (state : State) (identifiers : List Nat) (af : Nat → Nat → Bool) :
    List (Nat × Bool) :=
  identifiers.flatMap fun identifier => match state.workers identifier with
    | none => []
    | some worker => remainingSelections identifier worker.rank (af identifier)

def cohortSelections (state : State) (af : Nat → Nat → Bool) : List (Nat × Bool) :=
  cohortSelectionsFor state (currentCohort state) af

theorem cohortSelectionsFor_cons (state : State) (identifier : Nat) (rest : List Nat)
    (af : Nat → Nat → Bool) :
    cohortSelectionsFor state (identifier :: rest) af =
      (match state.workers identifier with
        | none => []
        | some worker => remainingSelections identifier worker.rank (af identifier)) ++
      cohortSelectionsFor state rest af := rfl

theorem cohortSelectionsFor_count_absent (state : State) (identifiers : List Nat)
    (af : Nat → Nat → Bool) (query : Nat) (absent : query ∉ identifiers) :
    ((cohortSelectionsFor state identifiers af).map Prod.fst).count query = 0 := by
  induction identifiers with
  | nil => rfl
  | cons identifier rest ih =>
    have different : identifier ≠ query := by intro equal; simp [equal] at absent
    have notIn : query ∉ rest := fun member => absent (by simp [member])
    cases found : state.workers identifier <;>
      simp [cohortSelectionsFor_cons, found, List.map_append, List.count_append,
        remainingSelections_count, different, ih notIn]

theorem cohortSelectionsFor_count (state : State) (identifiers : List Nat)
    (af : Nat → Nat → Bool) (query : Nat) (unique : identifiers.Nodup) :
    ((cohortSelectionsFor state identifiers af).map Prod.fst).count query =
      if query ∈ identifiers then (state.workers query).map Worker.rank |>.getD 0 else 0 := by
  induction identifiers with
  | nil => simp [cohortSelectionsFor]
  | cons identifier rest ih =>
    have distinct := List.nodup_cons.mp unique
    by_cases same : identifier = query
    · subst identifier
      have tailCount := cohortSelectionsFor_count_absent state rest af query distinct.1
      cases found : state.workers query <;>
        simp [cohortSelectionsFor_cons, found, List.map_append, List.count_append,
          remainingSelections_count, tailCount]
    · cases found : state.workers identifier <;>
        simp [cohortSelectionsFor_cons, found, List.map_append, List.count_append,
          remainingSelections_count, same, Ne.symm same, ih distinct.2]

theorem cohortSelections_count (state : State) (af : Nat → Nat → Bool) (query : Nat)
    (valid : WellFormed state) :
    ((cohortSelections state af).map Prod.fst).count query =
      ((state.workers query).map Worker.rank).getD 0 := by
  rw [cohortSelections, cohortSelectionsFor_count _ _ _ _ (currentCohort_nodup state)]
  by_cases member : query ∈ currentCohort state
  · simp [member]
  · have absent : state.workers query = none := by
      cases found : state.workers query with
      | none => rfl
      | some worker => exact False.elim (member ((mem_currentCohort_iff_live _ valid _).2 ⟨worker, found⟩))
    simp [member, absent]

theorem selectedCount_cohortSelections (state : State) (af : Nat → Nat → Bool) (query : Nat)
    (valid : WellFormed state) :
    selectedCount (cohortSelections state af) query =
      ((state.workers query).map Worker.rank).getD 0 :=
  cohortSelections_count state af query valid

/-- Legality is derived from current worker resources and exact finite counts;
no future dispatch, favorable AF, fairness or requested result is admitted. -/
theorem cohortSelections_legal (state : State) (af : Nat → Nat → Bool) (valid : WellFormed state) :
    Legal state (cohortSelections state af) := by
  intro identifier positive
  rw [selectedCount_cohortSelections _ _ _ valid] at positive
  cases found : state.workers identifier with
  | none => simp [found] at positive
  | some worker =>
    exact ⟨worker, rfl, by simp [selectedCount_cohortSelections _ _ _ valid, found]⟩

/-- Audit data survives collection even though the worker entry is removed.
The context is the actual checked join result, not a reconstructed CPU state. -/
structure CollectionRecord where
  identifier : Nat
  worker : Worker
  context : Context

/-- Checked finite collection. Failure returns the checked lifecycle fault and
does not expose any partially collected state. -/
def collectCohort (state : State) : List Nat → Except Fault (State × List CollectionRecord)
  | [] => .ok (state, [])
  | identifier :: rest => do
    let worker ← match state.workers identifier with
      | none => .error .missingThread
      | some worker => .ok worker
    let joined ← join state 0 identifier
    let tail ← collectCohort joined.1 rest
    return (tail.1, ⟨identifier, worker, joined.2⟩ :: tail.2)

/-- Every recorded administrative position is an actual checked join, retaining
that worker's entire event prefix and returned private context. -/
inductive CollectionHistory : State → List CollectionRecord → State → Prop where
  | refl {state} : CollectionHistory state [] state
  | next {state middle final identifier worker context rest}
      (live : state.workers identifier = some worker)
      (joined : join state 0 identifier = .ok (middle, context))
      (tail : CollectionHistory middle rest final) :
      CollectionHistory state (⟨identifier, worker, context⟩ :: rest) final

theorem collectCohort_cons_ok (state : State) (identifier : Nat) (rest : List Nat)
    (result : State × List CollectionRecord)
    (success : collectCohort state (identifier :: rest) = .ok result) :
    ∃ worker joined tail, state.workers identifier = some worker ∧
      join state 0 identifier = .ok joined ∧ collectCohort joined.1 rest = .ok tail ∧
      result = (tail.1, ⟨identifier, worker, joined.2⟩ :: tail.2) := by
  cases found : state.workers identifier with
  | none => simp [collectCohort, found] at success
  | some worker =>
    cases joined : join state 0 identifier with
    | error fault => simp [collectCohort, found, joined] at success
    | ok first =>
      cases collected : collectCohort first.1 rest with
      | error fault => simp [collectCohort, found, joined, collected] at success
      | ok tail =>
        simp [collectCohort, found, joined, collected] at success
        exact ⟨worker, first, tail, rfl, rfl, collected, success.symm⟩

theorem collectCohort_history (state : State) (identifiers : List Nat)
    (result : State × List CollectionRecord) (success : collectCohort state identifiers = .ok result) :
    CollectionHistory state result.2 result.1 := by
  induction identifiers generalizing state result with
  | nil => simp [collectCohort] at success; cases success; exact .refl
  | cons identifier rest ih =>
    obtain ⟨worker, joined, tail, live, joinedAt, collected, same⟩ := collectCohort_cons_ok _ _ _ _ success
    rw [same]
    exact .next live joinedAt (ih _ _ collected)

theorem collectCohort_identifiers (state : State) (identifiers : List Nat)
    (result : State × List CollectionRecord) (success : collectCohort state identifiers = .ok result) :
    result.2.map CollectionRecord.identifier = identifiers := by
  induction identifiers generalizing state result with
  | nil => simp [collectCohort] at success; cases success; rfl
  | cons identifier rest ih =>
    obtain ⟨worker, joined, tail, live, joinedAt, collected, same⟩ := collectCohort_cons_ok _ _ _ _ success
    rw [same]
    simp only [List.map_cons, ih _ _ collected]

theorem CollectionHistory.wellFormed {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) (valid : WellFormed state) : WellFormed final := by
  induction history with
  | refl => exact valid
  | next live joined tail ih => exact ih (join_wellFormed _ _ _ _ valid joined)

theorem CollectionHistory.resources {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) :
    final.shared.legacy.shared.resources = state.shared.legacy.shared.resources ∧
      final.shared.cells = state.shared.cells := by
  induction history with
  | refl => exact ⟨rfl, rfl⟩
  | next live joined tail ih =>
    have kept := join_resources _ _ _ _ joined
    exact ⟨ih.1.trans kept.1, ih.2.trans kept.2⟩

theorem CollectionHistory.frontier {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) : final.nextThread = state.nextThread := by
  induction history with
  | refl => rfl
  | next live joined tail ih => exact ih.trans (join_workers _ _ _ _ joined).2.1

/-- One managed administrative position for each actual checked join. -/
theorem CollectionHistory.managed {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) :
    History state (List.replicate records.length none) final := by
  induction history with
  | refl => exact .refl
  | next live joined tail ih => exact .next (.join joined) ih

/-- Administrative collection has an honest lower history. This projection is
only for joins and does not relabel mixed decoded RMWs as OR updates. -/
theorem CollectionHistory.atomicHistory {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) :
    Atomics64.History state.shared (List.replicate (3 * records.length) none) final.shared := by
  induction history with
  | refl => exact .refl
  | next live joined tail ih =>
    have both := (join_history _ _ _ _ joined).trans ih
    simpa only [List.length_cons, Nat.mul_succ, Nat.add_succ, Nat.add_zero,
      List.replicate_succ, List.cons_append, List.nil_append] using both

theorem CollectionHistory.audit {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) :
    ∀ record, record ∈ records → state.workers record.identifier = some record.worker ∧
      record.worker.phase = .completed ∧ record.context = record.worker.context := by
  induction history with
  | refl => intro record member; simp at member
  | @next state middle final identifier worker context rest live joined tail ih =>
    intro record member
    rcases List.mem_cons.mp member with same | member
    · subst record
      obtain ⟨actual, _, _, _, found, _, done, _, _, _, result⟩ := join_ok _ _ _ _ joined
      have equal := Option.some.inj (found.symm.trans live)
      subst actual
      exact ⟨live, done, congrArg Prod.snd result⟩
    · obtain ⟨atMiddle, done, returnedContext⟩ := ih record member
      have frame := join_workers _ _ _ _ joined
      have different : record.identifier ≠ identifier := by
        intro equal
        rw [equal, frame.1] at atMiddle
        cases atMiddle
      exact ⟨(frame.2.2 _ different).symm.trans atMiddle, done, returnedContext⟩

/-- All three exact resources remain revoked after every later join in this
collection; none of the retained audit records is live authority. -/
theorem CollectionHistory.revoked {state final : State} {records : List CollectionRecord}
    (history : CollectionHistory state records final) (valid : WellFormed state) :
    ∀ record, record ∈ records →
      Atomics64.HandleRevoked final.shared record.worker.handle ∧
      Borrowing.Revoked final.shared.legacy.shared record.worker.codeLoan ∧
      Borrowing.Revoked final.shared.legacy.shared record.worker.stackLoan := by
  induction history with
  | refl => intro record member; simp at member
  | @next state middle final identifier worker context rest live joined tail ih =>
    intro record member
    rcases List.mem_cons.mp member with same | member
    · subst record
      obtain ⟨actual, found, handle, code, stack⟩ := join_revokes _ _ _ _ valid joined
      have equal := Option.some.inj (found.symm.trans live)
      subst actual
      have middleValid := (join_wellFormed _ _ _ _ valid joined).1
      exact ⟨tail.atomicHistory.handle_revoked handle,
        tail.atomicHistory.loan_revoked middleValid code,
        tail.atomicHistory.loan_revoked middleValid stack⟩
    · exact ih (join_wellFormed _ _ _ _ valid joined) record member

theorem collectCohort_workers (state : State) (identifiers : List Nat)
    (result : State × List CollectionRecord) (success : collectCohort state identifiers = .ok result)
    (query : Nat) :
    result.1.workers query = if query ∈ identifiers then none else state.workers query := by
  induction identifiers generalizing state result with
  | nil => simp [collectCohort] at success; cases success; simp
  | cons identifier rest ih =>
    obtain ⟨worker, joined, tail, live, joinedAt, collected, same⟩ := collectCohort_cons_ok _ _ _ _ success
    rw [same]
    have frame := join_workers _ _ _ _ joinedAt
    have after := ih _ _ collected
    by_cases own : query = identifier
    · subst query
      simp [after, frame.1]
    · simp [after, frame.2.2 _ own, own]

/-- Construct collection from present completed-worker resources. No successful
future join is required by the input contract. -/
theorem collectCohort_enabled (state : State) (identifiers : List Nat)
    (valid : WellFormed state) (unique : identifiers.Nodup)
    (completed : ∀ identifier, identifier ∈ identifiers →
      ∃ worker, state.workers identifier = some worker ∧ worker.phase = .completed) :
    ∃ result, collectCohort state identifiers = .ok result ∧ WellFormed result.1 := by
  induction identifiers generalizing state with
  | nil => exact ⟨(state, []), rfl, valid⟩
  | cons identifier rest ih =>
    have distinct := List.nodup_cons.mp unique
    obtain ⟨worker, live, done⟩ := completed identifier (by simp)
    obtain ⟨joined, joinedAt, afterValid⟩ := join_enabled state identifier worker valid live done
    have tailReady : ∀ query, query ∈ rest →
        ∃ worker, joined.1.workers query = some worker ∧ worker.phase = .completed := by
      intro query member
      obtain ⟨peer, peerAt, peerDone⟩ := completed query (by simp [member])
      have different : query ≠ identifier := by intro equal; subst query; exact distinct.1 member
      exact ⟨peer, ((join_workers _ _ _ _ joinedAt).2.2 _ different).trans peerAt, peerDone⟩
    obtain ⟨tail, collected, finalValid⟩ := ih joined.1 afterValid distinct.2 tailReady
    exact ⟨(tail.1, ⟨identifier, worker, joined.2⟩ :: tail.2),
      by simp [collectCohort, live, joinedAt, collected], finalValid⟩

theorem collectCohort_resources (state : State) (identifiers : List Nat)
    (result : State × List CollectionRecord) (success : collectCohort state identifiers = .ok result) :
    result.1.shared.legacy.shared.resources = state.shared.legacy.shared.resources ∧
      result.1.shared.cells = state.shared.cells :=
  (collectCohort_history _ _ _ success).resources

theorem collectCohort_preserves_peer (state : State) (identifiers : List Nat)
    (result : State × List CollectionRecord) (success : collectCohort state identifiers = .ok result)
    (query : Nat) (outside : query ∉ identifiers) : result.1.workers query = state.workers query := by
  simpa only [outside, ↓reduceIte] using collectCohort_workers _ _ _ success query

/-- Every collected worker's complete stored audit list and completed ABI
context remain available with their pre-collection current resource validity. -/
theorem collectCohort_audit (state : State) (identifiers : List Nat)
    (result : State × List CollectionRecord) (valid : WellFormed state)
    (success : collectCohort state identifiers = .ok result) :
    ∀ record, record ∈ result.2 → state.workers record.identifier = some record.worker ∧
      WorkerValid state.shared record.identifier record.worker ∧
      record.worker.phase = .completed ∧ record.context = record.worker.context := by
  intro record member
  obtain ⟨live, done, context⟩ := (collectCohort_history _ _ _ success).audit record member
  exact ⟨live, (valid.2 _ _ live).2, done, context⟩

/-- Dispatch preserves the current finite membership, including a worker that
has just completed RET. Collection is a separate checked operation. -/
theorem currentCohort_dispatch (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    currentCohort result.1 = currentCohort state := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect <;> exact currentCohort_replace_some state identifier worker _ live

theorem cohortSchedule_frame (state : State) (selections : List Selection)
    (result : State × List Observation) (valid : WellFormed state)
    (success : schedule state selections = .ok result) :
    result.1.nextThread = state.nextThread ∧ currentCohort result.1 = currentCohort state := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact ⟨rfl, rfl⟩
  | cons selection rest ih =>
    obtain ⟨first, tail, selected, scheduled, same⟩ := schedule_cons_ok _ _ _ _ success
    have restFrame := ih first.1 tail (dispatch_wellFormed _ _ _ _ valid selected) scheduled
    rw [same]
    exact ⟨restFrame.1.trans (dispatch_frame _ _ _ _ valid selected).1,
      restFrame.2.trans (currentCohort_dispatch _ _ _ _ valid selected)⟩

theorem cohortSchedule_completes (state : State) (af : Nat → Nat → Bool)
    (result : State × List Observation) (valid : WellFormed state)
    (success : schedule state (cohortSelections state af) = .ok result)
    (identifier : Nat) (worker : Worker) (live : state.workers identifier = some worker) :
    ∃ current, result.1.workers identifier = some current ∧ current.phase = .completed ∧
      WorkerValid result.1.shared identifier current := by
  apply schedule_completes _ _ _ _ _ valid live success
  simp [selectedCount_cohortSelections _ _ _ valid, live]

/-- An actual finite dispatch schedule followed by checked collection of every
initially live worker. The resource equality refers to CURRENT post-schedule
RAM; it does not equate that RAM with any worker's last captured after-word. -/
structure CohortCompletion (state : State) (af : Nat → Nat → Bool)
    (scheduled : State × List Observation) (collected : State × List CollectionRecord) : Prop where
  scheduleSuccess : schedule state (cohortSelections state af) = .ok scheduled
  collectSuccess : collectCohort scheduled.1 (currentCohort state) = .ok collected
  wellFormed : WellFormed collected.1
  empty : ∀ identifier, collected.1.workers identifier = none
  frontier : collected.1.nextThread = state.nextThread
  resources : collected.1.shared.legacy.shared.resources = scheduled.1.shared.legacy.shared.resources
  cells : collected.1.shared.cells = scheduled.1.shared.cells

/-- Construct completion and collection of the current finite cohort with
every supplied AF choice. Present membership/resources/counts establish Legal;
Scheduling and Lifecycle enabledness derive the actual successful execution. -/
theorem currentCohort_complete_collect (state : State) (af : Nat → Nat → Bool)
    (valid : WellFormed state) :
    ∃ scheduled collected, CohortCompletion state af scheduled collected := by
  obtain ⟨scheduled, scheduledAt⟩ := schedule_enabled _ _ valid (cohortSelections_legal _ _ valid)
  have middleValid := schedule_wellFormed _ _ _ valid scheduledAt
  have scheduleFrame := cohortSchedule_frame _ _ _ valid scheduledAt
  have complete : ∀ identifier, identifier ∈ currentCohort state →
      ∃ worker, scheduled.1.workers identifier = some worker ∧ worker.phase = .completed := by
    intro identifier member
    obtain ⟨initial, live⟩ := (mem_currentCohort_iff_live _ valid _).1 member
    obtain ⟨worker, live, done, _⟩ := cohortSchedule_completes _ _ _ valid scheduledAt _ _ live
    exact ⟨worker, live, done⟩
  obtain ⟨collected, collectedAt, finalValid⟩ :=
    collectCohort_enabled _ _ middleValid (currentCohort_nodup state) complete
  have collection := collectCohort_history _ _ _ collectedAt
  refine ⟨scheduled, collected, scheduledAt, collectedAt, finalValid, ?_,
    collection.frontier.trans scheduleFrame.1, collection.resources.1, collection.resources.2⟩
  intro identifier
  rw [collectCohort_workers _ _ _ collectedAt]
  by_cases member : identifier ∈ currentCohort state
  · simp [member]
  · have absent : scheduled.1.workers identifier = none := by
      cases found : scheduled.1.workers identifier with
      | none => rfl
      | some worker =>
        have present := (mem_currentCohort_iff_live _ middleValid _).2 ⟨worker, found⟩
        rw [scheduleFrame.2] at present
        exact False.elim (member present)
    simp [member, absent]

theorem CohortCompletion.dispatchHistory {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) :
    DispatchHistory state scheduled.2 scheduled.1 :=
  schedule_history _ _ _ completion.scheduleSuccess

theorem CohortCompletion.collectionHistory {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) :
    CollectionHistory scheduled.1 collected.2 collected.1 :=
  collectCohort_history _ _ _ completion.collectSuccess

theorem CohortCompletion.scheduleManagedHistory {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) :
    History state (scheduled.2.map Prod.snd) scheduled.1 := by
  have project {before after : State} {observations : List Observation}
      (history : DispatchHistory before observations after) :
      History before (observations.map Prod.snd) after := by
    induction history with
    | refl => exact .refl
    | next selected tail ih => exact .next (.dispatch selected) ih
  exact project completion.dispatchHistory

/-- The full managed history retains all selected instruction labels and one
administrative position per collection; no lower history hop is manufactured. -/
theorem CohortCompletion.managedHistory {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) :
    History state (scheduled.2.map Prod.snd ++ List.replicate collected.2.length none) collected.1 :=
  completion.scheduleManagedHistory.trans completion.collectionHistory.managed

theorem CohortCompletion.collectedIdentifiers {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) :
    collected.2.map CollectionRecord.identifier = currentCohort state :=
  collectCohort_identifiers _ _ _ completion.collectSuccess

/-- All instruction positions, including actual RET `none` labels, remain
bound to exactly the constructed selections and their supplied AF values. -/
theorem CohortCompletion.observationSelections {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) :
    scheduled.2.map Prod.fst = cohortSelections state af :=
  schedule_selections _ _ _ completion.scheduleSuccess

theorem CohortCompletion.audit {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) (valid : WellFormed state) :
    ∀ record, record ∈ collected.2 →
      scheduled.1.workers record.identifier = some record.worker ∧
      WorkerValid scheduled.1.shared record.identifier record.worker ∧
      record.worker.phase = .completed ∧ record.context = record.worker.context :=
  collectCohort_audit _ _ _ (schedule_wellFormed _ _ _ valid completion.scheduleSuccess)
    completion.collectSuccess

/-- Collection retains exactly the initial audit prefix followed by this
worker's actual emitted occurrences from the successful schedule. Duplicate,
cancelling and no-change RMWs remain distinct occurrences. -/
theorem CohortCompletion.auditExtension {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) (valid : WellFormed state) :
    ∀ record, record ∈ collected.2 → ∃ previous,
      state.workers record.identifier = some previous ∧ previous.origin = record.worker.origin ∧
      record.worker.events = previous.events ++ workerEvents record.identifier (scheduled.2.map Prod.snd) := by
  intro record member
  have identifierMember : record.identifier ∈ currentCohort state := by
    rw [← completion.collectedIdentifiers]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  obtain ⟨previous, live⟩ := (mem_currentCohort_iff_live _ valid _).1 identifierMember
  have atScheduled := (completion.audit valid record member).1
  have origin := completion.scheduleManagedHistory.origin_and_prefix valid _ _ _ live atScheduled
  exact ⟨previous, live, origin.1,
    completion.scheduleManagedHistory.worker_events valid _ _ _ live atScheduled⟩

theorem CohortCompletion.revoked {state : State} {af : Nat → Nat → Bool}
    {scheduled : State × List Observation} {collected : State × List CollectionRecord}
    (completion : CohortCompletion state af scheduled collected) (valid : WellFormed state) :
    ∀ record, record ∈ collected.2 →
      Atomics64.HandleRevoked collected.1.shared record.worker.handle ∧
      Borrowing.Revoked collected.1.shared.legacy.shared record.worker.codeLoan ∧
      Borrowing.Revoked collected.1.shared.legacy.shared record.worker.stackLoan :=
  completion.collectionHistory.revoked (schedule_wellFormed _ _ _ valid completion.scheduleSuccess)

/-- Executable transaction for the proved finite plan and checked collection. -/
def completeCohort (state : State) (af : Nat → Nat → Bool) :
    Except Fault (State × (List Observation × List CollectionRecord)) := do
  let scheduled ← schedule state (cohortSelections state af)
  let collected ← collectCohort scheduled.1 (currentCohort state)
  return (collected.1, (scheduled.2, collected.2))

theorem completeCohort_enabled (state : State) (af : Nat → Nat → Bool) (valid : WellFormed state) :
    ∃ result, completeCohort state af = .ok result ∧ WellFormed result.1 ∧
      ∀ identifier, result.1.workers identifier = none := by
  obtain ⟨scheduled, collected, completion⟩ := currentCohort_complete_collect state af valid
  exact ⟨(collected.1, (scheduled.2, collected.2)),
    by simp [completeCohort, completion.scheduleSuccess, completion.collectSuccess],
    completion.wellFormed, completion.empty⟩

/-- Creation availability is an explicit spawn premise. Once checked creation
succeeds constructively, the same finite theorem also covers all existing peers. -/
theorem spawn_currentCohort_complete_collect (state : State) (start : Start) (available : Bool)
    (af : Nat → Nat → Bool) (valid : WellFormed state) (ready : SpawnReady state start)
    (free : available = true) :
    ∃ created scheduled collected, spawn state 0 start available = .ok created ∧
      CohortCompletion created.1 af scheduled collected := by
  obtain ⟨created, spawned, afterValid⟩ := spawn_enabled state start available valid ready free
  obtain ⟨scheduled, collected, completion⟩ := currentCohort_complete_collect created.1 af afterValid
  exact ⟨created, scheduled, collected, spawned, completion⟩

end EDSL.OS.AtomicSetThreads64
