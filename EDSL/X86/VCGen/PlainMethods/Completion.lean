/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Batch
import EDSL.OS.TSO64.DrainClosure

/-!
Construct a finite chosen schedule returning the complete fixed worker cohort.
One actual invocation admits each initial worker slot; an arbitrary successful
prior determines the current cutpoints through `schedule_preserves`. The
suffix visits the slots in increasing index order, with arbitrary per-thread,
per-suffix-own-issue AF choices, issuing exactly each current point's remaining
instructions. Previously returned workers contribute an empty block.

Methods, resources, padding and initial queues may differ at every slot. RET
does not require publication or an empty FIFO. The optional closing helper
appends the actual `DrainClosure` schedule and retains its certificate.

This constructs one finite schedule, with no fairness, source preservation or
compiler claim. The existing method/TSO64 environmental assumptions apply.
No future success, desired At, history, graph, or search bound is a premise of
`cohort_complete_after_prefix`.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

/-- The actual present cutpoint for one fixed method and worker slot. -/
structure CompletionCut (method : Method) (tid : Nat) (state : OS.TSO64.State) where
  point : Point method.operation
  worker : Worker
  current : Current method state
  live : state.workers[tid]? = some worker
  located : At method point worker

/-- A complete annotation recovered from the supplied successful prior.
The cut and replies concern that exact run, including all its drains. -/
structure InvocationCut {initial : OS.TSO64.State} {tid : Nat}
    (invocation : Invocation initial tid) (prior : List Action)
    (actual : OS.TSO64.State × List Observation) where
  cut : CompletionCut invocation.method tid actual.1
  emissions : List (Option invocation.method.operation.Reply)
  progress : cut.point.remaining + ownIssues tid prior = invocation.padding.length + 2
  replies : emissions.filterMap id = cut.point.replies
  trace : AccessTrace invocation.method tid initial prior actual emissions

/-- Recover the current authority, worker, point, remaining count and replies
from the real prior alone. This accepts no caller-provided future cutpoint. -/
theorem Invocation.cut_after_prefix {initial : OS.TSO64.State} {tid : Nat}
    (invocation : Invocation initial tid) {prior : List Action}
    {actual : OS.TSO64.State × List Observation}
    (success : schedule initial prior .sharedCell = .ok actual) :
    Nonempty (InvocationCut invocation prior actual) := by
  obtain ⟨current, point, worker, emissions, live, located, progress, replies, trace⟩ :=
    schedule_preserves invocation.current invocation.live invocation.entry success
  exact ⟨⟨⟨point, worker, current, live, located⟩, emissions,
    by simpa only [Point.remaining] using progress,
    by simpa only [Point.replies, List.nil_append] using replies, trace⟩⟩

/-- A specified finite block of own issues; the offset is local to this suffix. -/
def remainingIssues (tid count : Nat) (choices : Nat → Bool) : List Action :=
  (List.range count).map fun offset => .issue tid (choices offset)

theorem remainingIssues_length (tid count : Nat) (choices : Nat → Bool) :
    (remainingIssues tid count choices).length = count := by
  simp only [remainingIssues, List.length_map, List.length_range]

theorem remainingIssues_at (tid count offset : Nat) (choices : Nat → Bool)
    (within : offset < count) :
    (remainingIssues tid count choices)[offset]? = some (.issue tid (choices offset)) := by
  simp only [remainingIssues, List.getElem?_map, List.getElem?_range within, Option.map_some]

/-- The schedule is fixed by the actual current points and the caller's AF
choices, rather than discovered by searching for successful future steps. -/
def cohortActionsFor {n : Nat} {operations : Fin n → Operation}
    (points : (tid : Fin n) → Point (operations tid))
    (slots : List (Fin n)) (choices : Nat → Nat → Bool) : List Action :=
  slots.flatMap fun tid => remainingIssues tid.val (points tid).remaining (choices tid.val)

def cohortActions {n : Nat} {operations : Fin n → Operation}
    (points : (tid : Fin n) → Point (operations tid))
    (choices : Nat → Nat → Bool) : List Action :=
  cohortActionsFor points (List.finRange n) choices

theorem cohortActionsFor_length {n : Nat} {operations : Fin n → Operation}
    (points : (tid : Fin n) → Point (operations tid))
    (slots : List (Fin n)) (choices : Nat → Nat → Bool) :
    (cohortActionsFor points slots choices).length =
      (slots.map fun tid => (points tid).remaining).sum := by
  induction slots with
  | nil => rfl
  | cons tid rest ih =>
    change (remainingIssues tid.val (points tid).remaining (choices tid.val) ++
      cohortActionsFor points rest choices).length =
        (points tid).remaining + (rest.map fun slot => (points slot).remaining).sum
    rw [List.length_append, remainingIssues_length, ih]

/-- Compose actual scheduler runs, preserving the entire prior observation
list and the exact concatenated action list. -/
theorem completion_schedule_append {state : OS.TSO64.State}
    {prior suffix : List Action} {middle result : OS.TSO64.State × List Observation}
    {profile : Profile} (firstRun : schedule state prior profile = .ok middle)
    (lastRun : schedule middle.1 suffix profile = .ok result) :
    schedule state (prior ++ suffix) profile = .ok (result.1, middle.2 ++ result.2) := by
  induction prior generalizing state middle with
  | nil =>
    have same : (state, []) = middle := Except.ok.inj firstRun
    subst middle
    exact lastRun
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok firstRun
    rw [same] at lastRun ⊢
    have appended := ih following lastRun
    simp only [List.cons_append, schedule, stepped, ok_bind, appended, pure_ok]

/-- An issue-only block at another slot retains the literal peer worker,
including resources, context, phase, queue and allocation counter. -/
theorem completion_schedule_peer {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {tid peer : Nat} {profile : Profile}
    (only : ∀ action ∈ actions, ∃ af, action = .issue tid af)
    (success : schedule state actions profile = .ok result) (different : peer ≠ tid) :
    result.1.workers[peer]? = state.workers[peer]? := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨af, rfl⟩ := only action List.mem_cons_self
    have onlyRest : ∀ action ∈ rest, ∃ choice, action = .issue tid choice :=
      fun action member => only action (List.mem_cons_of_mem (.issue tid af) member)
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rw [same]
    exact (ih onlyRest following).trans (step_peer stepped different)

/-- Once returned, every further successful schedule retains the exact typed
reply and the full done contract. Own drains are permitted by this helper. -/
theorem completion_preserves_done {method : Method} {tid : Nat}
    {state : OS.TSO64.State} {worker : Worker} {reply : method.operation.Reply}
    (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method (.done reply) worker) {actions : List Action}
    {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result) :
    Current method result.1 ∧ ∃ after,
      result.1.workers[tid]? = some after ∧ At method (.done reply) after := by
  obtain ⟨finalCurrent, point, after, emissions, afterLive, atAfter, progress, replies, _⟩ :=
    schedule_preserves current live located success
  have zero : point.remaining = 0 := by
    have : point.remaining + ownIssues tid actions = 0 := progress
    omega
  obtain ⟨finalReply, rfl⟩ := atAfter.returned_done (atAfter.zero_returned zero)
  have equal : reply = finalReply := by
    change reply :: emissions.filterMap id = [finalReply] at replies
    exact (List.cons.inj replies).1
  subst finalReply
  exact ⟨finalCurrent, after, afterLive, atAfter⟩

/- Each unvisited slot has its original point and worker: the completed
head block only issued the head slot. Current is transported separately,
since the actual world may have changed. No method/opcode split is needed. -/
private theorem completion_slots {n : Nat} {methods : Fin n → Method}
    (points : (tid : Fin n) → Point (methods tid).operation)
    (slots : List (Fin n)) (choices : Nat → Nat → Bool) {state : OS.TSO64.State}
    (unique : slots.Nodup)
    (ready : ∀ tid ∈ slots, Current (methods tid) state ∧ ∃ worker,
      state.workers[tid.val]? = some worker ∧ At (methods tid) (points tid) worker) :
    ∃ result, schedule state (cohortActionsFor points slots choices) .sharedCell = .ok result ∧
      ∀ tid ∈ slots, ∃ worker,
        result.1.workers[tid.val]? = some worker ∧ worker.phase = .returned := by
  induction slots generalizing state with
  | nil =>
    refine ⟨(state, []), rfl, ?_⟩
    intro tid member
    cases member
  | cons tid rest ih =>
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    obtain ⟨current, worker, live, located⟩ := ready tid List.mem_cons_self
    obtain ⟨actions, first, after, reply, plan, _length, only, firstRun, afterLive, atAfter⟩ :=
      complete current live located (choices tid.val)
    have currentAfter := (schedule_preserves current live located firstRun).1
    have restReady : ∀ other ∈ rest, Current (methods other) first.1 ∧ ∃ worker,
        first.1.workers[other.val]? = some worker ∧ At (methods other) (points other) worker := by
      intro other member
      obtain ⟨otherCurrent, otherWorker, otherLive, otherAt⟩ :=
        ready other (List.mem_cons_of_mem tid member)
      have different : other.val ≠ tid.val := by
        intro same
        have equal : other = tid := Fin.ext same
        subst other
        exact absent member
      have peer := completion_schedule_peer only firstRun different
      exact ⟨(schedule_preserves otherCurrent otherLive otherAt firstRun).1,
        otherWorker, peer.trans otherLive, otherAt⟩
    obtain ⟨last, lastRun, restReturned⟩ := ih restUnique restReady
    obtain ⟨_, finalHead, finalHeadLive, finalHeadAt⟩ :=
      completion_preserves_done currentAfter afterLive atAfter lastRun
    refine ⟨(last.1, first.2 ++ last.2), ?_, ?_⟩
    · change schedule state
        (remainingIssues tid.val (points tid).remaining (choices tid.val) ++
          cohortActionsFor points rest choices) .sharedCell = _
      simpa only [plan, remainingIssues] using completion_schedule_append firstRun lastRun
    · intro other member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨finalHead, finalHeadLive, finalHeadAt.location.1⟩
      · exact restReturned other later

/-- Actual finite completion, with all current authority and access annotations
retained. `returned` covers the entire resulting worker list. -/
structure CohortCompletion {n : Nat} {methods : Fin n → Method} {state : OS.TSO64.State}
    (cuts : (tid : Fin n) → CompletionCut (methods tid) tid.val state)
    (choices : Nat → Nat → Bool) (result : OS.TSO64.State × List Observation) : Prop where
  scheduled : schedule state (cohortActions (fun tid => (cuts tid).point) choices)
    .sharedCell = .ok result
  workers_length : result.1.workers.length = state.workers.length
  returned : Returned result.1
  completed : ∀ tid : Fin n, Current (methods tid) result.1 ∧ ∃ after reply emissions,
    result.1.workers[tid.val]? = some after ∧ At (methods tid) (.done reply) after ∧
    BodyPost (methods tid) after reply ∧
    ownIssues tid.val (cohortActions (fun slot => (cuts slot).point) choices) =
      (cuts tid).point.remaining ∧
    (cuts tid).point.replies ++ emissions.filterMap id = [reply] ∧
    AccessTrace (methods tid) tid.val state
      (cohortActions (fun slot => (cuts slot).point) choices) result emissions

/-- Internal current-family interface. The coverage equality excludes omitted
workers; it is supplied by `ScheduleTrace.workers_length` for invocation prefixes.
The family may contain mixed methods and already returned cutpoints. -/
theorem cohort_complete {n : Nat} {methods : Fin n → Method} {state : OS.TSO64.State}
    (population : state.workers.length = n)
    (cuts : (tid : Fin n) → CompletionCut (methods tid) tid.val state)
    (choices : Nat → Nat → Bool) : ∃ result, CohortCompletion cuts choices result := by
  have ready : ∀ tid ∈ List.finRange n, Current (methods tid) state ∧ ∃ worker,
      state.workers[tid.val]? = some worker ∧ At (methods tid) (cuts tid).point worker :=
    fun tid _ => ⟨(cuts tid).current, (cuts tid).worker, (cuts tid).live, (cuts tid).located⟩
  obtain ⟨result, success, perSlot⟩ := completion_slots (methods := methods)
    (fun tid => (cuts tid).point)
    (List.finRange n) choices (List.nodup_finRange n) ready
  have length : result.1.workers.length = n :=
    (ScheduleTrace.workers_length success).trans population
  have returned : Returned result.1 := by
    intro worker member
    obtain ⟨tid, live⟩ := List.mem_iff_getElem?.mp member
    have within : tid < n := by
      have bound := (List.getElem_of_getElem? live).1
      omega
    let slot : Fin n := ⟨tid, within⟩
    obtain ⟨other, otherLive, phase⟩ := perSlot slot (List.mem_finRange slot)
    have same : other = worker := Option.some.inj (otherLive.symm.trans live)
    subst other
    exact phase
  refine ⟨result, ⟨success, ScheduleTrace.workers_length success, returned, ?_⟩⟩
  intro tid
  obtain ⟨current, point, after, emissions, live, located, progress, replies, trace⟩ :=
    schedule_preserves (cuts tid).current (cuts tid).live (cuts tid).located success
  obtain ⟨reply, rfl⟩ := located.returned_done (returned after (List.mem_of_getElem? live))
  exact ⟨current, after, reply, emissions, live, located, located.done_post,
    by simpa only [cohortActions, Point.remaining, Nat.zero_add] using progress,
    by simpa only [Point.replies] using replies, trace⟩

/-- Exact suffix size: the sum of the actual per-slot remaining counts. -/
theorem cohortActions_length {n : Nat} {operations : Fin n → Operation}
    (points : (tid : Fin n) → Point (operations tid))
    (choices : Nat → Nat → Bool) :
    (cohortActions points choices).length =
      ((List.finRange n).map fun tid => (points tid).remaining).sum :=
  cohortActionsFor_length points (List.finRange n) choices

theorem CohortCompletion.issueCount {n : Nat} {methods : Fin n → Method}
    {state : OS.TSO64.State}
    {cuts : (tid : Fin n) → CompletionCut (methods tid) tid.val state}
    {choices : Nat → Nat → Bool} {result : OS.TSO64.State × List Observation}
    (completion : CohortCompletion cuts choices result) (tid : Fin n) :
    ownIssues tid.val (cohortActions (fun slot => (cuts slot).point) choices) =
      (cuts tid).point.remaining := by
  obtain ⟨_, _, _, _, _, _, _, count, _, _⟩ := completion.completed tid
  exact count

/-- A previously returned worker contributes no own issue to this suffix. -/
theorem CohortCompletion.returned_ownIssues_zero {n : Nat} {methods : Fin n → Method}
    {state : OS.TSO64.State}
    {cuts : (tid : Fin n) → CompletionCut (methods tid) tid.val state}
    {choices : Nat → Nat → Bool} {result : OS.TSO64.State × List Observation}
    (completion : CohortCompletion cuts choices result) (tid : Fin n)
    (returned : (cuts tid).worker.phase = .returned) :
    ownIssues tid.val (cohortActions (fun slot => (cuts slot).point) choices) = 0 := by
  rw [completion.issueCount tid]
  obtain ⟨reply, done⟩ := (cuts tid).located.returned_done returned
  rw [done]
  rfl

private theorem completion_reply_eq {operation : Operation} {point : Point operation}
    {reply prior : operation.Reply} {extra : List operation.Reply}
    (replies : point.replies ++ extra = [reply]) (member : prior ∈ point.replies) :
    reply = prior := by
  cases point with
  | preamble offset padding => cases member
  | ret offset original | done original =>
    have same : original = reply := by
      change original :: extra = [reply] at replies
      exact (List.cons.inj replies).1
    have was : prior = original := List.mem_singleton.mp member
    exact same.symm.trans was.symm

/-- Any reply already present at the actual cutpoint is the final typed reply,
even if the suffix changes shared RAM or completes other workers first. -/
theorem CohortCompletion.prior_reply {n : Nat} {methods : Fin n → Method}
    {state : OS.TSO64.State}
    {cuts : (tid : Fin n) → CompletionCut (methods tid) tid.val state}
    {choices : Nat → Nat → Bool} {result : OS.TSO64.State × List Observation}
    (completion : CohortCompletion cuts choices result) (tid : Fin n)
    {prior : (methods tid).operation.Reply} (member : prior ∈ (cuts tid).point.replies) :
    ∃ after, result.1.workers[tid.val]? = some after ∧
      At (methods tid) (.done prior) after ∧ BodyPost (methods tid) after prior := by
  obtain ⟨_, after, reply, emissions, live, located, post, _, replies, _⟩ :=
    completion.completed tid
  have same : reply = prior := completion_reply_eq replies member
  subst reply
  exact ⟨after, live, located, post⟩

/-- In the invocation-prior interface, each actual prior access reply is
retained as the final reply. The prior annotation is from schedule_preserves. -/
theorem CohortCompletion.prefix_reply {initial : OS.TSO64.State}
    {invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val}
    {prior : List Action} {actual : OS.TSO64.State × List Observation}
    {cuts : (tid : Fin initial.workers.length) →
      InvocationCut (invocations tid) prior actual}
    {choices : Nat → Nat → Bool} {result : OS.TSO64.State × List Observation}
    (completion : CohortCompletion (fun tid => (cuts tid).cut) choices result)
    (tid : Fin initial.workers.length) {prior : (invocations tid).method.operation.Reply}
    (observed : prior ∈ (cuts tid).emissions.filterMap id) :
    ∃ after, result.1.workers[tid.val]? = some after ∧
      At (invocations tid).method (.done prior) after ∧
      BodyPost (invocations tid).method after prior := by
  apply completion.prior_reply tid
  rw [← (cuts tid).replies]
  exact observed

/-- Main invocation-prior theorem. Recover every actual cutpoint, construct
the finite suffix, retain the complete prior observations, and extract the
existing batch witness from the derived returned cohort. No future success,
At, completed family, history, graph or fairness premise is accepted. -/
theorem cohort_complete_after_prefix {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {prior : List Action} {actual : OS.TSO64.State × List Observation}
    (success : schedule initial prior .sharedCell = .ok actual)
    (choices : Nat → Nat → Bool) :
    ∃ (cuts : (tid : Fin initial.workers.length) →
        InvocationCut (invocations tid) prior actual), ∃ result,
      CohortCompletion (fun tid => (cuts tid).cut) choices result ∧
      schedule initial
        (prior ++ cohortActions (fun tid => (cuts tid).cut.point) choices) .sharedCell =
          .ok (result.1, actual.2 ++ result.2) ∧
      Nonempty (BatchResult initial
        (prior ++ cohortActions (fun tid => (cuts tid).cut.point) choices)
        (result.1, actual.2 ++ result.2) invocations) := by
  classical
  let cuts : (tid : Fin initial.workers.length) →
      InvocationCut (invocations tid) prior actual :=
    fun tid => Classical.choice ((invocations tid).cut_after_prefix success)
  obtain ⟨result, completion⟩ := cohort_complete (ScheduleTrace.workers_length success)
    (fun tid => (cuts tid).cut) choices
  have appended := completion_schedule_append success completion.scheduled
  have perSlot : ∀ tid : Fin initial.workers.length,
      ∃ worker, result.1.workers[tid.val]? = some worker ∧ worker.phase = .returned := by
    intro tid
    obtain ⟨_, worker, reply, emissions, live, located, _⟩ := completion.completed tid
    exact ⟨worker, live, located.location.1⟩
  exact ⟨cuts, result, completion, appended, completed_batch invocations appended perSlot⟩

/-- Drain closure changes no CPU response, at every index including missing
indices. The literal worker frame is retained in the supplied certificate. -/
theorem completion_drain_responses {state : OS.TSO64.State}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    (certificate : DrainClosure.Certificate state result profile) (tid : Nat) :
    OS.TSO64.Return.returnValue (result.1, .returned tid) =
      OS.TSO64.Return.returnValue (state, .returned tid) := by
  cases live : state.workers[tid]? with
  | none =>
    simp only [OS.TSO64.Return.returnValue, certificate.workers,
      List.getElem?_map, live, Option.map_none]
  | some worker =>
    have finalLive := certificate.worker live
    simp only [OS.TSO64.Return.returnValue, finalLive, live, Option.map_some,
      DrainClosure.clearPending]

/-- Full worker coverage and Returned survive the actual FIFO-clearing frame. -/
theorem completion_drain_returned {state : OS.TSO64.State}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    (certificate : DrainClosure.Certificate state result profile) (returned : Returned state) :
    Returned result.1 := by
  intro worker member
  rw [certificate.workers] at member
  obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.mp member
  exact returned prior priorMember

/-- Optional closed completion. The separate current-WF premise also handles
the empty cohort, whose per-slot Current family is vacuous. Own stores may be
pending at RET; only this appended production drain schedule establishes quiet.
Its actual certificate, exact concatenation and CPU response equality remain
available to callers. -/
theorem CohortCompletion.close {n : Nat} {methods : Fin n → Method}
    {state : OS.TSO64.State}
    {cuts : (tid : Fin n) → CompletionCut (methods tid) tid.val state}
    {choices : Nat → Nat → Bool} {result : OS.TSO64.State × List Observation}
    (completion : CohortCompletion cuts choices result) (valid : WellFormed state .sharedCell) :
    ∃ closed, DrainClosure.drainAll result.1 .sharedCell = .ok closed ∧
      DrainClosure.Certificate result.1 closed .sharedCell ∧
      schedule state
        (cohortActions (fun tid => (cuts tid).point) choices ++ DrainClosure.actions result.1)
        .sharedCell = .ok (closed.1, result.2 ++ closed.2) ∧
      Finished closed.1 ∧
      (∀ tid, OS.TSO64.Return.returnValue (closed.1, .returned tid) =
        OS.TSO64.Return.returnValue (result.1, .returned tid)) := by
  obtain ⟨closed, drained, certificate⟩ :=
    DrainClosure.drainAll_complete (schedule_wellFormed valid completion.scheduled)
  exact ⟨closed, drained, certificate,
    completion_schedule_append completion.scheduled certificate.scheduled,
    ⟨completion_drain_returned certificate completion.returned, certificate.quiescent⟩,
    completion_drain_responses certificate⟩

/-- Close the exact invocation prior plus the constructed issue suffix.
The completion and drain certificates identify both actual intermediate runs;
publication after RET is permitted and the old observations stay a prior. -/
theorem cohort_closed_after_prefix {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (valid : WellFormed initial .sharedCell) {prior : List Action}
    {actual : OS.TSO64.State × List Observation}
    (success : schedule initial prior .sharedCell = .ok actual)
    (choices : Nat → Nat → Bool) :
    ∃ (cuts : (tid : Fin initial.workers.length) →
        InvocationCut (invocations tid) prior actual), ∃ result closed,
      CohortCompletion (fun tid => (cuts tid).cut) choices result ∧
      DrainClosure.drainAll result.1 .sharedCell = .ok closed ∧
      DrainClosure.Certificate result.1 closed .sharedCell ∧
      schedule initial
        (prior ++ (cohortActions (fun tid => (cuts tid).cut.point) choices ++
          DrainClosure.actions result.1)) .sharedCell =
            .ok (closed.1, actual.2 ++ (result.2 ++ closed.2)) ∧
      Finished closed.1 ∧
      (∀ tid, OS.TSO64.Return.returnValue (closed.1, .returned tid) =
        OS.TSO64.Return.returnValue (result.1, .returned tid)) := by
  obtain ⟨cuts, result, completion, _appended, _batch⟩ :=
    cohort_complete_after_prefix invocations success choices
  obtain ⟨closed, drained, certificate, closedRun, finished, responses⟩ :=
    completion.close (schedule_wellFormed valid success)
  exact ⟨cuts, result, closed, completion, drained, certificate,
    completion_schedule_append success closedRun, finished, responses⟩

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
