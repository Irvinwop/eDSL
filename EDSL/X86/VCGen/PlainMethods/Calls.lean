/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Progress
import EDSL.OS.TSO64.ScheduleTrace

/-!
Completed plain managed calls extracted from actual scheduler runs. Invocation
is the admitted initial machine entry; it is not an invented source invocation
or a native boundary. Original action positions include every peer issue and
FIFO drain. A buffered store's response does not imply publication.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

private theorem reply_filter_cons {α : Type _} {head : Option α} {tail : List (Option α)} :
    (head :: tail).filterMap id = head.toList ++ tail.filterMap id := by
  cases head <;> rfl

private theorem reply_eq {operation : Operation} {entry : Register → Word}
    {first second : operation.Reply}
    (same : operation.registers entry first .rax = operation.registers entry second .rax) :
    first = second := by
  cases operation with
  | load address =>
      change AtomicMethods.written entry .rax first .rax =
        AtomicMethods.written entry .rax second .rax at same
      exact (AtomicMethods.written_same entry .rax first).symm.trans
        (same.trans (AtomicMethods.written_same entry .rax second))
  | store address source =>
      change @Eq PUnit first second
      exact Subsingleton.elim _ _

/-- The actual indexed RET, including its production prefix, response value,
and original caller/resource origin. A final RAX value alone is insufficient. -/
def ResponseAt (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (actions : List Action) (result : OS.TSO64.State × List Observation)
    (index : Nat) (reply : method.operation.Reply) : Prop :=
  ∃ before action next,
    schedule state (actions.take index) .sharedCell = .ok (before, result.2.take index) ∧
    actions[index]? = some action ∧ result.2[index]? = some (.returned tid) ∧
    OS.TSO64.step before action .sharedCell = .ok (next, .returned tid) ∧
    Return.returnValue (next, .returned tid) = some (tid, method.responded reply .rax) ∧
    Return.ReturnOrigin before action (next, .returned tid) tid
      (method.responded reply .rax) .sharedCell

private theorem ownIssue_le_one (tid : Nat) (action : Action) : ownIssue tid action ≤ 1 := by
  cases action with
  | issue thread af => simp only [ownIssue]; split <;> omega
  | drain thread => exact Nat.zero_le 1

private theorem ownIssue_eq_one {tid : Nat} {action : Action}
    (one : ownIssue tid action = 1) : ∃ af, action = .issue tid af := by
  cases action with
  | issue thread af =>
    by_cases same : thread = tid
    · subst thread; exact ⟨af, rfl⟩
    · simp [ownIssue, same] at one
  | drain thread => cases one

private theorem returned_step_phase {method : Method} {tid : Nat}
    {state : OS.TSO64.State} {action : Action} {first : OS.TSO64.State × Observation}
    (current : Current method state)
    (actual : OS.TSO64.step state action .sharedCell = .ok first)
    (observed : first.2 = .returned tid) {after : Worker}
    (live : first.1.workers[tid]? = some after) : after.phase = .returned := by
  have shaped : first = (first.1, .returned tid) := Prod.ext rfl observed
  have executed : OS.TSO64.step state action .sharedCell = .ok (first.1, .returned tid) := by
    exact actual.trans (congrArg Except.ok shaped)
  obtain ⟨value, _, origin⟩ := Return.returned_origin current.valid executed
  obtain ⟨_, _, worker, _, workerLive, _, phase, _⟩ := origin.frame
  have same : worker = after := Option.some.inj (workerLive.symm.trans live)
  simpa only [same] using phase

private theorem done_schedule {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {worker : Worker} {reply : method.operation.Reply} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method (.done reply) worker)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result) {final : Worker}
    (finalLive : result.1.workers[tid]? = some final) :
    At method (.done reply) final ∧
      ∀ index : Nat, result.2[index]? ≠ some (Observation.returned tid) := by
  obtain ⟨_, point, after, emissions, afterLive, atAfter, progress, replies, _⟩ :=
    schedule_preserves current live located success
  have same : after = final := Option.some.inj (afterLive.symm.trans finalLive)
  subst after
  have zero : point.remaining = 0 := by
    have : point.remaining + ownIssues tid actions = 0 := progress
    omega
  obtain ⟨finalReply, rfl⟩ := atAfter.returned_done (atAfter.zero_returned zero)
  have equal : reply = finalReply := by
    change (reply :: emissions.filterMap id) = [finalReply] at replies
    exact (List.cons.inj replies).1
  subst finalReply
  refine ⟨atAfter, ?_⟩
  intro index found
  obtain ⟨before, action, next, prefixRun, selected, actual⟩ :=
    ScheduleTrace.observation_at success found
  obtain ⟨prefixCurrent, prefixPoint, prefixWorker, _, prefixLive, prefixAt,
    prefixProgress, _, _⟩ := schedule_preserves current live located prefixRun
  have prefixZero : prefixPoint.remaining = 0 := by
    have : prefixPoint.remaining + ownIssues tid (actions.take index) = 0 := prefixProgress
    omega
  have returned := prefixAt.zero_returned prefixZero
  obtain ⟨value, _, origin⟩ := Return.returned_origin prefixCurrent.valid actual
  obtain ⟨af, issuing, output, observation, _, issuingLive, running, _⟩ := origin
  have same : issuing = prefixWorker := Option.some.inj (issuingLive.symm.trans prefixLive)
  subst issuing
  exact running returned

/-- Internal witness retaining the prefix annotation from the same proof of
progress. Its conservation equation establishes that the access preceded RET;
no intermediate cutpoint is accepted from the caller. -/
private structure ResponsePrefix (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (point : Point method.operation) (actions : List Action)
    (result : OS.TSO64.State × List Observation) (final : Worker) where
  index : Nat
  reply : method.operation.Reply
  before : OS.TSO64.State
  action : Action
  next : OS.TSO64.State
  beforeWorker : Worker
  offset : Nat
  emissions : List (Option method.operation.Reply)
  prefixRun : schedule state (actions.take index) .sharedCell = .ok (before, result.2.take index)
  selected : actions[index]? = some action
  observed : result.2[index]? = some (.returned tid)
  actual : OS.TSO64.step before action .sharedCell = .ok (next, .returned tid)
  live : before.workers[tid]? = some beforeWorker
  located : At method (.ret offset reply) beforeWorker
  trace : AccessTrace method tid state (actions.take index) (before, result.2.take index) emissions
  replies : point.replies ++ emissions.filterMap id = [reply]
  finalAt : At method (.done reply) final
  unique : ∀ other, result.2[other]? = some (.returned tid) → other = index

private theorem ret_actual {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {worker : Worker} {offset : Nat} {reply : method.operation.Reply}
    (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method (.ret offset reply) worker) (af : Bool) :
    OS.TSO64.step state (.issue tid af) .sharedCell =
      .ok (install state tid state.world (ManagedReturn.returnedWorker worker method.returnAddress),
        .returned tid) := by
  have fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩
      worker.resources.code.loan.region := by rw [located.resources]; exact current.fits
  have caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok method.returnAddress := by
    rw [located.resources]; exact current.caller
  have stack : worker.context.registers .rsp = worker.resources.callerAddress := by
    rw [located.resources]
    exact located.ret_rsp
  exact ManagedReturn.step_ret located.location.2.2.2.1 method.size current.valid live
    located.location.1 current.code fits located.location.2.1 stack caller
    method.returnCanonical af

/-- Find the response by following actual progress from a running cutpoint.
The recursive construction retains the actual prefix access annotation. -/
private theorem find_response {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (running : worker.phase = .running) {actions : List Action}
    {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result) {final : Worker}
    (finalLive : result.1.workers[tid]? = some final) (returned : final.phase = .returned) :
    Nonempty (ResponsePrefix method tid state point actions result final) := by
  induction actions generalizing state point worker result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    have sameWorker : worker = final := Option.some.inj (live.symm.trans finalLive)
    subst final
    rw [running] at returned
    cases returned
  | cons action rest ih =>
    obtain ⟨first, tail, actual, following, resultEq⟩ := schedule_cons_ok success
    obtain ⟨middle, after, emitted, afterLive, atAfter, progress, replies, capture⟩ :=
      step_preserves current live located actual
    have tailLive : tail.1.workers[tid]? = some final := by simpa only [resultEq] using finalLive
    by_cases afterReturned : after.phase = .returned
    · obtain ⟨reply, rfl⟩ := atAfter.returned_done afterReturned
      have retPoint : ∃ offset, point = .ret offset reply := by
        cases point with
        | preamble offset padding =>
          have bound := ownIssue_le_one tid action
          simp only [Point.remaining] at progress
          omega
        | done previous =>
          have phase := located.location.1
          rw [running] at phase
          cases phase
        | ret offset previous =>
          have equal : previous = reply := by
            change (previous :: emitted.toList) = [reply] at replies
            exact (List.cons.inj replies).1
          subst previous
          exact ⟨offset, rfl⟩
      obtain ⟨offset, rfl⟩ := retPoint
      have issueCount : ownIssue tid action = 1 := by
        simpa only [Point.remaining, Nat.zero_add] using progress
      obtain ⟨af, actionEq⟩ := ownIssue_eq_one issueCount
      subst action
      have exactStep := ret_actual current live located af
      have sameFirst := Except.ok.inj (actual.symm.trans exactStep)
      have observed : first.2 = .returned tid := congrArg Prod.snd sameFirst
      have shaped : first = (first.1, .returned tid) := Prod.ext rfl observed
      have executed : OS.TSO64.step state (.issue tid af) .sharedCell =
          .ok (first.1, .returned tid) := actual.trans (congrArg Except.ok shaped)
      obtain ⟨finalAt, noLater⟩ :=
        done_schedule (current.step actual) afterLive atAfter following tailLive
      refine ⟨⟨0, reply, state, .issue tid af, first.1, worker, offset, [], rfl, rfl,
        ?_, executed, live, located, .nil state, rfl, finalAt, ?_⟩⟩
      · simpa only [resultEq, List.getElem?_cons_zero] using congrArg some observed
      · intro other selected
        cases other with
        | zero => rfl
        | succ other =>
          have later : tail.2[other]? = some (.returned tid) := by
            simpa only [resultEq, List.getElem?_cons_succ] using selected
          exact False.elim (noLater other later)
    · have afterRunning : after.phase = .running := by
        cases phase : after.phase with
        | running => rfl
        | returned => exact False.elim (afterReturned phase)
      have noHead : first.2 ≠ .returned tid := by
        intro observed
        exact afterReturned (returned_step_phase current actual observed afterLive)
      obtain ⟨found⟩ := ih (current.step actual) afterLive atAfter afterRunning following tailLive
      refine ⟨⟨found.index + 1, found.reply, found.before, found.action, found.next,
        found.beforeWorker, found.offset, emitted :: found.emissions, ?_, ?_, ?_,
        found.actual, found.live, found.located, ?_, ?_, found.finalAt, ?_⟩⟩
      · simp only [List.take_succ_cons, schedule, actual, ok_bind, found.prefixRun, pure_ok,
          resultEq]
      · simpa only [List.getElem?_cons_succ] using found.selected
      · simpa only [resultEq, List.getElem?_cons_succ] using found.observed
      · simpa only [List.take_succ_cons, resultEq] using AccessTrace.cons actual capture found.trace
      · rw [reply_filter_cons, ← List.append_assoc, replies]
        exact found.replies
      · intro other selected
        cases other with
        | zero =>
          have observed : first.2 = .returned tid := by
            simpa only [resultEq, List.getElem?_cons_zero, Option.some.injEq] using selected
          exact False.elim (noHead observed)
        | succ other =>
          have later : tail.2[other]? = some (.returned tid) := by
            simpa only [resultEq, List.getElem?_cons_succ] using selected
          exact congrArg Nat.succ (found.unique other later)

/-- An indexed access in a real prefix remains at the original position in
the full schedule. Neither action nor observation positions are compressed. -/
private theorem access_prefix {method : Method} {tid : Nat} {state before : OS.TSO64.State}
    {actions : List Action} {observations : List Observation} {length index : Nat}
    {reply : method.operation.Reply}
    (access : AccessAt method tid state (actions.take length)
      (before, observations.take length) index reply) :
    AccessAt method tid state actions (before, observations) index reply ∧ index < length := by
  obtain ⟨prior, action, first, prefixRun, selected, observed, actual, origin⟩ := access
  have bound : index < (actions.take length).length := (List.getElem_of_getElem? selected).1
  have earlier : index < length := Nat.lt_of_lt_of_le bound (List.length_take_le length actions)
  have prefixEq : (actions.take length).take index = actions.take index := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlier)]
  have observationsEq : (observations.take length).take index = observations.take index := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlier)]
  refine ⟨⟨prior, action, first, ?_, ?_, ?_, actual, origin⟩, earlier⟩
  · simpa only [prefixEq, observationsEq] using prefixRun
  · simpa only [List.getElem?_take, earlier, ↓reduceIte] using selected
  · simpa only [List.getElem?_take, earlier, ↓reduceIte] using observed

/-- A postcondition witness extracted from a completed machine invocation.
Both events retain their original action positions. Coverage is independent
of chosen annotation payloads: every own MOV64 and every own RET is covered. -/
structure CompletedCall (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (actions : List Action) (result : OS.TSO64.State × List Observation) where
  execution : schedule state actions .sharedCell = .ok result
  reply : method.operation.Reply
  performed : Nat
  returned : Nat
  access : AccessAt method tid state actions result performed reply
  oneAccess : OneAccess method tid state actions result reply
  response : ResponseAt method tid state actions result returned reply
  beforeReturn : performed < returned
  responseUnique : ∀ other, result.2[other]? = some (.returned tid) → other = returned

/-- Logical occurrence is supplied separately from the actual machine store
counter. Invocation denotes the admitted initial entry boundary. -/
def CompletedCall.call {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (completed : CompletedCall method tid state actions result) (occurrence : Nat) :
    Concurrency.AtomicCalls.Call Atomics64.CellId64 Word where
  thread := tid
  occurrence := occurrence
  request := method.request
  reply := method.requestReply completed.reply
  invoked := 0
  performed := completed.performed
  returned := completed.returned

theorem CompletedCall.intervals {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (completed : CompletedCall method tid state actions result) (occurrence : Nat) :
    (completed.call occurrence).invoked ≤ (completed.call occurrence).performed ∧
      (completed.call occurrence).performed < (completed.call occurrence).returned :=
  ⟨Nat.zero_le _, completed.beforeReturn⟩

/-- The independent call event uses the intended acquire/release request and
actual access reply. This is source-event classification, not publication or
universal C23 legality. -/
def Operation.access (operation : Operation) (entry : Register → Word) :
    operation.Reply → Concurrency.C23Atomic.Access Word :=
  match operation with
  | .load _ => fun value => .load .acquire value
  | .store _ source => fun _ => .store .release (entry source)

theorem CompletedCall.event_access {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (completed : CompletedCall method tid state actions result) (occurrence : Nat) :
    (completed.call occurrence).event.access =
      method.operation.access method.entry completed.reply := by
  cases method with
  | mk bytes operation base entry entryFlags resources reference returnAddress initialQueue
      size codeNoWrap originalRsp returnCanonical stackNoWrap =>
    cases operation <;> rfl

/-- Every successful completed invocation has an actual unique RET response,
one actual managed access strictly earlier, and the retained saved reply.
Only present admission, a real successful schedule, and its final worker phase
are premises. Future cutpoints, desired responses and histories are derived. -/
theorem completed_call {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {padding : List Padding} {initial : Worker} (current : Current method state)
    (live : state.workers[tid]? = some initial) (entry : At method (.preamble 0 padding) initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result) {final : Worker}
    (finalLive : result.1.workers[tid]? = some final) (returned : final.phase = .returned) :
    Nonempty (CompletedCall method tid state actions result) := by
  obtain ⟨found⟩ := find_response current live entry entry.location.1 success finalLive returned
  have single : found.emissions.filterMap id = [found.reply] := by
    simpa only [Point.replies, List.nil_append] using found.replies
  obtain ⟨performed, prefixAccess, _⟩ := found.trace.one_access single
  obtain ⟨access, beforeReturn⟩ := access_prefix prefixAccess
  obtain ⟨_, reply, body, one, _, _⟩ := all_completed current live entry success finalLive returned
  have sameReply : reply = found.reply := by
    have both : method.responded reply .rax = method.responded found.reply .rax :=
      body.rax.symm.trans found.finalAt.done_post.rax
    exact reply_eq both
  subst reply
  obtain ⟨prefixCurrent, _, _, _, _, _, _, _, _⟩ := schedule_preserves current live entry found.prefixRun
  obtain ⟨point, after, emitted, afterLive, afterAt, _, replies, _⟩ :=
    step_preserves prefixCurrent found.live found.located found.actual
  have nextReturned : after.phase = .returned :=
    returned_step_phase prefixCurrent found.actual rfl afterLive
  obtain ⟨reply, rfl⟩ := afterAt.returned_done nextReturned
  have equal : found.reply = reply := by
    change (found.reply :: emitted.toList) = [reply] at replies
    exact (List.cons.inj replies).1
  subst reply
  have nextAt : At method (.done found.reply) after := afterAt
  have responded := At.done_returnValue afterLive nextAt
  have origin := At.return_origin prefixCurrent.valid found.actual afterLive nextAt
  exact ⟨⟨success, found.reply, performed, found.index, access, one,
    ⟨found.before, found.action, found.next, found.prefixRun, found.selected, found.observed,
      found.actual, responded, origin⟩, beforeReturn, found.unique⟩⟩

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
