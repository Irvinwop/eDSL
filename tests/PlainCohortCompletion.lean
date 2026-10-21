/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Completion
import tests.PlainMethodHistories

/-!
Resume the real two-slot history after the writer's store and RET. The generic
completion theorem must construct the reader's two issues from this raw prefix;
the returned writer must receive no issue. Its exact managed FIFO survives both
reader instructions and is published by a separate actual drain closure.

Expected observations, AF choices, counts, queues, responses and RAM words are
literal requirements. Checks of a successful run are deliberately true on an
error: they cannot supply future success to the theorem under test. Success
comes exclusively from cohort completion and its optional closing certificate.
No instruction proof, desired future cutpoint or future-success fixture is used.

Source-only scope: sharedCell, scalar RAM, long mode with CET off, initialized
stable resources and one invocation per fixed worker slot. No native, source,
compiler, kernel, fairness or compiler-corpus claim is made by this client.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainCohortCompletion
open X86 OS.TSO64 X86.VCGen.PlainMethods
open X86.VCGen.AtomicMethods (ownIssues)
open PlainMethodHistories (initial invocations)

private instance : DecidableEq (List Pending) := inferInstance
private instance : DecidableEq (List (List Pending)) := inferInstance
private instance : DecidableEq (List (Except Error Word)) := inferInstance
private instance : DecidableEq (List (Option (Nat × Word))) := inferInstance

def readerSlot : Fin initial.workers.length :=
  ⟨0, by rw [PlainMethodHistories.initial_length]; decide⟩

def writerSlot : Fin initial.workers.length :=
  ⟨1, by rw [PlainMethodHistories.initial_length]; decide⟩

def prefixActions : List Action := PlainMethodHistories.actions.take 2

def actualPrefix : OS.TSO64.State × List Observation :=
  (PlainMethodHistories.storeReturned.1,
    [PlainMethodHistories.stored.2, PlainMethodHistories.storeReturned.2])

/-- Reuse only the two existing production-step proofs at this boundary. -/
theorem prefix_actual : schedule initial prefixActions .sharedCell = .ok actualPrefix := by
  change schedule initial [.issue 1 true, .issue 1 false] .sharedCell =
    .ok (PlainMethodHistories.storeReturned.1,
      [PlainMethodHistories.stored.2, PlainMethodHistories.storeReturned.2])
  simp only [schedule, PlainMethodHistories.store_actual,
    PlainMethodHistories.store_return_actual, ok_bind, pure_ok]

-- Use the proved prefix interface during elaboration; kernel checks still
-- unfold its complete concrete setup and scheduler definitions.
attribute [local irreducible] actualPrefix

-- The first suffix issue chooses false and the second true at reader slot 0.
-- A mistaken use of the global action offset would lose the second true.
def choices (tid offset : Nat) : Bool := decide (tid + offset = 1)

abbrev PrefixCuts := (tid : Fin initial.workers.length) →
  InvocationCut (invocations tid) prefixActions actualPrefix

def suffix (cuts : PrefixCuts) : List Action :=
  cohortActions (fun tid => (cuts tid).cut.point) choices

private theorem finRange_two {n : Nat} (two : n = 2) (first second : Fin n)
    (firstValue : first.val = 0) (secondValue : second.val = 1) :
    List.finRange n = [first, second] := by
  subst n
  have firstEq : first = (⟨0, by decide⟩ : Fin 2) := Fin.ext firstValue
  have secondEq : second = (⟨1, by decide⟩ : Fin 2) := Fin.ext secondValue
  rw [firstEq, secondEq]
  decide +kernel

/-- Counts come from the prefix annotation, independently of any suffix run. -/
theorem remaining_counts (cuts : PrefixCuts) :
    (cuts readerSlot).cut.point.remaining = 2 ∧
      (cuts writerSlot).cut.point.remaining = 0 := by
  have readerProgress := (cuts readerSlot).progress
  have writerProgress := (cuts writerSlot).progress
  have readerPadding : (invocations readerSlot).padding = [] := by rfl
  have writerPadding : (invocations writerSlot).padding = [] := by rfl
  have readerIssued : ownIssues readerSlot.val prefixActions = 0 := by rfl
  have writerIssued : ownIssues writerSlot.val prefixActions = 2 := by rfl
  rw [readerPadding, readerIssued] at readerProgress
  rw [writerPadding, writerIssued] at writerProgress
  simp only [List.length_nil] at readerProgress writerProgress
  exact ⟨by omega, by omega⟩

/-- Enumerate the entire initial universe, including the already returned slot. -/
theorem exact_suffix (cuts : PrefixCuts) :
    suffix cuts = [.issue 0 false, .issue 0 true] := by
  obtain ⟨readerRemaining, writerRemaining⟩ := remaining_counts cuts
  unfold suffix cohortActions cohortActionsFor
  rw [finRange_two PlainMethodHistories.initial_length readerSlot writerSlot rfl rfl]
  change remainingIssues 0 (cuts readerSlot).cut.point.remaining (choices 0) ++
    (remainingIssues 1 (cuts writerSlot).cut.point.remaining (choices 1) ++ []) = _
  rw [readerRemaining, writerRemaining]
  rfl

-- These are observations of the actual production prefix, not a proposed
-- initial machine state. The reader's earlier ordinary entry has drained, but
-- its allocation counter is still one. The writer has already returned.
theorem prefix_observations : actualPrefix.2 = [.ordinary 1, .returned 1] := by
  decide +kernel

theorem prefix_counters : actualPrefix.1.workers.map Worker.nextStore = [1, 1] := by
  decide +kernel

theorem prefix_queues : actualPrefix.1.workers.map Worker.pending =
    [[], [.managed PlainCallBatch.peerReference 0xfedcba9876543210 0]] := by
  decide +kernel

theorem prefix_writer_returned :
    (actualPrefix.1.workers[1]?).map Worker.phase = some .returned := by
  decide +kernel

theorem prefix_writer_response : Return.returnValue PlainMethodHistories.storeReturned =
    some (1, 5) := by
  decide +kernel

/-- Observe the actual result without comparing world functions or reconstructing
an expected machine state. Queues retain full managed references, not summaries. -/
structure RuntimeView where
  observations : List Observation
  counters : List Nat
  queues : List (List Pending)
  responses : List (Option (Nat × Word))
  words : List (Except Error Word)
  deriving DecidableEq

def runtimeView (output : OS.TSO64.State × List Observation) : RuntimeView :=
  ⟨output.2, output.1.workers.map Worker.nextStore, output.1.workers.map Worker.pending,
    [Return.returnValue (output.1, .returned 0), Return.returnValue (output.1, .returned 1)],
    PlainMethods.worldWords output.1⟩

def expectedResume : RuntimeView :=
  ⟨[.ordinary 0, .returned 0], [1, 1],
    [[], [.managed PlainCallBatch.peerReference 0xfedcba9876543210 0]],
    [some (0, 0x1122334455667788), some (1, 5)],
    [.ok 9, .ok 0, .ok 0x1122334455667788, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]⟩

def expectedClosed : RuntimeView :=
  ⟨[.ordinary 0, .returned 0,
      .drained 1 (.managed PlainCallBatch.peerReference 0xfedcba9876543210 0)],
    [1, 1], [[], []], [some (0, 0x1122334455667788), some (1, 5)],
    [.ok 9, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]⟩

-- A failed attempt satisfies this check as well. These finite checks therefore
-- establish no future success; a production completion certificate is needed.
private def onSuccess {ε α : Type} (attempt : Except ε α) (property : α → Prop) : Prop :=
  match attempt with
  | .error _ => True
  | .ok output => property output

private instance {ε α : Type} (attempt : Except ε α) (property : α → Prop)
    [DecidablePred property] : Decidable (onSuccess attempt property) := by
  cases attempt <;> dsimp only [onSuccess] <;> infer_instance

private theorem onSuccess_apply {ε α : Type} {attempt : Except ε α}
    {property : α → Prop} {output : α} (success : attempt = .ok output)
    (checked : onSuccess attempt property) : property output := by
  rw [success] at checked
  exact checked

attribute [local irreducible] onSuccess

private theorem resume_check :
    onSuccess (schedule actualPrefix.1 [.issue 0 false, .issue 0 true] .sharedCell)
      (fun output => runtimeView output = expectedResume) := by
  decide +kernel

private theorem closed_check :
    onSuccess (schedule actualPrefix.1 [.issue 0 false, .issue 0 true, .drain 1] .sharedCell)
      (fun output => runtimeView output = expectedClosed) := by
  decide +kernel

/-- An already returned writer retains its literal context, full resources,
FIFO and counter throughout the constructed reader-only suffix. -/
theorem writer_unchanged (cuts : PrefixCuts) (output : OS.TSO64.State × List Observation)
    (completion : CohortCompletion (fun tid => (cuts tid).cut) choices output) :
    output.1.workers[1]? = actualPrefix.1.workers[1]? := by
  have scheduled : schedule actualPrefix.1 [.issue 0 false, .issue 0 true] .sharedCell =
      .ok output := by
    have actual := completion.scheduled
    change schedule actualPrefix.1 (suffix cuts) .sharedCell = .ok output at actual
    simpa only [exact_suffix cuts] using actual
  have only : ∀ action ∈ ([.issue 0 false, .issue 0 true] : List Action),
      ∃ af, action = .issue 0 af := by
    intro action member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨false, rfl⟩
    · have same : action = .issue 0 true := List.mem_singleton.mp later
      exact ⟨true, same⟩
  exact completion_schedule_peer only scheduled (by decide)

/-- The actual prefix's typed store reply remains the completed writer reply. -/
def SavedPrefixReply (cuts : PrefixCuts) (output : OS.TSO64.State × List Observation) : Prop :=
  ∃ saved : (invocations writerSlot).method.operation.Reply,
      (cuts writerSlot).emissions.filterMap id = [saved] ∧
      ∃ after, output.1.workers[1]? = some after ∧
        At (invocations writerSlot).method (.done saved) after ∧
        BodyPost (invocations writerSlot).method after saved

/-- Exercise prefix_reply on a reply recovered from this actual nonempty
prefix. It remains a typed reply at the final writer cutpoint. -/
theorem saved_prefix_reply (cuts : PrefixCuts) (output : OS.TSO64.State × List Observation)
    (completion : CohortCompletion (fun tid => (cuts tid).cut) choices output) :
    SavedPrefixReply cuts output := by
  have phase : (cuts writerSlot).cut.worker.phase = .returned := by
    have observed := prefix_writer_returned
    have live : actualPrefix.1.workers[1]? = some (cuts writerSlot).cut.worker :=
      (cuts writerSlot).cut.live
    rw [live] at observed
    exact Option.some.inj observed
  obtain ⟨saved, point⟩ := (cuts writerSlot).cut.located.returned_done phase
  have emitted : (cuts writerSlot).emissions.filterMap id = [saved] := by
    simpa only [point, Point.replies] using (cuts writerSlot).replies
  have member : saved ∈ (cuts writerSlot).emissions.filterMap id := by
    rw [emitted]
    exact List.mem_singleton_self saved
  exact ⟨saved, emitted,
    CohortCompletion.prefix_reply (initial := initial) (invocations := invocations)
      (cuts := cuts) completion writerSlot member⟩

/-- Full resources for every admitted slot, not merely a resource summary. -/
theorem original_resources (cuts : PrefixCuts) (output : OS.TSO64.State × List Observation)
    (completion : CohortCompletion (fun tid => (cuts tid).cut) choices output)
    (tid : Fin initial.workers.length) :
    ∃ after, output.1.workers[tid.val]? = some after ∧
      after.resources = (invocations tid).initial.resources := by
  obtain ⟨_, after, _, _, live, _, post, _⟩ := completion.completed tid
  exact ⟨after, live, post.resources.trans (invocations tid).entry.resources.symm⟩

/-- This helper accepts an existing actual certificate; the main client below
obtains that certificate from raw admission and prefix_actual. -/
theorem resumed_runtime (cuts : PrefixCuts) (output : OS.TSO64.State × List Observation)
    (completion : CohortCompletion (fun tid => (cuts tid).cut) choices output) :
    runtimeView output = expectedResume := by
  have scheduled : schedule actualPrefix.1 [.issue 0 false, .issue 0 true] .sharedCell =
      .ok output := by
    have actual := completion.scheduled
    change schedule actualPrefix.1 (suffix cuts) .sharedCell = .ok output at actual
    simpa only [exact_suffix cuts] using actual
  exact onSuccess_apply
    (attempt := schedule actualPrefix.1 [.issue 0 false, .issue 0 true] .sharedCell)
    (output := output) (property := fun result => runtimeView result = expectedResume)
    scheduled resume_check

private theorem drain_plan_two (workers : List Worker) (entry : Pending)
    (queues : workers.map Worker.pending = [[], [entry]]) :
    DrainClosure.actionsFrom 0 workers = [.drain 1] := by
  have length : workers.length = 2 := by
    have mapped := congrArg List.length queues
    simpa only [List.length_map, List.length_cons, List.length_nil] using mapped
  cases workers with
  | nil => simp only [List.length_nil] at length; contradiction
  | cons reader rest =>
    cases rest with
    | nil => simp only [List.length_cons, List.length_nil] at length; contradiction
    | cons writer tail =>
      have heads := List.cons.inj queues
      have rest := List.cons.inj heads.2
      have tailEmpty : tail = [] := List.length_eq_zero_iff.mp (by
        have length := congrArg List.length rest.2
        simpa only [List.length_map, List.length_nil] using length)
      subst tail
      simp only [DrainClosure.actionsFrom, heads.1, rest.1]
      rfl

/-- Publication has a separate one-drain plan, derived from the actual FIFO. -/
theorem exact_drain_plan (cuts : PrefixCuts) (output : OS.TSO64.State × List Observation)
    (completion : CohortCompletion (fun tid => (cuts tid).cut) choices output) :
    DrainClosure.actions output.1 = [.drain 1] := by
  have queues := congrArg RuntimeView.queues (resumed_runtime cuts output completion)
  change output.1.workers.map Worker.pending =
    [[], [.managed PlainCallBatch.peerReference 0xfedcba9876543210 0]] at queues
  exact drain_plan_two output.1.workers _ queues

/-- Raw-prefix client: the cohort theorem supplies successful completion and
the batch. Only then are its literal actions and observable results checked.
The drain certificate and Finished conclusion come from actual closure. -/
theorem integration_client :
    ∃ (cuts : PrefixCuts) (output closed : OS.TSO64.State × List Observation),
      CohortCompletion (fun tid => (cuts tid).cut) choices output ∧
      suffix cuts = [.issue 0 false, .issue 0 true] ∧
      ownIssues 0 (suffix cuts) = 2 ∧ ownIssues 1 (suffix cuts) = 0 ∧
      runtimeView output = expectedResume ∧
      output.1.workers[1]? = actualPrefix.1.workers[1]? ∧
      SavedPrefixReply cuts output ∧
      (∀ tid : Fin initial.workers.length, ∃ after,
        output.1.workers[tid.val]? = some after ∧
        after.resources = (invocations tid).initial.resources) ∧
      Nonempty (BatchResult initial (prefixActions ++ [.issue 0 false, .issue 0 true])
        (output.1, actualPrefix.2 ++ output.2) invocations) ∧
      DrainClosure.drainAll output.1 .sharedCell = .ok closed ∧
      DrainClosure.Certificate output.1 closed .sharedCell ∧
      DrainClosure.actions output.1 = [.drain 1] ∧
      closed.2 = [.drained 1 (.managed PlainCallBatch.peerReference 0xfedcba9876543210 0)] ∧
      runtimeView (closed.1, output.2 ++ closed.2) = expectedClosed ∧
      schedule initial (prefixActions ++ [.issue 0 false, .issue 0 true, .drain 1]) .sharedCell =
        .ok (closed.1, [.ordinary 1, .returned 1, .ordinary 0, .returned 0,
          .drained 1 (.managed PlainCallBatch.peerReference 0xfedcba9876543210 0)]) ∧
      Finished closed.1 ∧
      (∀ tid, Return.returnValue (closed.1, .returned tid) =
        Return.returnValue (output.1, .returned tid)) := by
  obtain ⟨cuts, output, completion, _appended, batch⟩ :=
    cohort_complete_after_prefix invocations prefix_actual choices
  have actions := exact_suffix cuts
  have runtime := resumed_runtime cuts output completion
  have readerCount : ownIssues 0 (suffix cuts) = 2 := by
    have count := completion.issueCount readerSlot
    have remaining := (remaining_counts cuts).1
    change ownIssues 0 (suffix cuts) = (cuts readerSlot).cut.point.remaining at count
    exact count.trans remaining
  have writerCount : ownIssues 1 (suffix cuts) = 0 := by
    have phase : (cuts writerSlot).cut.worker.phase = .returned := by
      have observed := prefix_writer_returned
      have live : actualPrefix.1.workers[1]? = some (cuts writerSlot).cut.worker :=
        (cuts writerSlot).cut.live
      rw [live] at observed
      exact Option.some.inj observed
    exact completion.returned_ownIssues_zero writerSlot phase
  have drainActions := exact_drain_plan cuts output completion
  have currentValid : WellFormed actualPrefix.1 .sharedCell :=
    schedule_wellFormed PlainMethodHistories.reader_current.valid prefix_actual
  obtain ⟨closed, drained, certificate, closedRun, finished, responses⟩ :=
    completion.close currentValid
  have closedScheduled : schedule actualPrefix.1
      [.issue 0 false, .issue 0 true, .drain 1] .sharedCell =
      .ok (closed.1, output.2 ++ closed.2) := by
    change schedule actualPrefix.1 (suffix cuts ++ DrainClosure.actions output.1)
      .sharedCell = .ok (closed.1, output.2 ++ closed.2) at closedRun
    simpa only [actions, drainActions, List.cons_append, List.nil_append] using closedRun
  have closedRuntime := onSuccess_apply
    (attempt := schedule actualPrefix.1 [.issue 0 false, .issue 0 true, .drain 1] .sharedCell)
    (output := (closed.1, output.2 ++ closed.2))
    (property := fun result => runtimeView result = expectedClosed) closedScheduled closed_check
  have combinedObservations := congrArg RuntimeView.observations closedRuntime
  change output.2 ++ closed.2 = [.ordinary 0, .returned 0,
    .drained 1 (.managed PlainCallBatch.peerReference 0xfedcba9876543210 0)] at combinedObservations
  have resumeObservations := congrArg RuntimeView.observations runtime
  change output.2 = [.ordinary 0, .returned 0] at resumeObservations
  have drainObservations : closed.2 =
      [.drained 1 (.managed PlainCallBatch.peerReference 0xfedcba9876543210 0)] := by
    rw [resumeObservations] at combinedObservations
    exact (List.cons.inj (List.cons.inj combinedObservations).2).2
  have fullRun := completion_schedule_append prefix_actual closedScheduled
  rw [prefix_observations, combinedObservations] at fullRun
  have literalBatch : Nonempty (BatchResult initial (prefixActions ++ [.issue 0 false, .issue 0 true])
      (output.1, actualPrefix.2 ++ output.2) invocations) := by
    change Nonempty (BatchResult initial (prefixActions ++ suffix cuts)
      (output.1, actualPrefix.2 ++ output.2) invocations) at batch
    simpa only [actions] using batch
  exact ⟨cuts, output, closed, completion, actions, readerCount, writerCount, runtime,
    writer_unchanged cuts output completion, saved_prefix_reply cuts output completion,
    original_resources cuts output completion, literalBatch, drained, certificate,
    drainActions, drainObservations, closedRuntime, fullRun, finished, responses⟩

end EDSL.Tests.PlainCohortCompletion

#print axioms EDSL.Tests.PlainCohortCompletion.prefix_actual
#print axioms EDSL.Tests.PlainCohortCompletion.remaining_counts
#print axioms EDSL.Tests.PlainCohortCompletion.exact_suffix
#print axioms EDSL.Tests.PlainCohortCompletion.saved_prefix_reply
#print axioms EDSL.Tests.PlainCohortCompletion.resumed_runtime
#print axioms EDSL.Tests.PlainCohortCompletion.integration_client
#audit_edsl
