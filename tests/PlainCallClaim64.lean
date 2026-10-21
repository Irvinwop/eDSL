/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallClaim64
import EDSL.Corpus.V1.PlainClaims
import tests.PlainCallHistory64

/-!
Nonempty clients of the complete independent registered contract. Completion
starts after a real load and RET with mixed incoming queues still present; the
returned worker contributes no issue to the chosen suffix. The closed client
then checks exact full64 calls, INITIAL source and publication-derived rank
through the full Claim, using the actual store-RET/load/publication/reader-RET
execution. Existing checked setup and instruction execution are reused.
No entire-ELF resource inhabitant or compiler-corpus credit is claimed here.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainCallClaim64
open X86 OS.TSO64 OS.TSO64.C23Projection Concurrency
open Grading.ConcurrentTask

private instance : DecidableEq (List AtomicTrace.Event) := inferInstance
private instance : DecidableEq (Option (List AtomicTrace.Event)) := inferInstance
private instance : DecidableEq (List PublishedHistory.Stamp) := inferInstance
private instance : DecidableEq (List (Option Nat) × List Nat) := inferInstance

theorem registered : Plain64.Claim PlainCallAdmission64.catalog :=
  OS.PlainCallClaim64.claim PlainCallAdmission64.separateStaticShapes

def prior : List Action := [.issue 0 false, .issue 0 true]
def priorResult : OS.TSO64.State × List Observation :=
  (PlainCallAdmission64.loadReturned.1,
    [PlainCallAdmission64.loaded.2, PlainCallAdmission64.loadReturned.2])

theorem prior_actual : schedule PlainCallAdmission64.initial prior .sharedCell = .ok priorResult := by
  simp only [prior, priorResult, schedule, PlainCallAdmission64.load_actual,
    PlainCallAdmission64.load_return_actual, ok_bind, pure_ok]

private theorem prior_returned {worker : Worker}
    (live : priorResult.1.workers[0]? = some worker) : worker.phase = .returned := by
  have observed : priorResult.1.workers[0]?.map Worker.phase = some .returned := by decide +kernel
  rw [live, Option.map_some] at observed
  exact Option.some.inj observed

/-- Arbitrary thread-local AF choices are retained after a real partial run.
The generic completion recovers points internally, skips the returned reader,
and supplies the full independent Post for the concatenated execution. -/
theorem chosen_completion (choices : Nat → Nat → Bool) :
    ∃ suffix result,
      Plain64.ChosenIssues choices suffix ∧ Plain64.issues 0 suffix = 0 ∧
      schedule priorResult.1 suffix .sharedCell = .ok result ∧ Returned result.1 ∧
      schedule PlainCallAdmission64.initial (prior ++ suffix) .sharedCell =
        .ok (result.1, priorResult.2 ++ result.2) ∧
      Nonempty (Plain64.Post PlainCallAdmission64.initial PlainCallAdmission64.inputs
        (prior ++ suffix) (result.1, priorResult.2 ++ result.2)) := by
  obtain ⟨cuts, result, completed, chosen, appended, post⟩ :=
    OS.PlainCallCompletion64.complete PlainCallAdmission64.separateStaticShapes
      PlainCallAdmission64.independentPre prior_actual choices
  have returned : (cuts PlainCallAdmission64.readerSlot).cut.worker.phase = .returned :=
    prior_returned (cuts PlainCallAdmission64.readerSlot).cut.live
  have skipped := OS.PlainCallCompletion64.returned_issues_zero completed
    PlainCallAdmission64.readerSlot returned
  exact ⟨_, result, chosen, skipped, completed.scheduled, completed.returned, appended, post⟩

private theorem literal_scan :
    (AtomicTrace.scan PlainCallHistory64.initial PlainCallHistory64.actions .sharedCell 0
      PublishedHistory.empty).toOption.map AtomicTrace.Result.events =
      some [⟨0, 1, .store PlainCallHistory64.writerReference PlainCallAdmission64.storeWord 11⟩,
        ⟨2, 0, .load PlainCallHistory64.readerReference PlainCallAdmission64.oldWord
          (.initial PlainCallAdmission64.target)⟩] := by decide +kernel

private theorem literal_publication : writes 0 PlainCallHistory64.result.2 =
    [⟨3, .buffered 1 PlainCallHistory64.writerReference PlainCallAdmission64.storeWord 11⟩] := by
  decide +kernel

/-- Full registered closed behavior has the actual old read and INITIAL source
although the writer already returned, and its rank is publication 3 plus one.
The independent full Post's call list retains original access positions. -/
theorem closed_history :
    ∃ post : Plain64.ClosedPost PlainCallHistory64.initial PlainCallHistory64.inputs
        PlainCallHistory64.actions PlainCallHistory64.result,
      post.calls.calls.map (fun call => (call.performed, call.event)) =
        [(0, ⟨some 1, PlainCallAdmission64.target, .store .release PlainCallAdmission64.storeWord⟩),
         (2, ⟨some 0, PlainCallAdmission64.target, .load .acquire PlainCallAdmission64.oldWord⟩)] ∧
      post.table.sources = [none, none, some 0] ∧ post.table.ranks = [0, 4, 0] := by
  obtain ⟨post⟩ := registered.whole PlainCallHistory64.initial PlainCallHistory64.inputs
    PlainCallHistory64.independentClosedPre PlainCallHistory64.actions
    PlainCallHistory64.result PlainCallHistory64.scheduled PlainCallHistory64.finished
  have expected := literal_scan
  rw [post.captured.scanned] at expected
  have emitted : post.run.events =
      [⟨0, 1, .store PlainCallHistory64.writerReference PlainCallAdmission64.storeWord 11⟩,
       ⟨2, 0, .load PlainCallHistory64.readerReference PlainCallAdmission64.oldWord
         (.initial PlainCallAdmission64.target)⟩] := Option.some.inj expected
  have initialized : post.initials =
      [⟨PlainCallAdmission64.target, PlainCallAdmission64.cell, PlainCallAdmission64.oldWord⟩] :=
    Except.ok.inj (post.captured.enumerated.symm.trans PlainCallHistory64.literal_initials)
  have observations : post.run.observations = PlainCallHistory64.result.2 :=
    congrArg Prod.snd post.execution
  have metadata : (AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs post.initials post.run 0)
      Plain64.orders).map (fun table => (table.sources, table.ranks)) =
      some ([none, none, some 0], [0, 4, 0]) := by
    change (AtomicTrace.Graph.build ⟨post.initials, post.run.events, writes 0 post.run.observations⟩
      Plain64.orders).map (fun table => (table.sources, table.ranks)) = _
    rw [initialized, emitted, observations, literal_publication]
    decide +kernel
  rw [post.built, Option.map_some] at metadata
  have exactMetadata := Option.some.inj metadata
  have positioned := post.positioned_events
  have erased : post.run.events.map (fun event => (event.position, event.toSource Plain64.orders)) =
      [(0, (⟨some 1, PlainCallAdmission64.target, .store .release PlainCallAdmission64.storeWord⟩ :
          C23Atomic.Event OS.Atomics64.CellId64 Word)),
       (2, ⟨some 0, PlainCallAdmission64.target, .load .acquire PlainCallAdmission64.oldWord⟩)] := by
    rw [emitted]
    simp only [List.map_cons, List.map_nil, AtomicTrace.Event.toSource,
      AtomicTrace.Event.object, Plain64.orders, PlainCallHistory64.readerReference,
      PlainCallHistory64.writerReference, PlainCallAdmission64.target]
  refine ⟨post, ?_, congrArg Prod.fst exactMetadata, congrArg Prod.snd exactMetadata⟩
  simpa only [Nat.zero_add] using positioned.symm.trans erased

end EDSL.Tests.PlainCallClaim64

#print axioms EDSL.Tests.PlainCallClaim64.registered
#print axioms EDSL.Tests.PlainCallClaim64.chosen_completion
#print axioms EDSL.Tests.PlainCallClaim64.closed_history
#audit_edsl
