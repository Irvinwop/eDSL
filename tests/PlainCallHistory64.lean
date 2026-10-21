/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallHistory64
import tests.PlainCallAdmission64

/-!
Independent closed admission to an actual constructed plain-call history.
Reuse the checked world, attached workers, code, callers, inputs and static
catalog of PlainCallAdmission64. This boundary has empty actual FIFOs and
arbitrary retained counters; it does not repeat resource construction or
invent prior issues. The generic admission proof admits any counter values.

The concrete writer stores and returns before publication. The reader then
loads the old full64 word, the writer publishes, and the reader returns its
saved old word. The history theorem receives independent ClosedPre, actual
schedule success and Finished only. Exact source identities and publication
ranks are independent observations checked after the theorem constructs its
own scanner, initializer manifest, graph and calls.

These are project-owned synthetic resources, not final-ELF or compiler-corpus
evidence. The existing finite sharedCell, scalar-RAM, long-mode/CET-off,
resource and translation/alias assumptions remain explicit model boundaries.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainCallHistory64
open X86 OS.TSO64 X86.VCGen.PlainMethods
open OS.TSO64.C23Projection Concurrency
open Grading.ConcurrentTask

private def exceptDecEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error first, .error second =>
      match decEq first second with
      | .isTrue same => .isTrue (congrArg Except.error same)
      | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok first, .ok second =>
      match decEq first second with
      | .isTrue same => .isTrue (congrArg Except.ok same)
      | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error _, .ok _ => .isFalse (fun same => by cases same)
  | .ok _, .error _ => .isFalse (fun same => by cases same)

private instance : DecidableEq (Except Error Word) := exceptDecEq
private instance : DecidableEq (Except Fault Word) := exceptDecEq
private instance : DecidableEq (List Phase) := inferInstance
private instance : DecidableEq (List Pending) := inferInstance
private instance : DecidableEq (List (List Pending)) := inferInstance
private instance : DecidableEq (List Observation) := inferInstance
private instance : DecidableEq (List AtomicTrace.Event) := inferInstance
private instance : DecidableEq (List AtomicTrace.Initials.Entry) := inferInstance
private instance : DecidableEq (List PublishedHistory.Stamp) := inferInstance
private instance : DecidableEq (Except Fault (List AtomicTrace.Event)) := exceptDecEq
private instance : DecidableEq (Except Fault (List AtomicTrace.Initials.Entry)) := exceptDecEq
private instance : DecidableEq (List (Option Nat) × List Nat) := inferInstance

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

attribute [local irreducible] PlainCallAdmission64.world PlainCallAdmission64.attachedReader
  PlainCallAdmission64.attachedWriter PlainCallAdmission64.authority

-- Only queue/counter state changes; code, callers, flags and all resource
-- descriptors remain the existing actual attached workers' descriptors.
private def emptyWorker (worker : Worker) (counter : Nat) : Worker :=
  { worker with pending := [], nextStore := counter }

def reader (counter : Nat) : Worker := emptyWorker PlainCallAdmission64.attachedReader counter
def writer (counter : Nat) : Worker := emptyWorker PlainCallAdmission64.attachedWriter counter

def initialWith (readerCounter writerCounter : Nat) : OS.TSO64.State :=
  ⟨PlainCallAdmission64.world, [reader readerCounter, writer writerCounter]⟩

def inputsWith (readerCounter writerCounter : Nat)
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) : Plain64.Input :=
  if tid.val = 0 then PlainCallAdmission64.readerInput else PlainCallAdmission64.writerInput

private theorem entry_empty {input : Plain64.Input} {before : OS.TSO64.State} {worker : Worker}
    (facts : Plain64.Entry input before worker) (workers : List Worker) (counter : Nat) :
    Plain64.Entry input ⟨before.world, workers⟩ (emptyWorker worker counter) where
  running := facts.running
  pc := facts.pc
  arguments := facts.arguments
  nonempty := facts.nonempty
  baseCanonical := facts.baseCanonical
  code := facts.code
  fits := facts.fits
  originalRsp := facts.originalRsp
  scalar := ⟨facts.scalar.aligned, facts.scalar.direction, facts.scalar.stackBound,
    facts.scalar.postStackCanonical⟩
  liveTarget := facts.liveTarget
  validCell := facts.validCell
  selected := facts.selected
  caller := facts.caller

theorem initialWith_valid (readerCounter writerCounter : Nat) :
    WellFormed (initialWith readerCounter writerCounter) .sharedCell := by
  refine ⟨PlainCallAdmission64.world_valid, ?_⟩
  intro worker member
  have alternatives : worker = reader readerCounter ∨ worker = writer writerCounter := by
    simpa only [initialWith, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] using member
  rcases alternatives with rfl | rfl
  · refine ⟨(PlainCallAdmission64.attached_valid.2 PlainCallAdmission64.attachedReader (by simp)).1, ?_⟩
    intro entry member
    cases member
  · refine ⟨(PlainCallAdmission64.attached_valid.2 PlainCallAdmission64.attachedWriter (by simp)).1, ?_⟩
    intro entry member
    cases member

theorem initialWith_empty (readerCounter writerCounter : Nat) :
    Quiescent (initialWith readerCounter writerCounter) := by
  intro worker member
  have alternatives : worker = reader readerCounter ∨ worker = writer writerCounter := by
    simpa only [initialWith, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] using member
  rcases alternatives with rfl | rfl <;> rfl

private theorem slot_cases {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) :
    tid.val = 0 ∨ tid.val = 1 := by
  have bound : tid.val < 2 := tid.isLt
  omega

private def oldSlot {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) :
    Fin PlainCallAdmission64.initial.workers.length := ⟨tid.val, tid.isLt⟩

private def originalWorker {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) : Worker :=
  if tid.val = 0 then PlainCallAdmission64.reader else PlainCallAdmission64.writer

private def currentWorker {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) : Worker :=
  if tid.val = 0 then reader readerCounter else writer writerCounter

private theorem old_live {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) :
    PlainCallAdmission64.initial.workers[tid.val]? = some (originalWorker tid) := by
  rcases slot_cases tid with zero | one
  · simpa [originalWorker, zero] using PlainCallAdmission64.reader_live
  · simpa [originalWorker, one] using PlainCallAdmission64.writer_live

private theorem current_live {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) :
    (initialWith readerCounter writerCounter).workers[tid.val]? = some (currentWorker tid) := by
  rcases slot_cases tid with zero | one
  · simp [initialWith, currentWorker, zero]
  · simp [initialWith, currentWorker, one]

private theorem current_resources {readerCounter writerCounter : Nat}
    (tid : Fin (initialWith readerCounter writerCounter).workers.length) :
    (currentWorker tid).resources = (originalWorker tid).resources := by
  by_cases zero : tid.val = 0
  · simp only [currentWorker, originalWorker, ite_eq_left zero]
    rfl
  · simp only [currentWorker, originalWorker, ite_eq_right zero]
    rfl

/-- Independent current-only admission is stable under replacing the queues
by actual empty boundary queues with arbitrary retained counters. Existing
code, scalar ABI, private callers and separation proofs are reused. -/
theorem independentPreWith (readerCounter writerCounter : Nat) :
    Plain64.Pre PlainCallAdmission64.catalog (initialWith readerCounter writerCounter)
      (inputsWith readerCounter writerCounter) := by
  refine ⟨initialWith_valid readerCounter writerCounter, ?_, ?_, ?_, ?_⟩
  · intro tid
    change (PlainCallAdmission64.inputs (oldSlot tid)).site ∈ PlainCallAdmission64.catalog
    exact PlainCallAdmission64.independentPre.selected (oldSlot tid)
  · intro tid
    rcases slot_cases tid with zero | one
    · refine ⟨reader readerCounter, ?_, ?_⟩
      · simp [initialWith, zero]
      · have facts := entry_empty PlainCallAdmission64.reader_entry
          [reader readerCounter, writer writerCounter] readerCounter
        simpa only [inputsWith, zero, ite_true, initialWith,
          PlainCallAdmission64.initial, PlainCallAdmission64.reader, reader, emptyWorker]
          using facts
    · refine ⟨writer writerCounter, ?_, ?_⟩
      · simp [initialWith, one]
      · have facts := entry_empty PlainCallAdmission64.writer_entry
          [reader readerCounter, writer writerCounter] writerCounter
        simpa only [inputsWith, one, ite_eq_right (by decide : (1 : Nat) ≠ 0), initialWith,
          PlainCallAdmission64.initial, PlainCallAdmission64.writer, writer, emptyWorker] using facts
  · intro i j first second different firstLive secondLive
    have firstEq : first = currentWorker i :=
      Option.some.inj (firstLive.symm.trans (current_live i))
    have secondEq : second = currentWorker j :=
      Option.some.inj (secondLive.symm.trans (current_live j))
    subst first
    subst second
    rw [current_resources, current_resources]
    exact PlainCallAdmission64.independentPre.privateCallers (oldSlot i) (oldSlot j)
      (originalWorker i) (originalWorker j)
      (fun same => different (Fin.ext (congrArg Fin.val same))) (old_live i) (old_live j)
  · intro i j caller callerLive
    have callerEq : caller = currentWorker j :=
      Option.some.inj (callerLive.symm.trans (current_live j))
    subst caller
    rw [current_resources]
    change OS.Ownership.Disjoint
      ⟨(PlainCallAdmission64.inputs (oldSlot i)).site.image.base,
        (PlainCallAdmission64.inputs (oldSlot i)).site.image.bytes.length⟩
      (originalWorker j).resources.caller.loan.region
    exact PlainCallAdmission64.independentPre.codeCallerSeparation (oldSlot i) (oldSlot j)
      (originalWorker j) (old_live j)

theorem independentClosedPreWith (readerCounter writerCounter : Nat) :
    Plain64.ClosedPre PlainCallAdmission64.catalog (initialWith readerCounter writerCounter)
      (inputsWith readerCounter writerCounter) :=
  ⟨independentPreWith readerCounter writerCounter, initialWith_empty readerCounter writerCounter⟩

-- Concrete nonzero counters are distinct from logical occurrence labels 41/93.
def initial : OS.TSO64.State := initialWith 7 11
def inputs : Fin initial.workers.length → Plain64.Input := inputsWith 7 11

theorem independentClosedPre : Plain64.ClosedPre PlainCallAdmission64.catalog initial inputs :=
  independentClosedPreWith 7 11

def storeAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step initial (.issue 1 true) .sharedCell
theorem store_succeeds : storeAttempt.toOption.isSome = true := by decide +kernel
def stored : OS.TSO64.State × Observation := checked storeAttempt store_succeeds
theorem store_actual : step initial (.issue 1 true) .sharedCell = .ok stored := checked_ok _ _

def storeReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step stored.1 (.issue 1 false) .sharedCell
theorem store_return_succeeds : storeReturnAttempt.toOption.isSome = true := by decide +kernel
def storeReturned : OS.TSO64.State × Observation := checked storeReturnAttempt store_return_succeeds
theorem store_return_actual : step stored.1 (.issue 1 false) .sharedCell = .ok storeReturned :=
  checked_ok _ _

def loadAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step storeReturned.1 (.issue 0 false) .sharedCell
theorem load_succeeds : loadAttempt.toOption.isSome = true := by decide +kernel
def loaded : OS.TSO64.State × Observation := checked loadAttempt load_succeeds
theorem load_actual : step storeReturned.1 (.issue 0 false) .sharedCell = .ok loaded := checked_ok _ _

def publicationAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step loaded.1 (.drain 1) .sharedCell
theorem publication_succeeds : publicationAttempt.toOption.isSome = true := by decide +kernel
def publishedStore : OS.TSO64.State × Observation := checked publicationAttempt publication_succeeds
theorem publication_actual : step loaded.1 (.drain 1) .sharedCell = .ok publishedStore :=
  checked_ok _ _

def readerReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step publishedStore.1 (.issue 0 true) .sharedCell
theorem reader_return_succeeds : readerReturnAttempt.toOption.isSome = true := by decide +kernel
def readerReturned : OS.TSO64.State × Observation := checked readerReturnAttempt reader_return_succeeds
theorem reader_return_actual : step publishedStore.1 (.issue 0 true) .sharedCell = .ok readerReturned :=
  checked_ok _ _

def actions : List Action :=
  [.issue 1 true, .issue 1 false, .issue 0 false, .drain 1, .issue 0 true]
def result : OS.TSO64.State × List Observation :=
  (readerReturned.1, [stored.2, storeReturned.2, loaded.2, publishedStore.2, readerReturned.2])

theorem scheduled : schedule initial actions .sharedCell = .ok result := by
  simp only [actions, result, schedule, store_actual, store_return_actual, load_actual,
    publication_actual, reader_return_actual, ok_bind, pure_ok]

attribute [local irreducible] result

theorem finished : Finished result.1 := by
  have phases : result.1.workers.map Worker.phase = [.returned, .returned] := by decide +kernel
  have queues : result.1.workers.map Worker.pending = [[], []] := by decide +kernel
  constructor
  · intro worker member
    have mapped : worker.phase ∈ result.1.workers.map Worker.phase :=
      List.mem_map.mpr ⟨worker, member, rfl⟩
    rw [phases] at mapped
    simpa using mapped
  · intro worker member
    have mapped : worker.pending ∈ result.1.workers.map Worker.pending :=
      List.mem_map.mpr ⟨worker, member, rfl⟩
    rw [queues] at mapped
    simpa using mapped

/-- Independent executable observations catch early-publication, low-word,
wrong-source, lost-reply, counter-reset and RET/collection regressions. -/
theorem literal_runtime :
    result.2 = [.ordinary 1, .returned 1, .ordinary 0,
      .drained 1 (.managed
        ⟨PlainCallAdmission64.ready.atomicB, ⟨12, PlainCallAdmission64.target⟩,
          PlainCallAdmission64.cell⟩ PlainCallAdmission64.storeWord 11), .returned 0] ∧
    storeReturned.1.workers[1]?.map (fun worker => Queue.occurrences worker.pending) = some [11] ∧
    collect storeReturned.1 1 = .error .resource ∧
    Return.returnValue readerReturned = some (0, PlainCallAdmission64.oldWord) ∧
    loadQWord (published result.1.world) 65536 = .ok PlainCallAdmission64.storeWord ∧
    collect result.1 0 = .ok PlainCallAdmission64.oldWord ∧ collect result.1 1 = .ok 5 ∧
    result.1.workers.map Worker.nextStore = [7, 12] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem actual_abi : Plain64.ReturnFrame initial result.1 inputs :=
  OS.PlainCallFrames64.returned_cohort PlainCallAdmission64.separateStaticShapes independentClosedPre.1
    scheduled finished.1

def readerReference : Queue.ManagedRef :=
  ⟨PlainCallAdmission64.ready.atomicA, PlainCallAdmission64.authority.1, PlainCallAdmission64.cell⟩
def writerReference : Queue.ManagedRef :=
  ⟨PlainCallAdmission64.ready.atomicB, ⟨12, PlainCallAdmission64.target⟩, PlainCallAdmission64.cell⟩

-- These are observations of the executable scanner and enumeration, not
-- premises passed to history_of_closed. That theorem constructs its own run.
theorem literal_scan :
    (AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty).map
      (fun run => run.events) = .ok
      [⟨37, 1, .store writerReference PlainCallAdmission64.storeWord 11⟩,
       ⟨39, 0, .load readerReference PlainCallAdmission64.oldWord (.initial PlainCallAdmission64.target)⟩] := by decide +kernel

theorem literal_initials : AtomicTrace.Initials.enumerate initial.world =
    .ok [⟨PlainCallAdmission64.target, PlainCallAdmission64.cell, PlainCallAdmission64.oldWord⟩] := by decide +kernel

theorem literal_publications : writes 37 result.2 =
    [⟨40, .buffered 1 writerReference PlainCallAdmission64.storeWord 11⟩] := by decide +kernel

theorem store_response : result.2[1]? = some (.returned 1) := by decide +kernel

private theorem observations_at_output {run : AtomicTrace.Result}
    {output : OS.TSO64.State × List Observation} (same : run.execution = output) :
    run.observations = output.2 := by
  simpa only [AtomicTrace.Result.execution] using congrArg Prod.snd same

/-- Actual independent admission and execution construct the complete History.
The old read resolves to INITIAL despite the writer's earlier RET. The store's
rank 41 is publication 40 plus one, not issue 37, RET 38 or filtered index. -/
theorem independent_closed_history :
    ∃ (run : AtomicTrace.Result) (initials : List AtomicTrace.Initials.Entry)
      (table : AtomicTrace.Graph.Table),
      run.execution = result ∧
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run 37)
        AtomicEvents.orders = some table ∧
      ∃ batch : BatchResult initial actions run.execution
          (OS.PlainCallAdmission64.invocations PlainCallAdmission64.separateStaticShapes independentClosedPre.1),
        AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
          batch.calls table.toCandidate ∧
        batch.calls.map (fun actual => (37 + actual.performed, actual.event)) =
          [(37, ⟨some 1, PlainCallAdmission64.target, .store .release PlainCallAdmission64.storeWord⟩),
           (39, ⟨some 0, PlainCallAdmission64.target, .load .acquire PlainCallAdmission64.oldWord⟩)] ∧
        table.sources = [none, none, some 0] ∧ table.ranks = [0, 41, 0] ∧
        (∃ store ∈ batch.calls, store.thread = 1 ∧ store.returned = 1) := by
  obtain ⟨run, initials, execution, captured, table, built, _mapped, batch, history⟩ :=
    OS.PlainCallHistory64.history_of_closed PlainCallAdmission64.separateStaticShapes
      independentClosedPre scheduled finished 37
  have observations := observations_at_output execution
  have manifest : initials = [⟨PlainCallAdmission64.target, PlainCallAdmission64.cell, PlainCallAdmission64.oldWord⟩] :=
    Except.ok.inj (captured.enumerated.symm.trans literal_initials)
  have emitted : run.events =
      [⟨37, 1, .store writerReference PlainCallAdmission64.storeWord 11⟩,
       ⟨39, 0, .load readerReference PlainCallAdmission64.oldWord (.initial PlainCallAdmission64.target)⟩] := by
    have observed := literal_scan
    rw [captured.scanned] at observed
    exact Except.ok.inj observed
  have metadata :
      (AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run 37)
        AtomicEvents.orders).map (fun candidate => (candidate.sources, candidate.ranks)) =
        some ([none, none, some 0], [0, 41, 0]) := by
    change (AtomicTrace.Graph.build ⟨initials, run.events, writes 37 run.observations⟩
      AtomicEvents.orders).map (fun candidate => (candidate.sources, candidate.ranks)) = _
    rw [manifest, emitted, observations, literal_publications]
    decide +kernel
  rw [built, Option.map_some] at metadata
  have exactMetadata : (table.sources, table.ranks) =
      ([none, none, some 0], [0, 41, 0]) := Option.some.inj metadata
  have positioned :=
    Correspondence.positioned_events batch captured.valid captured.sequenced captured.scanned
  have literal : run.events.map (fun actual =>
      (actual.position, actual.toSource AtomicEvents.orders)) =
      [(37, (⟨some 1, PlainCallAdmission64.target, .store .release PlainCallAdmission64.storeWord⟩ :
        C23Atomic.Event OS.Atomics64.CellId64 Word)),
       (39, ⟨some 0, PlainCallAdmission64.target, .load .acquire PlainCallAdmission64.oldWord⟩)] := by
    rw [emitted]
    rfl
  have response : run.observations[1]? = some (.returned 1) := by
    rw [observations]
    exact store_response
  obtain ⟨store, member, thread, returned⟩ := batch.responded response
  exact ⟨run, initials, table, execution, built, batch, history,
    positioned.symm.trans literal, congrArg Prod.fst exactMetadata,
    congrArg Prod.snd exactMetadata, store, member, thread, returned⟩

end EDSL.Tests.PlainCallHistory64

#print axioms EDSL.Tests.PlainCallHistory64.independentClosedPreWith
#print axioms EDSL.Tests.PlainCallHistory64.finished
#print axioms EDSL.Tests.PlainCallHistory64.literal_runtime
#print axioms EDSL.Tests.PlainCallHistory64.actual_abi
#print axioms EDSL.Tests.PlainCallHistory64.literal_scan
#print axioms EDSL.Tests.PlainCallHistory64.independent_closed_history
#audit_edsl
