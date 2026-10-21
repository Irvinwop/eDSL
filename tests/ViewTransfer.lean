/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64CrossCellFixtures
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ViewTransfer
import EDSL.OS.TSO64.ExecutionViews.Query
import EDSL.Audit

/-!
Actual scanner clients for view transfer through a precise B writer, with A in
a separately allocated cell. Publication to another worker and own forwarding
use the same theorem. The reader's A view may select its own pending writer;
the transferred rank is not an assertion that its A load returns seven.

All annotations follow execution. Literal source identities, publication ranks,
peer accesses and prefix queues/RAM are independent expected results. Initial B
and the writer's B both contain seven: the early read must retain initial source
identity, and cannot be treated as reading that later publication.

These are finite sharedCell scalar-RAM, long-mode/CET-off model clients with
checked complete resources. They establish no source memory order, source-C23
legality, fairness, physical execution, native refinement or corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.Tests.ViewTransfer
open X86 OS.TSO64 OS.TSO64.PublishedHistory OS.TSO64.C23Projection.AtomicTrace

inductive Scenario where
  | pending | published | early | forwarded
  deriving DecidableEq

/-- Common bytes: MOV [RDI],RSI; MOV RAX,[RDX]; MOV [RDX],RSI;
MOV RAX,[RDI]; RET. Forwarding exchanges the middle load and store.
Both programs have instruction offsets 0, 3, 6, 9, 12. -/
def initialAttempt (scenario : Scenario) : Except Fault OS.TSO64.State :=
  TSO64CrossCellFixtures.start
    (if scenario = .forwarded then 0x8b48328948378948 else 0x8948028b48378948)
    (if scenario = .forwarded then 0x000000c3078b4802 else 0x000000c3078b4832)
    3 7 7 11 0 (match scenario with | .pending => 0 | .forwarded => 12 | _ => 3)

def actions : Scenario → List Action
  | .pending =>
    [.issue 0 false, .issue 0 true, .issue 0 false, .issue 1 true,
      .drain 0, .drain 0, .issue 1 false, .issue 1 true,
      .issue 0 false, .issue 0 true, .issue 1 false, .issue 1 true, .drain 1, .drain 1]
  | .published =>
    [.issue 0 false, .issue 0 true, .issue 0 false, .drain 0, .drain 0,
      .issue 1 false, .issue 1 true, .issue 0 false, .issue 0 true,
      .issue 1 false, .issue 1 true, .drain 1]
  | .early =>
    [.issue 0 false, .issue 0 true, .issue 0 false, .issue 1 false,
      .issue 1 true, .issue 1 false, .issue 1 true, .issue 0 false,
      .issue 0 true, .drain 0, .drain 0, .drain 1]
  | .forwarded =>
    [.issue 0 false, .issue 0 true, .issue 1 false, .issue 0 false,
      .issue 0 true, .issue 0 false, .drain 0, .drain 0]

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

theorem initial_succeeds (scenario : Scenario) :
    (initialAttempt scenario).toOption.isSome = true := by cases scenario <;> decide +kernel

@[irreducible] def initial (scenario : Scenario) : OS.TSO64.State :=
  checked (initialAttempt scenario) (initial_succeeds scenario)

theorem initial_actual (scenario : Scenario) : initialAttempt scenario = .ok (initial scenario) := by
  unfold initial
  exact checked_ok _ _

theorem initial_valid (scenario : Scenario) : WellFormed (initial scenario) .sharedCell :=
  TSO64CrossCellFixtures.start_valid (initial_actual scenario)

def scanAttempt (scenario : Scenario) : Except Fault Result :=
  scan (initial scenario) (actions scenario) .sharedCell 101 empty

theorem scan_succeeds (scenario : Scenario) :
    (scanAttempt scenario).toOption.isSome = true := by cases scenario <;> decide +kernel

@[irreducible] def scanned (scenario : Scenario) : Result :=
  checked (scanAttempt scenario) (scan_succeeds scenario)

theorem scanned_actual (scenario : Scenario) :
    scan (initial scenario) (actions scenario) .sharedCell 101 empty = .ok (scanned scenario) := by
  unfold scanned
  exact checked_ok _ _

@[irreducible] def result (scenario : Scenario) : OS.TSO64.State × List Observation :=
  (scanned scenario).execution

theorem scheduled (scenario : Scenario) :
    schedule (initial scenario) (actions scenario) .sharedCell = .ok (result scenario) := by
  unfold result
  exact scan_scheduled (scanned_actual scenario)

private theorem quiescent_of_queues {state : OS.TSO64.State}
    (queues : state.workers.map Worker.pending = [[], []]) : Quiescent state := by
  intro worker member
  have mapped : worker.pending ∈ state.workers.map Worker.pending :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  rw [queues] at mapped
  simpa using mapped

theorem initial_quiescent (scenario : Scenario) : Quiescent (initial scenario) := by
  apply quiescent_of_queues
  cases scenario <;> decide +kernel

theorem initial_sequenced (scenario : Scenario) : Sequenced (initial scenario) := by
  intro worker member
  simp [Worker.storeCursor, Queue.Cursor.Ordered, initial_quiescent scenario worker member]

theorem final_quiescent (scenario : Scenario) : Quiescent (result scenario).1 := by
  apply quiescent_of_queues
  cases scenario <;> decide +kernel

theorem execution (scenario : Scenario) :
    ExecutionViews.Execution (initial scenario) (actions scenario) (result scenario) .sharedCell :=
  ⟨scheduled scenario, initial_valid scenario, initial_sequenced scenario, final_quiescent scenario⟩

theorem access_certificate (scenario : Scenario) :
    Certificate (initial scenario) (actions scenario) .sharedCell 101 empty (scanned scenario) :=
  scan_certificate (initial_valid scenario) (initial_sequenced scenario) (scanned_actual scenario)

private theorem prefix_succeeds (scenario : Scenario) (cut : Nat) :
    (schedule (initial scenario) ((actions scenario).take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut (scheduled scenario) cut
  rw [success]
  rfl

@[irreducible] def atCut (scenario : Scenario) (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule (initial scenario) ((actions scenario).take cut) .sharedCell)
    (prefix_succeeds scenario cut)

theorem prefix_exact (scenario : Scenario) (cut : Nat) :
    schedule (initial scenario) ((actions scenario).take cut) .sharedCell =
      .ok ((atCut scenario cut).1, (result scenario).2.take cut) := by
  have actual : schedule (initial scenario) ((actions scenario).take cut) .sharedCell =
      .ok (atCut scenario cut) := by unfold atCut; exact checked_ok _ _
  have same := (ScheduleTrace.suffix (scheduled scenario) actual).1
  rw [← same]
  exact actual

/-- Complete independent descriptors, including actor, allocation and epoch.
Their authority below comes from actual store/load admissions. -/
def ownA : Queue.ManagedRef := ⟨⟨0⟩, ⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩
def peerA : Queue.ManagedRef := ⟨⟨1⟩, ⟨12, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩
def ownB : Queue.ManagedRef := ⟨⟨2⟩, ⟨11, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩
def peerB : Queue.ManagedRef := ⟨⟨3⟩, ⟨12, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩

theorem literal_accesses (scenario : Scenario) : (scanned scenario).events =
    match scenario with
    | .pending =>
      [⟨101, 0, .store ownA 7 0⟩, ⟨102, 0, .load ownB 7 (.initial ⟨1⟩)⟩,
        ⟨103, 0, .store ownB 7 1⟩, ⟨104, 1, .store peerA 11 0⟩,
        ⟨107, 1, .load peerB 7 (.store 0 1)⟩, ⟨108, 1, .store peerB 11 1⟩,
        ⟨109, 0, .load ownA 7 (.store 0 0)⟩, ⟨111, 1, .load peerA 11 (.store 1 0)⟩]
    | .published =>
      [⟨101, 0, .store ownA 7 0⟩, ⟨102, 0, .load ownB 7 (.initial ⟨1⟩)⟩,
        ⟨103, 0, .store ownB 7 1⟩, ⟨106, 1, .load peerB 7 (.store 0 1)⟩,
        ⟨107, 1, .store peerB 11 0⟩, ⟨108, 0, .load ownA 7 (.store 0 0)⟩,
        ⟨110, 1, .load peerA 7 (.store 0 0)⟩]
    | .early =>
      [⟨101, 0, .store ownA 7 0⟩, ⟨102, 0, .load ownB 7 (.initial ⟨1⟩)⟩,
        ⟨103, 0, .store ownB 7 1⟩, ⟨104, 1, .load peerB 7 (.initial ⟨1⟩)⟩,
        ⟨105, 1, .store peerB 11 0⟩, ⟨106, 1, .load peerA 3 (.initial ⟨0⟩)⟩,
        ⟨108, 0, .load ownA 7 (.store 0 0)⟩]
    | .forwarded =>
      [⟨101, 0, .store ownA 7 0⟩, ⟨102, 0, .store ownB 7 1⟩,
        ⟨104, 0, .load ownB 7 (.store 0 1)⟩, ⟨105, 0, .load ownA 7 (.store 0 0)⟩] := by
  cases scenario <;> decide +kernel

theorem literal_observations (scenario : Scenario) : (result scenario).2 =
    match scenario with
    | .pending =>
      [.ordinary 0, .ordinary 0, .ordinary 0, .ordinary 1,
        .drained 0 (.managed ownA 7 0), .drained 0 (.managed ownB 7 1),
        .ordinary 1, .ordinary 1, .ordinary 0, .returned 0, .ordinary 1, .returned 1,
        .drained 1 (.managed peerA 11 0), .drained 1 (.managed peerB 11 1)]
    | .published =>
      [.ordinary 0, .ordinary 0, .ordinary 0, .drained 0 (.managed ownA 7 0),
        .drained 0 (.managed ownB 7 1), .ordinary 1, .ordinary 1, .ordinary 0,
        .returned 0, .ordinary 1, .returned 1, .drained 1 (.managed peerB 11 0)]
    | .early =>
      [.ordinary 0, .ordinary 0, .ordinary 0, .ordinary 1, .ordinary 1,
        .ordinary 1, .returned 1, .ordinary 0, .returned 0,
        .drained 0 (.managed ownA 7 0), .drained 0 (.managed ownB 7 1),
        .drained 1 (.managed peerB 11 0)]
    | .forwarded =>
      [.ordinary 0, .ordinary 0, .returned 1, .ordinary 0, .ordinary 0,
        .returned 0, .drained 0 (.managed ownA 7 0), .drained 0 (.managed ownB 7 1)] := by
  cases scenario <;> decide +kernel

def writeIndex : Scenario → Nat | .forwarded => 1 | _ => 2
def loadIndex : Scenario → Nat | .pending => 6 | .published => 5 | _ => 3
def drainIndex : Scenario → Nat | .pending => 5 | .published => 4 | .early => 10 | .forwarded => 7
def reader : Scenario → Nat | .forwarded => 0 | _ => 1
def readTarget (scenario : Scenario) : Queue.ManagedRef :=
  if scenario = .forwarded then ownB else peerB
def readSource : Scenario → WriterId
  | .early => .initial ⟨1⟩ | _ => .store 0 1
def sourceEvent (scenario : Scenario) : Event :=
  ⟨101 + loadIndex scenario, reader scenario, .load (readTarget scenario) 7 (readSource scenario)⟩
def BStamp (scenario : Scenario) : Stamp :=
  ⟨101 + drainIndex scenario, .buffered 0 ownB 7 1⟩

private theorem authenticated {scenario : Scenario} {event : Event} {index : Nat}
    (member : event ∈ (scanned scenario).events) (position : event.position = 101 + index) :
    EventAt .sharedCell event index (initial scenario) (actions scenario) (result scenario) 101 empty := by
  obtain ⟨actualIndex, actual⟩ := scan_sound (initial_valid scenario)
    (initial_sequenced scenario) (scanned_actual scenario) member
  have actualPosition := actual.position
  have same : actualIndex = index := by omega
  subst actualIndex
  simpa only [result] using actual

theorem A_at (scenario : Scenario) : EventAt .sharedCell ⟨101, 0, .store ownA 7 0⟩
    0 (initial scenario) (actions scenario) (result scenario) 101 empty := by
  apply authenticated
  · cases scenario <;> rw [literal_accesses] <;> simp
  · rfl

theorem B_at (scenario : Scenario) :
    EventAt .sharedCell ⟨101 + writeIndex scenario, 0, .store ownB 7 1⟩
      (writeIndex scenario) (initial scenario) (actions scenario) (result scenario) 101 empty := by
  apply authenticated
  · cases scenario <;> rw [literal_accesses] <;> simp [writeIndex]
  · rfl

theorem read_at (scenario : Scenario) : EventAt .sharedCell (sourceEvent scenario)
    (loadIndex scenario) (initial scenario) (actions scenario) (result scenario) 101 empty := by
  apply authenticated
  · cases scenario <;> rw [literal_accesses] <;>
      simp [sourceEvent, loadIndex, reader, readTarget, readSource]
  · rfl

theorem B_issued (scenario : Scenario) : StoreHistory.IssuedAt .sharedCell 0 (.managed ownB 7 1)
    (writeIndex scenario) (initial scenario) (actions scenario) (result scenario) :=
  (B_at scenario).store_issued

theorem B_written (scenario : Scenario) : Nonempty (InstructionWriteAt (initial scenario)
    (actions scenario) (result scenario) .sharedCell 101 (writeIndex scenario) (BStamp scenario)) := by
  have observed : (result scenario).2[drainIndex scenario]? = some (.drained 0 (.managed ownB 7 1)) := by
    cases scenario <;> rw [literal_observations] <;> rfl
  obtain ⟨publication, _index⟩ := managed_drain_writeAt (offset := 101) (scheduled scenario) observed
  exact ⟨InstructionWriteAt.buffered (B_issued scenario) publication⟩

/-- Literal expected ranks, never inputs to setup, execution or scanning. -/
def writerARank : Scenario → Nat
  | .pending => 106 | .published => 105 | .early => 111 | .forwarded => 108
def readerARank : Scenario → Nat
  | .pending => 114 | .published => 105 | .early => 0 | .forwarded => 108
def sourceRank : Scenario → Nat
  | .pending => 107 | .published => 106 | .early => 0 | .forwarded => 109
def queried (scenario : Scenario) (cut tid : Nat) (target : Queue.ManagedRef) : Option Nat :=
  ExecutionViews.query (atCut scenario cut).1 (result scenario).2 cut tid target 101 empty

theorem literal_view_queries (scenario : Scenario) :
    queried scenario (writeIndex scenario + 1) 0 ownA = some (writerARank scenario) ∧
    queried scenario (loadIndex scenario) (reader scenario) ownA = some (readerARank scenario) ∧
    queried scenario (loadIndex scenario) (reader scenario) (readTarget scenario) =
      some (sourceRank scenario) := by cases scenario <;> decide +kernel

/-- Every client retains the actual source instruction, actual scanned read,
and actual query-derived views. The same full A target is current through the
writer's original resources, even when inspecting the peer's ghost view. -/
structure Witnesses (scenario : Scenario) : Prop where
  written : Nonempty (InstructionWriteAt (initial scenario) (actions scenario) (result scenario)
    .sharedCell 101 (writeIndex scenario) (BStamp scenario))
  access : EventAt .sharedCell (sourceEvent scenario) (loadIndex scenario)
    (initial scenario) (actions scenario) (result scenario) 101 empty
  earlier : Nonempty (ExecutionViews.At (initial scenario) (actions scenario) (result scenario)
    .sharedCell (writeIndex scenario + 1) 0 ownA 101 empty (writerARank scenario))
  later : Nonempty (ExecutionViews.At (initial scenario) (actions scenario) (result scenario)
    .sharedCell (loadIndex scenario) (reader scenario) ownA 101 empty (readerARank scenario))
  sourceView : Nonempty (ExecutionViews.At (initial scenario) (actions scenario) (result scenario)
    .sharedCell (loadIndex scenario) (reader scenario) (readTarget scenario) 101 empty (sourceRank scenario))

theorem witnesses (scenario : Scenario) : Witnesses scenario := by
  obtain ⟨own, target, ownLive, currentA, relatedA⟩ := (A_at scenario).initial_authority
  have targetEq : target = ownA := relatedA.2
  subst target
  have actual := read_at scenario
  obtain ⟨peer, selected, peerLive, currentB, relatedB⟩ := actual.initial_authority
  have selectedEq : selected = readTarget scenario := relatedB.2
  subst selected
  have answers := literal_view_queries scenario
  exact ⟨B_written scenario, actual,
    ExecutionViews.query_sound (execution scenario) ownLive
      (prefix_exact scenario (writeIndex scenario + 1)) currentA answers.1,
    ExecutionViews.query_sound (execution scenario) peerLive
      (prefix_exact scenario (loadIndex scenario)) currentA answers.2.1,
    ExecutionViews.query_sound (execution scenario) peerLive
      (prefix_exact scenario (loadIndex scenario)) currentB answers.2.2⟩

private theorem transfer (scenario : Scenario) (positive : scenario ≠ .early) :
    Witnesses scenario ∧ writerARank scenario ≤ readerARank scenario := by
  have actual := witnesses scenario
  obtain ⟨written⟩ := actual.written
  obtain ⟨earlier⟩ := actual.earlier
  obtain ⟨later⟩ := actual.later
  have sameSource : readSource scenario = Graph.publicationKey (BStamp scenario) := by
    cases scenario with
    | early => exact False.elim (positive rfl)
    | pending | published | forwarded => rfl
  exact ⟨actual, actual.access.transfers_view (execution scenario) rfl written sameSource earlier later⟩

/-- B is published, but the peer's A view selects its own queued eleven,
published only at action twelve. No caller supplies the transferred ordering. -/
theorem published_with_own_pending : Witnesses .pending ∧ 106 ≤ 114 :=
  transfer .pending (by decide)

/-- With no own A writer, the peer's A view is the already published writer. -/
theorem published_without_own_pending : Witnesses .published ∧ 105 ≤ 105 :=
  transfer .published (by decide)

/-- Both A and B remain queued when own B forwards. The intervening peer RET
neither publishes the source nor changes the retained A view. -/
theorem own_forwarding_before_publication : Witnesses .forwarded ∧ 108 ≤ 108 :=
  transfer .forwarded (by decide)

/-- Seven is read from initial B before either writer publication. Actual A
views would violate transfer from this B writer; its source key is different. -/
theorem early_equal_payload_is_initial : Witnesses .early ∧
    readSource .early ≠ Graph.publicationKey (BStamp .early) ∧ ¬ 111 ≤ 0 :=
  ⟨witnesses .early, by decide, by decide⟩

/-- The automatic-domain API constructs its own views. Independent prefix
queries fix their exact ranks, without supplying them to that API. -/
theorem access_authenticated_transfer :
    Nonempty (ExecutionViews.At (initial .pending) (actions .pending) (result .pending)
      .sharedCell 3 0 ownA 101 empty 106) ∧
    Nonempty (ExecutionViews.At (initial .pending) (actions .pending) (result .pending)
      .sharedCell 6 1 ownA 101 empty 114) ∧ 106 ≤ 114 := by
  have known := witnesses .pending
  obtain ⟨written⟩ := known.written
  obtain ⟨target, firstRank, lastRank, related, ⟨before⟩, ⟨after⟩, ordered⟩ :=
    known.access.transfers_access_views (execution .pending) rfl written rfl (A_at .pending) rfl
  have targetEq : target = ownA := related.2
  subst target
  obtain ⟨expectedBefore⟩ := known.earlier
  obtain ⟨expectedAfter⟩ := known.later
  have firstEq := before.unique expectedBefore
  have lastEq := after.unique expectedAfter
  subst firstRank
  subst lastRank
  exact ⟨⟨before⟩, ⟨after⟩, ordered⟩

/-- A peer's distinct A handle has actual admission authority. Its separately
queried pending view participates in the same source-driven transfer. -/
theorem current_alias_transfer :
    ownA.identifier ≠ peerA.identifier ∧
    Nonempty (ExecutionViews.At (initial .pending) (actions .pending) (result .pending)
      .sharedCell 6 1 peerA 101 empty 114) ∧ 106 ≤ 114 := by
  have peerStore : EventAt .sharedCell ⟨104, 1, .store peerA 11 0⟩ 3
      (initial .pending) (actions .pending) (result .pending) 101 empty := by
    apply authenticated
    · rw [literal_accesses]; simp
    · rfl
  obtain ⟨writer, writerTarget, _writerLive, writerCurrent, writerRelated⟩ :=
    (A_at .pending).initial_authority
  have writerTargetEq : writerTarget = ownA := writerRelated.2
  subst writerTarget
  obtain ⟨peer, readerTarget, peerLive, peerCurrent, peerRelated⟩ := peerStore.initial_authority
  have readerTargetEq : readerTarget = peerA := peerRelated.2
  subst readerTarget
  have answered : queried .pending 6 1 peerA = some 114 := by decide +kernel
  obtain ⟨aliasView⟩ := ExecutionViews.query_sound (execution .pending) peerLive
    (prefix_exact .pending 6) peerCurrent answered
  have known := witnesses .pending
  obtain ⟨written⟩ := known.written
  obtain ⟨before⟩ := known.earlier
  have bound := known.access.transfers_view_alias (execution .pending) rfl written rfl
    before aliasView writerCurrent peerCurrent (by rfl)
  exact ⟨by decide, ⟨aliasView⟩, bound⟩

private instance : DecidableEq (Word × Word) := inferInstance
private instance : DecidableEq (List Pending × Word × Word) := inferInstance

/-- Inspect real prefix execution, including RAM independently of annotations. -/
def visibility (scenario : Scenario) (cut tid : Nat) : Option (List Pending × Word × Word) := do
  let before ← (schedule (initial scenario) ((actions scenario).take cut) .sharedCell).toOption
  let worker ← before.1.workers[tid]?
  let a ← (loadQWord (published before.1.world) 65536).toOption
  let b ← (loadQWord (published before.1.world) 458752).toOption
  return (worker.pending, a, b)

theorem prefix_queue_and_RAM_contract :
    visibility .pending 3 0 = some ([.managed ownA 7 0, .managed ownB 7 1], 3, 7) ∧
    visibility .pending 6 1 = some ([.managed peerA 11 0], 7, 7) ∧
    visibility .published 5 1 = some ([], 7, 7) ∧
    visibility .early 3 1 = some ([], 3, 7) ∧
    visibility .early 6 1 = some ([.managed peerB 11 0], 3, 7) ∧
    visibility .forwarded 5 0 = some ([.managed ownA 7 0, .managed ownB 7 1], 3, 7) := by
  decide +kernel

/-- Real loads and peer actions determine returned registers and final RAM;
returning does not substitute for the separate queue-emptiness certificate. -/
theorem final_machine_contract (scenario : Scenario) :
    (result scenario).1.workers.map (fun worker => worker.context.registers .rax) =
      (match scenario with
        | .pending => [7, 11] | .published => [7, 7] | .early => [7, 3] | .forwarded => [7, 5]) ∧
    (result scenario).1.workers.map Worker.phase = [.returned, .returned] ∧
    (result scenario).1.workers.map Worker.nextStore =
      (match scenario with | .pending => [2, 2] | .forwarded => [2, 0] | _ => [2, 1]) ∧
    (loadQWord (published (result scenario).1.world) 65536).toOption =
      some (if scenario = .pending then 11 else 7) ∧
    (loadQWord (published (result scenario).1.world) 458752).toOption =
      some (if scenario = .forwarded then 7 else 11) := by cases scenario <;> decide +kernel

end EDSL.Tests.ViewTransfer

#print axioms EDSL.Tests.ViewTransfer.execution
#print axioms EDSL.Tests.ViewTransfer.access_certificate
#print axioms EDSL.Tests.ViewTransfer.B_issued
#print axioms EDSL.Tests.ViewTransfer.B_written
#print axioms EDSL.Tests.ViewTransfer.witnesses
#print axioms EDSL.Tests.ViewTransfer.published_with_own_pending
#print axioms EDSL.Tests.ViewTransfer.published_without_own_pending
#print axioms EDSL.Tests.ViewTransfer.own_forwarding_before_publication
#print axioms EDSL.Tests.ViewTransfer.early_equal_payload_is_initial
#print axioms EDSL.Tests.ViewTransfer.access_authenticated_transfer
#print axioms EDSL.Tests.ViewTransfer.current_alias_transfer
#print axioms EDSL.Tests.ViewTransfer.prefix_queue_and_RAM_contract
#print axioms EDSL.Tests.ViewTransfer.final_machine_contract
#audit_edsl
