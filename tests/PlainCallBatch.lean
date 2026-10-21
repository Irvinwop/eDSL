/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Batch
import tests.PlainCallInterference

namespace EDSL.Tests.PlainCallBatch
open X86 OS.TSO64 X86.VCGen.PlainMethods

/-!
One invocation per worker in the scheduler's fixed two-slot universe. The
initial state follows the reader's actual ordinary store, before the peer's
managed store. Both slots have present admission derived from checked setup
and attachment, not from a desired final world or a future cutpoint.

The peer accesses first even though it occupies slot 1. Its publication and
both RETs are real scheduler actions. The reader retains the old full qword
across publication and returns with its own ordinary FIFO still outstanding.
The extracted calls must retain access positions 0/1 and RET positions 3/4.
No graph, RF, ranks, C23 legality, History, native or compiler claim is made.
The imported sharedCell, scalar RAM, long-mode, CET-off, translation/alias and
managed-resource assumptions remain in force.
-/

private instance : DecidableEq PlainMethods.PendingView := inferInstance
private instance : DecidableEq (List PlainMethods.PendingView) := inferInstance
private instance : DecidableEq (List PlainMethods.PendingView × Nat) := inferInstance
private instance : DecidableEq (Option (List PlainMethods.PendingView × Nat)) := inferInstance
private instance : DecidableEq (List (Except Error Word)) := inferInstance
private instance : DecidableEq (List (Option (Nat × Word))) := inferInstance
private instance : DecidableEq (List (Word × Nat)) := inferInstance

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private def found {α : Type} (value : Option α) (present : value.isSome = true) : α :=
  value.get present

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (found value present) := by
  cases value with
  | none => cases present
  | some value => rfl

def initial : OS.TSO64.State := PlainCallInterference.ownQueued.1

theorem initial_length : initial.workers.length = 2 := by decide +kernel

-- Reconstruct present authority, then transport it FORWARD through the actual
-- ordinary issue. PlainCallInterference.present is at a later boundary and is not used
-- to assume Current at this invocation boundary.
private theorem reader_initial_current : Current PlainCallInterference.method PlainCallInterference.initial := by
  refine ⟨PlainCallInterference.initial_valid, ?_, ?_, ?_, ?_⟩
  · apply checkCode_sound
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem reader_current : Current PlainCallInterference.method initial :=
  reader_initial_current.step PlainCallInterference.own_issued

-- The cell is shared, but the peer's authorized handle belongs to actor 12.
def peerReference : Queue.ManagedRef :=
  ⟨PlainCallInterference.ready.atomicB, ⟨12, PlainMethodAdmission.reference.handle.cell⟩,
    PlainMethodAdmission.reference.cell⟩

def peerMethod : Method where
  bytes := [0x48, 0x89, 0x37, 0xc3]
  operation := .store (.base .rdi) .rsi
  base := 393223
  entry := PlainCallInterference.peerContext.registers
  entryFlags := PlainCallInterference.peerContext.flags
  resources := PlainCallInterference.peer.resources
  reference := peerReference
  returnAddress := 0x8000
  initialQueue := ⟨PlainCallInterference.peer.pending, PlainCallInterference.peer.nextStore⟩
  size := by decide +kernel
  codeNoWrap := by decide +kernel
  originalRsp := by decide +kernel
  returnCanonical := by decide +kernel
  stackNoWrap := by decide +kernel

private theorem peer_initial_current : Current peerMethod PlainCallInterference.initial := by
  refine ⟨PlainCallInterference.initial_valid, ?_, ?_, ?_, ?_⟩
  · apply checkCode_sound
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem peer_current : Current peerMethod initial :=
  peer_initial_current.step PlainCallInterference.own_issued

private theorem peer_live_after {state : OS.TSO64.State} {result : OS.TSO64.State × Observation}
    {tid issuing : Nat} {af : Bool} {worker : Worker}
    (success : step state (.issue issuing af) .sharedCell = .ok result)
    (different : tid ≠ issuing) (live : state.workers[tid]? = some worker) :
    result.1.workers[tid]? = some worker := (step_peer success different).trans live

theorem peer_live : initial.workers[1]? = some PlainCallInterference.peer := by
  dsimp only [initial]
  exact peer_live_after (state := PlainCallInterference.initial)
    (result := PlainCallInterference.ownQueued) (tid := 1) (issuing := 0) (af := false)
    (worker := PlainCallInterference.peer) PlainCallInterference.own_issued (by decide) rfl

private theorem peer_context : PlainCallInterference.peer.context = PlainCallInterference.peerContext :=
  (makeWorker_valid_for .sharedCell PlainCallInterference.peer_made).2.2.2

theorem peer_entry : At peerMethod (.preamble 0 []) PlainCallInterference.peer := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [peerMethod]
  · dsimp only [peerMethod]
    exact congrArg Context.flags peer_context
  · dsimp only [Method.queueAt, peerMethod]
    exact QueueFrame.refl _
  · refine ⟨(makeWorker_valid_for .sharedCell PlainCallInterference.peer_made).2.1, ?_, ?_, ?_⟩
    · dsimp only [peerMethod]
      rw [peer_context]
      rfl
    · dsimp only [peerMethod]
      exact congrArg Context.registers peer_context
    · exact (check_sound (bytes := peerMethod.bytes) (operation := peerMethod.operation)
        (padding := []) (by decide +kernel)).2

theorem reader_live : initial.workers[0]? = some PlainCallInterference.boundaryReader := by
  dsimp only [initial]
  exact PlainCallInterference.queued_reader_live

def readerInvocation : Invocation initial 0 where
  method := PlainCallInterference.method
  padding := []
  occurrence := 17
  initial := PlainCallInterference.boundaryReader
  current := reader_current
  live := reader_live
  entry := PlainCallInterference.entry

def peerInvocation : Invocation initial 1 where
  method := peerMethod
  padding := []
  occurrence := 17
  initial := PlainCallInterference.peer
  current := peer_current
  live := peer_live
  entry := peer_entry

/-- All actual initial slots are admitted. Equal logical occurrences in the
two slots are intentional; neither label is a nextStore counter. -/
def invocations (tid : Fin initial.workers.length) : Invocation initial tid.val := by
  by_cases zero : tid.val = 0
  · rw [zero]
    exact readerInvocation
  · have bound : tid.val < 2 := by simpa only [initial_length] using tid.isLt
    have one : tid.val = 1 := by omega
    rw [one]
    exact peerInvocation

theorem store_actual : step initial (.issue 1 true) .sharedCell = .ok PlainCallInterference.peerQueued :=
  PlainCallInterference.peer_issued

-- Reuse the actual store/load/publication prefix. Only the following three
-- production steps are new; checked extraction never accepts a supplied state.
def peerReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step (PlainCallInterference.peerPublished false).1 (.issue 1 false) .sharedCell

theorem peer_return_succeeds : peerReturnAttempt.toOption.isSome = true := by decide +kernel

def peerReturned : OS.TSO64.State × Observation := checked peerReturnAttempt peer_return_succeeds

theorem peer_returned_actual :
    step (PlainCallInterference.peerPublished false).1 (.issue 1 false) .sharedCell = .ok peerReturned :=
  checked_ok peerReturnAttempt peer_return_succeeds

def readerReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step peerReturned.1 (.issue 0 true) .sharedCell

theorem reader_return_succeeds : readerReturnAttempt.toOption.isSome = true := by decide +kernel

def readerReturned : OS.TSO64.State × Observation := checked readerReturnAttempt reader_return_succeeds

theorem reader_returned_actual : step peerReturned.1 (.issue 0 true) .sharedCell = .ok readerReturned :=
  checked_ok readerReturnAttempt reader_return_succeeds

def closeAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step readerReturned.1 (.drain 0) .sharedCell

theorem close_succeeds : closeAttempt.toOption.isSome = true := by decide +kernel

def closed : OS.TSO64.State × Observation := checked closeAttempt close_succeeds

theorem closed_actual : step readerReturned.1 (.drain 0) .sharedCell = .ok closed :=
  checked_ok closeAttempt close_succeeds

def actions : List Action :=
  [.issue 1 true, .issue 0 false, .drain 1, .issue 1 false, .issue 0 true, .drain 0]

def result : OS.TSO64.State × List Observation :=
  (closed.1, [PlainCallInterference.peerQueued.2, (PlainCallInterference.loaded false).2,
    (PlainCallInterference.peerPublished false).2, peerReturned.2, readerReturned.2, closed.2])

theorem scheduled : schedule initial actions .sharedCell = .ok result := by
  have loadStep := PlainCallInterference.loaded_actual false
  dsimp only [PlainCallInterference.boundary] at loadStep
  simp only [actions, result, schedule, store_actual, loadStep,
    PlainCallInterference.peer_published_actual, peer_returned_actual, reader_returned_actual,
    closed_actual, ok_bind, pure_ok]

theorem final_reader_present : (result.1.workers[0]?).isSome = true := by decide +kernel
theorem final_peer_present : (result.1.workers[1]?).isSome = true := by decide +kernel

def finalReader : Worker := found (result.1.workers[0]?) final_reader_present
def finalPeer : Worker := found (result.1.workers[1]?) final_peer_present

theorem final_reader_live : result.1.workers[0]? = some finalReader := found_ok _ final_reader_present
theorem final_peer_live : result.1.workers[1]? = some finalPeer := found_ok _ final_peer_present
theorem final_reader_returned : finalReader.phase = .returned := by decide +kernel
theorem final_peer_returned : finalPeer.phase = .returned := by decide +kernel

theorem all_returned (tid : Fin initial.workers.length) :
    ∃ final, result.1.workers[tid.val]? = some final ∧ final.phase = .returned := by
  have bound : tid.val < 2 := by simpa only [initial_length] using tid.isLt
  have slots : tid.val = 0 ∨ tid.val = 1 := by omega
  rcases slots with zero | one
  · rw [zero]
    exact ⟨finalReader, final_reader_live, final_reader_returned⟩
  · rw [one]
    exact ⟨finalPeer, final_peer_live, final_peer_returned⟩

/-- A closed, nonempty two-worker use of the adapter, with no additional
admission, success, final At, legality or verifier-success hypotheses. -/
theorem admitted_batch : Nonempty (BatchResult initial actions result invocations) :=
  completed_batch invocations scheduled all_returned

private theorem body_node {bytes : List Byte} {operation : Operation}
    (shape : Shape bytes operation 0 []) :
    X86.VCGen.AtomicMethods.Node bytes 0 (.ordinary operation.instruction) := by
  cases shape with
  | body access _ _ => exact access

/-- The production decoder recognizes the peer's actual store at action 0.
This witness supplies no typed reply or proposed access annotation. -/
theorem store_dispatched : DispatchedAt 1 initial actions result 0 := by
  refine ⟨initial, .issue 1 true, PlainCallInterference.peerQueued, rfl, rfl, store_actual, ?_⟩
  refine ⟨true, PlainCallInterference.peer, peerMethod.operation.instruction, rfl, peer_live, ?_,
    True.intro⟩
  exact (peer_current.decode_node peer_live peer_entry.resources
    (body_node peer_entry.location.2.2.2) peer_entry.location.2.1).1

/-- The reader dispatch is at original action 1, after the real peer issue.
Its checked current/entry facts are at that actual prefix boundary. -/
theorem reader_dispatched : DispatchedAt 0 initial actions result 1 := by
  refine ⟨PlainCallInterference.boundary, .issue 0 false, PlainCallInterference.loaded false, ?_, rfl,
    PlainCallInterference.loaded_actual false, ?_⟩
  · change schedule initial [.issue 1 true] .sharedCell =
      .ok (PlainCallInterference.boundary, [PlainCallInterference.peerQueued.2])
    simp only [schedule, store_actual, ok_bind, pure_ok, PlainCallInterference.boundary]
  · refine ⟨false, PlainCallInterference.boundaryReader, PlainCallInterference.method.operation.instruction,
      rfl, PlainCallInterference.live, ?_, True.intro⟩
    exact (PlainCallInterference.present.decode_node PlainCallInterference.live PlainCallInterference.entry.resources
      (body_node PlainCallInterference.entry.location.2.2.2) PlainCallInterference.entry.location.2.1).1

theorem peer_response : result.2[3]? = some (.returned 1) := by decide +kernel
theorem reader_response : result.2[4]? = some (.returned 0) := by decide +kernel

/-- Exercise access and response coverage together: each actual dispatch and
its independently observed RET name the SAME unique extracted thread. -/
theorem covered_calls (batch : BatchResult initial actions result invocations) :
    ∃ store ∈ batch.calls, ∃ reader ∈ batch.calls,
      (store.thread, store.performed, store.returned) = (1, 0, 3) ∧
      (reader.thread, reader.performed, reader.returned) = (0, 1, 4) := by
  obtain ⟨store, storeMem, storeThread, storePosition⟩ := batch.dispatched store_dispatched
  obtain ⟨storeRet, storeRetMem, storeRetThread, storeRetPosition⟩ := batch.responded peer_response
  have sameStore : store = storeRet :=
    batch.thread_unique storeMem storeRetMem (storeThread.trans storeRetThread.symm)
  have storeReturned : store.returned = 3 := by rw [sameStore]; exact storeRetPosition
  obtain ⟨reader, readerMem, readerThread, readerPosition⟩ := batch.dispatched reader_dispatched
  obtain ⟨readerRet, readerRetMem, readerRetThread, readerRetPosition⟩ := batch.responded reader_response
  have sameReader : reader = readerRet :=
    batch.thread_unique readerMem readerRetMem (readerThread.trans readerRetThread.symm)
  have readerReturned : reader.returned = 4 := by rw [sameReader]; exact readerRetPosition
  refine ⟨store, storeMem, reader, readerMem, ?_, ?_⟩
  · simp only [storeThread, storePosition, storeReturned]
  · simp only [readerThread, readerPosition, readerReturned]

-- A two-element list is fixed by independent membership and strict order.
-- This lemma neither invokes nor reproduces the adapter's sorting algorithm.
private theorem two_in_order {α : Type} {relation : α → α → Prop}
    (items : List α) (first second : α) (size : items.length = 2)
    (firstMem : first ∈ items) (secondMem : second ∈ items) (different : first ≠ second)
    (ordered : items.Pairwise relation) (noReverse : ¬ relation second first) :
    items = [first, second] := by
  cases items with
  | nil => simp at size
  | cons head tail =>
    cases tail with
    | nil => simp at size
    | cons next rest =>
      have empty : rest = [] := by
        cases rest with
        | nil => rfl
        | cons extra tail => simp only [List.length_cons] at size; omega
      subst rest
      simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMem secondMem
      rcases firstMem with rfl | rfl
      · rcases secondMem with rfl | rfl
        · exact False.elim (different rfl)
        · rfl
      · rcases secondMem with rfl | rfl
        · exact False.elim (noReverse ((List.pairwise_cons.mp ordered).1 _ (by simp)))
        · exact False.elim (different rfl)

/-- Every extraction has chronological thread order [1,0] and retains drains
in its original RET indices. Sorting by thread/slot, dropping a call, or
compressing indices cannot satisfy these independently fixed observations. -/
theorem chronological_calls (batch : BatchResult initial actions result invocations) :
    batch.calls.map (fun actual => (actual.thread, actual.performed, actual.returned)) =
      [(1, 0, 3), (0, 1, 4)] := by
  obtain ⟨store, storeMem, reader, readerMem, storePosition, readerPosition⟩ := covered_calls batch
  have storeThread : store.thread = 1 := congrArg Prod.fst storePosition
  have readerThread : reader.thread = 0 := congrArg Prod.fst readerPosition
  have storePerformed : store.performed = 0 :=
    congrArg (fun triple : Nat × Nat × Nat => triple.2.1) storePosition
  have readerPerformed : reader.performed = 1 :=
    congrArg (fun triple : Nat × Nat × Nat => triple.2.1) readerPosition
  have different : store ≠ reader := by
    intro same
    have threads := congrArg Concurrency.AtomicCalls.Call.thread same
    rw [storeThread, readerThread] at threads
    cases threads
  have noReverse : ¬ reader.performed < store.performed := by
    rw [readerPerformed, storePerformed]
    exact Nat.not_lt_zero _
  have exactCalls := two_in_order batch.calls store reader (batch.length.trans initial_length)
    storeMem readerMem different batch.ordered noReverse
  rw [exactCalls]
  simp only [List.map_cons, List.map_nil, storePosition, readerPosition]

def readerSlot : Fin initial.workers.length := ⟨0, by rw [initial_length]; decide⟩
def peerSlot : Fin initial.workers.length := ⟨1, by rw [initial_length]; decide⟩

/-- Uniqueness concerns every actual independently recognized dispatch and
every observed RET, not merely membership of two selected annotation values. -/
theorem selected_unique (batch : BatchResult initial actions result invocations) :
    (∀ index, DispatchedAt 1 initial actions result index → index = 0) ∧
    (∀ index, DispatchedAt 0 initial actions result index → index = 1) ∧
    (∀ index, result.2[index]? = some (.returned 1) → index = 3) ∧
    (∀ index, result.2[index]? = some (.returned 0) → index = 4) := by
  have peerPerformed := (batch.completed peerSlot).performed_unique store_dispatched
  have readerPerformed := (batch.completed readerSlot).performed_unique reader_dispatched
  have peerReturnedAt := (batch.completed peerSlot).responseUnique 3 peer_response
  have readerReturnedAt := (batch.completed readerSlot).responseUnique 4 reader_response
  exact ⟨fun _ actual => ((batch.completed peerSlot).performed_unique actual).trans peerPerformed.symm,
    fun _ actual => ((batch.completed readerSlot).performed_unique actual).trans readerPerformed.symm,
    fun _ actual => ((batch.completed peerSlot).responseUnique _ actual).trans peerReturnedAt.symm,
    fun _ actual => ((batch.completed readerSlot).responseUnique _ actual).trans readerReturnedAt.symm⟩

/-- Actual executable observations, with independently literal words/counters.
The managed cell changes to the peer's word, while the reader returns the old
64-bit word and finally publishes its outstanding ordinary payload 9. -/
theorem literal_runtime :
    initial.workers[0]?.map (fun worker =>
      (worker.pending.map PlainMethods.pendingView, worker.nextStore)) =
      some ([(0, 131072, .qword 9, none)], 1) ∧
    result.2.map PlainMethods.eventKind = [(0, 1), (0, 0), (2, 1), (1, 1), (1, 0), (2, 0)] ∧
    [OS.TSO64.Return.returnValue peerReturned, OS.TSO64.Return.returnValue readerReturned] =
      [some (1, 5), some (0, 0x1122334455667788)] ∧
    readerReturned.1.workers[0]?.map (fun worker =>
      (worker.pending.map PlainMethods.pendingView, worker.nextStore)) =
      some ([(0, 131072, .qword 9, none)], 1) ∧
    PlainMethods.worldWords result.1 =
      [.ok 9, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000] ∧
    result.1.workers.map (fun worker => (worker.context.registers .rax, worker.nextStore)) =
      [(0x1122334455667788, 1), (5, 1)] ∧
    result.1.workers.map (fun worker => worker.pending.isEmpty) = [true, true] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Closed existence plus exact extraction; no chosen expected call list is
supplied to completed_batch or used as an execution input. -/
theorem admitted_chronological_batch :
    ∃ batch : BatchResult initial actions result invocations,
      batch.calls.map (fun actual => (actual.thread, actual.performed, actual.returned)) =
        [(1, 0, 3), (0, 1, 4)] := by
  obtain ⟨batch⟩ := admitted_batch
  exact ⟨batch, chronological_calls batch⟩

end EDSL.Tests.PlainCallBatch

#print axioms EDSL.Tests.PlainCallBatch.reader_current
#print axioms EDSL.Tests.PlainCallBatch.peer_current
#print axioms EDSL.Tests.PlainCallBatch.peer_entry
#print axioms EDSL.Tests.PlainCallBatch.admitted_batch
#print axioms EDSL.Tests.PlainCallBatch.chronological_calls
#print axioms EDSL.Tests.PlainCallBatch.selected_unique
#print axioms EDSL.Tests.PlainCallBatch.literal_runtime
#print axioms EDSL.Tests.PlainCallBatch.admitted_chronological_batch
#audit_edsl
