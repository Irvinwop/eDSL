/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Outcome

namespace EDSL.OS.MutexTSO
open X86

/-- Number of FIFO insertions performed by one decoded instruction. -/
def instructionStores : Instruction → Nat
  | .storeEsiRdi | .storeEaxRsi => 1
  | _ => 0

private theorem pendingStore_some_count {context : Threads.Context} {instruction : Instruction}
    {store : StoreBuffer.Store} (selected : TSO.pendingStore context instruction = some store) :
    instructionStores instruction = 1 := by
  cases instruction <;> simp_all [TSO.pendingStore, instructionStores]

private theorem pendingStore_none_count {context : Threads.Context} {instruction : Instruction}
    (selected : TSO.pendingStore context instruction = none) : instructionStores instruction = 0 := by
  cases instruction <;> simp_all [TSO.pendingStore, instructionStores]

/-- Replacing one actual FIFO changes the total number of pending writes by
exactly its length difference, including when unrelated queues are nonempty. -/
theorem pendingCount_install {physical : Physical} {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) (memory : Memory)
    (context : Threads.Context) (returned : Bool) (buffer : StoreBuffer.Buffer) :
    pendingCount (TSO.install physical identifier memory context returned buffer) + before.buffer.length =
      pendingCount physical + buffer.length := by
  rcases physical with ⟨oldMemory, workers⟩
  change ((workers.set identifier ⟨context, returned, buffer⟩).flatMap
      (fun worker => worker.buffer)).length + before.buffer.length =
    (workers.flatMap (fun worker => worker.buffer)).length + buffer.length
  change workers[identifier]? = some before at live
  induction workers generalizing identifier with
  | nil => simp at live
  | cons head tail ih =>
    cases identifier with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at live
      subst head
      simp only [List.set, List.flatMap_cons, List.length_append]
      omega
    | succ identifier =>
      have rest := ih (identifier := identifier) live
      simp only [List.set, List.flatMap_cons, List.length_append]
      omega

/-- Actual retirement either appends one write or preserves the pending count.
Locked operations require an empty own FIFO and cannot discard queued writes. -/
theorem issue_pendingCount {physical after : Physical} {identifier : Nat}
    {event : Option AtomicEvent}
    (issued : TSO.issue physical identifier = .ok (after, .retired identifier event)) :
    ∃ before instruction, physical.workers[identifier]? = some before ∧
      decodeAt (TSO.sharedState physical before) = .ok instruction ∧
      pendingCount after = pendingCount physical + instructionStores instruction := by
  obtain ⟨before, instruction, live, _, decoded, _, effect⟩ := TSO.issue_effect _ _ _ issued
  refine ⟨before, instruction, live, decoded, ?_⟩
  cases effect with
  | @queued store output selected _ _ _ _ _ =>
    have count := pendingCount_install live physical.memory (Threads.Context.ofState output) false
      (StoreBuffer.enqueue before.buffer store)
    have storeCount := pendingStore_some_count selected
    have length : (StoreBuffer.enqueue before.buffer store).length = before.buffer.length + 1 := by
      simp only [StoreBuffer.enqueue, List.length_append, List.length_singleton]
    rw [length] at count
    omega
  | @ordinary output selected _ _ _ _ =>
    have count := pendingCount_install live physical.memory (Threads.Context.ofState output) false before.buffer
    have storeCount := pendingStore_none_count selected
    omega
  | @returned output selected _ _ _ _ =>
    have count := pendingCount_install live physical.memory (Threads.Context.ofState output) true before.buffer
    have storeCount := pendingStore_none_count selected
    omega
  | @atomic event output selected _ empty _ _ _ _ _ =>
    have count := pendingCount_install live output.memory (Threads.Context.ofState output) false []
    have storeCount := pendingStore_none_count selected
    rw [empty] at count
    simp only [List.length_nil, Nat.add_zero] at count
    omega

private theorem Rel.decode_eq {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) {identifier : Nat} {before : TSO.Worker}
    {worker : MutexReplay.Worker} {instruction expected : Instruction}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (physicalDecoded : decodeAt (TSO.sharedState physical before) = .ok instruction)
    (logicalDecoded : decodeAt (worker.context.snapshot logical.shared.shared.resources.space) =
      .ok expected) : instruction = expected := by
  have contexts := (related.match_workers physicalLive logicalLive).1
  have same := decodeAt_fetch_congr (TSO.sharedState physical before)
    (worker.context.snapshot logical.shared.shared.resources.space)
    (congrArg Threads.Context.rip contexts) (fun address => (related.fetch address).symm)
  exact Except.ok.inj (physicalDecoded.symm.trans (same.trans logicalDecoded))

/-- The credit increment is determined by the instruction actually fetched
from shared code, using the checked protocol execution only for its semantics. -/
theorem dispatch_instructionStores {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) {identifier : Nat} {before : TSO.Worker}
    {worker : MutexReplay.Worker} {instruction : Instruction} {logicalAfter : Logical}
    {event : Option AtomicEvent}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (decoded : decodeAt (TSO.sharedState physical before) = .ok instruction)
    (checked : MutexReplay.dispatch logical identifier = .ok (logicalAfter, event)) :
    MutexReplay.stores worker = instructionStores instruction := by
  obtain ⟨selected, output, live, advanced, _⟩ := MutexReplay.dispatch_ok _ _ _ checked
  have equal := Option.some.inj (live.symm.trans logicalLive)
  subst selected
  obtain ⟨_, operation, action, performed, _⟩ := MutexReplay.advance_ok _ _ _ _ advanced
  cases MutexReplay.perform_effect _ _ _ _ _ performed with
  | plain plain context ran =>
    obtain ⟨_, fetched, _, _⟩ := MutexReplay.runNext_ok _ _ _ _ ran
    rw [related.decode_eq physicalLive logicalLive decoded fetched]
    have count := MutexReplay.action_nonstore worker _ action (by intro lease; simp)
    cases plain <;> simpa [instructionStores, MutexReplay.Plain.instruction] using count
  | acquire record attempt context _ _ _ _ ran =>
    obtain ⟨_, fetched, _, _⟩ := MutexReplay.runAtomic_ok _ _ _ _ ran
    rw [related.decode_eq physicalLive logicalLive decoded fetched]
    exact MutexReplay.action_nonstore worker _ action (by intro lease; simp)
  | load guard record value context _ _ _ ran =>
    obtain ⟨_, fetched, _, _⟩ := MutexReplay.runNext_ok _ _ _ _ ran
    rw [related.decode_eq physicalLive logicalLive decoded fetched]
    exact MutexReplay.action_nonstore worker _ action (by intro lease; simp)
  | store guard record after context _ _ _ ran =>
    obtain ⟨_, fetched, _, _⟩ := MutexReplay.runNext_ok _ _ _ _ ran
    rw [related.decode_eq physicalLive logicalLive decoded fetched]
    have phases := (MutexReplay.action_store worker guard action).1
    simp [MutexReplay.stores, instructionStores, phases]
  | release guard record released context _ _ _ _ ran =>
    obtain ⟨_, fetched, _, _⟩ := MutexReplay.runAtomic_ok _ _ _ _ ran
    rw [related.decode_eq physicalLive logicalLive decoded fetched]
    exact MutexReplay.action_nonstore worker _ action (by intro lease; simp)
  | ret context ran =>
    obtain ⟨_, fetched, _, _⟩ := MutexReplay.runReturn_ok _ _ _ ran
    rw [related.decode_eq physicalLive logicalLive decoded fetched]
    exact MutexReplay.action_nonstore worker _ action (by intro lease; simp)

/-- Retirement creates the same number of checked store credits and physical
FIFO entries. The actual event and the full logical endpoint are retained. -/
theorem retired_conservation {config : Mutex.Config} {physical after : Physical}
    {logical logicalAfter : Logical} (related : Rel config physical logical)
    {identifier : Nat} {event : Option AtomicEvent}
    (issued : TSO.issue physical identifier = .ok (after, .retired identifier event))
    (checked : MutexReplay.dispatch logical identifier = .ok (logicalAfter, event)) :
    MutexReplay.credits logicalAfter + pendingCount physical =
      MutexReplay.credits logical + pendingCount after := by
  obtain ⟨before, instruction, live, decoded, queued⟩ := issue_pendingCount issued
  obtain ⟨worker, found, _, _⟩ := related.physical_live live
  have stores := dispatch_instructionStores related live found decoded checked
  have credits := MutexReplay.dispatch_credits logical identifier worker
    (logicalAfter, event) found checked
  dsimp only at credits
  omega

/-- A single observed action accounts for every queue entry. Publication
removes one entry; a blocked issue changes neither credits nor the queue. -/
theorem step_conservation {config : Mutex.Config} {physical after : Physical}
    {logical logicalAfter : Logical} (related : Rel config physical logical)
    {action : TSO.Action} {observation : TSO.Observation}
    (success : TSO.step physical action = .ok (after, observation))
    (lifted : Lift logical action observation logicalAfter) :
    MutexReplay.credits logicalAfter + pendingCount physical =
      MutexReplay.credits logical + pendingCount after + drainCount [observation] := by
  cases lifted with
  | retired checked =>
    have count := retired_conservation related success checked
    simpa only [drainCount, List.filter_cons, List.filter_nil, Bool.false_eq_true,
      ↓reduceIte, List.length_nil, Nat.add_zero] using count
  | blocked identifier =>
    obtain ⟨_, _, _, _, _, _, _, same, _⟩ := TSO.issue_blocked_effect success
    simp only [same, drainCount, List.filter_cons, List.filter_nil, Bool.false_eq_true,
      ↓reduceIte, List.length_nil, Nat.add_zero]
  | drained identifier store =>
    have count := related.drain_pending_length success
    change pendingCount after + 1 = pendingCount physical at count
    simp only [drainCount, List.filter_cons, List.filter_nil, ↓reduceIte,
      List.length_cons, List.length_nil]
    omega

/-- Prefix conservation follows the actual physical trace. The returned
logical trace contains exactly its real retirements and atomic events. -/
theorem trace_conservation {config : Mutex.Config} {physical after : Physical}
    {logical : Logical} (related : Rel config physical logical)
    (closed : MutexReplay.ClosedUnderTwo config)
    {actions : List TSO.Action} {observations : List TSO.Observation}
    (trace : TSO.Trace physical actions observations after) :
    ∃ finalState, LiftTrace logical actions observations finalState ∧
      Rel config after finalState ∧
      MutexReplay.credits finalState + pendingCount physical =
        MutexReplay.credits logical + pendingCount after + drainCount observations := by
  induction trace generalizing logical with
  | nil => exact ⟨logical, .nil, related, by simp [drainCount]⟩
  | @cons before middle after action observation actions observations first tail ih =>
    obtain ⟨next, lifted, nextRel⟩ := step_lifts related closed first
    obtain ⟨finalState, following, finalRel, finalCount⟩ := ih nextRel
    have firstCount := step_conservation related first lifted
    have drains := drainCount_append [observation] observations
    simp only [List.singleton_append] at drains
    exact ⟨finalState, .cons lifted following, finalRel, by omega⟩

/-- Issued-store credits are partitioned into stores still pending and stores
actually drained. Successful canonical replay is derived from the physical
schedule rather than required as an admission premise. -/
theorem schedule_conservation {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {actions : List TSO.Action} {result : Physical × List TSO.Observation}
    (success : TSO.schedule physical actions = .ok result) :
    ∃ finalState,
      MutexReplay.schedule logical (retiredSelections result.2) =
        .ok (finalState, TSO.atomicEvents result.2) ∧
      Rel config result.1 finalState ∧
      MutexReplay.credits finalState + pendingCount physical =
        MutexReplay.credits logical + pendingCount result.1 + drainCount result.2 := by
  obtain ⟨finalState, lifted, finalRel, count⟩ :=
    trace_conservation related closed (TSO.schedule_trace _ _ _ success)
  exact ⟨finalState, lifted.replay, finalRel, count⟩

@[simp] theorem pendingCount_initial (state : MachineThreads.State) :
    pendingCount (TSO.initial state) = 0 := by
  have empty : TSO.Quiescent (TSO.initial state) := by
    intro worker member
    obtain ⟨before, _, rfl⟩ := List.mem_map.mp member
    rfl
  simp only [pendingCount, pending_nil empty, List.length_nil]

/-- For an arbitrary admitted paused prefix, completion publishes every
remaining payload write. Existing issued-store credits and queued writes are
both counted, so a partially completed cohort needs no fresh-entry premise. -/
theorem returned_drains {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {actions : List TSO.Action} {result : Physical × List TSO.Observation}
    (success : TSO.schedule physical actions = .ok result)
    (returned : TSO.Returned result.1) :
    drainCount result.2 + MutexReplay.credits logical =
      2 * logical.workers.length + pendingCount physical := by
  obtain ⟨finalState, replayed, finalRel, count⟩ :=
    schedule_conservation related closed success
  have empty := finalRel.returned_quiescent returned
  have finalCredit := MutexReplay.completed_credits finalState
    (finalRel.invariant.completed (finalRel.returned_finished returned))
  have length := (MutexReplay.schedule_trace _ _ _ replayed).length
  dsimp only at length
  have finalPending : pendingCount result.1 = 0 := by
    simp only [pendingCount, pending_nil empty, List.length_nil]
  rw [finalPending, finalCredit] at count
  omega

/-- This routine performs exactly two protected stores per worker. Actual
completion therefore entails precisely two physical drains per worker. -/
theorem completed_drains {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {actions : List TSO.Action}
    {result : Physical × List TSO.Observation}
    (success : TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result)
    (returned : TSO.Returned result.1) :
    drainCount result.2 = 2 * state.workers.length := by
  have count := returned_drains
    (Rel.initial admitted.invariant admitted.ready admitted.profile) admitted.closed success
    returned
  simpa only [MutexReplay.entry_credits state admitted.entry, pendingCount_initial,
    Nat.add_zero] using count

/-- Model actions count retired instructions, real FIFO drains and blocked
issues separately. They do not measure hardware time or micro-operations. -/
theorem completed_action_count {config : Mutex.Config} {state : Logical} {initial : BitVec 32}
    (admitted : Admission config state initial) {actions : List TSO.Action}
    {result : Physical × List TSO.Observation}
    (success : TSO.schedule (TSO.initial (MutexReplay.erase state)) actions = .ok result)
    (returned : TSO.Returned result.1) :
    actions.length = 15 * state.workers.length +
      4 * MutexReplay.busyCount (TSO.atomicEvents result.2) + blockedCount result.2 := by
  have actions := schedule_action_count _ _ _ success
  have retired := (completed_observations admitted success returned).retired
  have drains := completed_drains admitted success returned
  omega

end EDSL.OS.MutexTSO

#audit_edsl
