/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Batch
import EDSL.OS.TSO64.StoreHistory.Indexed
import EDSL.Audit

/-!
Full RAM-cell frames for arbitrary successful prefixes of a plain-method
cohort. The footprint contains every admitted target qword and the exact
address/width footprints of the actual initial pending entries. In particular,
the boundary is not Method.initialQueue: an initial At assertion may already
describe a suffix of that queue.

Every actual worker slot has one initial Invocation. Production progress and
access capture classify subsequent issues; production store-history provenance
classifies remaining entries as boundary entries or actual issues. Locked
dispatch is excluded by the checked current cutpoints. An issue, including
MOV-store and RET, retains the published world. Only an actual head drain
publishes, through its current ordinary or managed authority.

The conclusion equates complete Space.cells, including inaccessible contents,
mappedness and permissions. It makes no fairness, compiler, native-execution,
source-memory-model or body-interpreter claim. The production scalar RAM,
long-mode, CET-off, translation/alias and resource assumptions are inherited
unchanged from Invocation and the TSO64 operations.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods.Footprint
open OS OS.TSO64 OS.AddressSpace AtomicMethods

/-- Natural-address footprint retaining the actual ordinary/managed width. -/
def storeRegion (store : Store) : Region := ⟨store.address, store.width⟩

/-- Union over all actual initial slots, including slots that admit loads. -/
def targets {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (query : Word) : Prop :=
  ∃ tid, (qwordRegion (invocations tid).method.reference.cell.address).Contains query

/-- Only actual initial FIFO entries, with their complete retained payloads.
No earlier issue is invented for an incoming entry. -/
def boundary (initial : OS.TSO64.State) (query : Word) : Prop :=
  ∃ tid entry, StoreHistory.Queued initial tid entry ∧ (storeRegion entry.store).Contains query

def affected {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (query : Word) : Prop :=
  targets invocations query ∨ boundary initial query

/-- Ordinary checked publication frames complete cells at its exact width.
The machine-memory projection alone would lose inaccessible byte contents. -/
theorem ordinary_publication_cells {world : World} {actor : Nat}
    {ticket : Ownership.Ticket} {store : Store} {result : World × Option Ownership.Ticket}
    (success : Atomics64.mutate world (operation actor ticket store) = .ok result)
    (query : Word) (outside : ¬(storeRegion store).Contains query) :
    result.1.legacy.shared.resources.space.cells query =
      world.legacy.shared.resources.space.cells query := by
  obtain ⟨_, legacy, changed, same⟩ := Atomics64.mutate_ok _ _ _ success
  obtain ⟨_, shared, changedShared, legacyEq⟩ := Atomics.mutate_ok _ _ _ changed
  obtain ⟨_, resources, changedResources, sharedEq⟩ := Borrowing.mutate_ok _ _ _ changedShared
  cases store with
  | mk address value =>
    cases value with
    | dword value =>
      cases stored : Ownership.storeWord world.legacy.shared.resources actor ticket address value with
      | error fault =>
        simp [operation, Ownership.Mutation.run, stored, Except.map] at changedResources
      | ok output =>
        simp only [operation, Ownership.Mutation.run, stored, Except.map, Except.ok.injEq]
          at changedResources
        subst resources
        obtain ⟨_, space, _, _, written, outputEq⟩ := Ownership.storeWord_ok _ _ _ _ _ _ stored
        rw [same, legacyEq, sharedEq, outputEq]
        exact (AddressSpace.storeWord_sound _ _ _ _ written).2.2.2 query outside
    | qword value =>
      cases stored : Ownership.storeWord64 world.legacy.shared.resources actor ticket address value with
      | error fault =>
        simp [operation, Ownership.Mutation.run, stored, Except.map] at changedResources
      | ok output =>
        simp only [operation, Ownership.Mutation.run, stored, Except.map, Except.ok.injEq]
          at changedResources
        subst resources
        obtain ⟨_, space, _, _, written, outputEq⟩ := Ownership.storeWord64_ok _ _ _ _ _ _ stored
        rw [same, legacyEq, sharedEq, outputEq]
        exact (AddressSpace.storeQWord_sound _ _ _ _ written).2.2.2 query outside

/-- The real mixed-queue publication frames full cells. Managed publication
is bound to the original descriptor by its current authorization result. -/
theorem publication_cells {world : World} {resources : Resources} {entry : Pending}
    {result : World × Option Atomics64.StoreEvent64}
    (effect : Queue.Effect world resources entry result)
    (query : Word) (outside : ¬(storeRegion entry.store).Contains query) :
    result.1.legacy.shared.resources.space.cells query =
      world.legacy.shared.resources.space.cells query := by
  cases effect with
  | ordinary changed => exact ordinary_publication_cells changed query outside
  | @managed reference value _ output current changed =>
    obtain ⟨handle, cell, authorized, eventEq, _⟩ :=
      Atomics64.publishStore_guarded _ _ _ _ _ changed
    have descriptor := Except.ok.inj (authorized.symm.trans current.2)
    have cellEq : cell = reference.cell := congrArg Prod.snd descriptor
    have addressEq : output.2.address = reference.cell.address := by rw [eventEq, cellEq]
    apply Atomics64.publishStore_frame _ _ _ _ _ changed query
    simpa only [addressEq, Queue.Entry.store, storeRegion, StoreBuffer.Mixed.Store.width,
      qwordRegion] using outside

/-- The actual checked cutpoint supplies an ordinary dispatch. Only the body
access can have store intent; neither padding nor RET can issue an entry. -/
private theorem dispatch_at_issue {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} {af : Bool}
    {result : OS.TSO64.State × Observation} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (success : OS.TSO64.step state (.issue tid af) .sharedCell = .ok result) :
    ∃ instruction, OS.TSO64.decode (fetchCPU state worker) = .ok (.ordinary instruction) ∧
      (instruction = method.operation.instruction ∨
        storeIntent instruction (localCPU state worker) = none) := by
  cases point with
  | preamble offset padding =>
    obtain ⟨_running, pc, _registers, shape⟩ := located.location
    cases shape with
    | body node _ret _extent =>
      exact ⟨_, (current.decode_node live located.resources node pc).1, .inl rfl⟩
    | @pad _ padding _ node _tail =>
      refine ⟨_, (current.decode_node live located.resources node pc).1, .inr ?_⟩
      cases padding <;> rfl
  | ret offset reply =>
    obtain ⟨_running, pc, _registers, node, _extent⟩ := located.location
    exact ⟨_, (current.decode_node live located.resources node pc).1, .inr rfl⟩
  | done reply =>
    have returned := located.location.1
    simp [OS.TSO64.step, issue, live, returned] at success

private theorem issued_access {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} {action : Action}
    {result : OS.TSO64.State × Observation} {entry : Pending}
    (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker)
    (issued : StoreHistory.Issued state action result .sharedCell tid entry) :
    OwnAccess tid state action := by
  cases issued with
  | @ordinary af issuingWorker instruction _store _observation issuing success issuingLive
      fetched _effect intent _admission _committed =>
    have workerEq : issuingWorker = worker := Option.some.inj (issuingLive.symm.trans live)
    subst issuingWorker
    have ownSuccess : OS.TSO64.step state (.issue tid af) .sharedCell = .ok result := by
      rw [← issuing]
      exact success
    obtain ⟨plain, decoded, kind⟩ := dispatch_at_issue current live located ownSuccess
    have instructionEq : instruction = plain :=
      Decoded.ordinary.inj (Except.ok.inj (fetched.symm.trans decoded))
    rcases kind with expected | absent
    · have exactInstruction : instruction = method.operation.instruction := instructionEq.trans expected
      refine ⟨af, worker, method.operation.instruction, issuing, live, ?_, ?_⟩
      · simpa only [exactInstruction] using fetched
      · cases method.operation <;> exact True.intro
    · rw [instructionEq, absent] at intent
      cases intent

/-- Identify a real issued entry using the actual captured access and current
managed selection. Full reference, original source and nonzero counter survive. -/
private theorem access_issued_entry {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {action : Action} {result : OS.TSO64.State × Observation}
    {reply : method.operation.Reply} {entry : Pending}
    (valid : Atomics64.WellFormed state.world)
    (origin : AccessOrigin method tid state action result reply)
    (issued : StoreHistory.Issued state action result .sharedCell tid entry) :
    ∃ address source, method.operation = .store address source ∧
      entry = .managed method.reference (method.entry source) method.initialQueue.nextStore := by
  rcases method with ⟨bytes, operation, base, registers, entryFlags, resources, reference,
    returnAddress, initialQueue, size, codeNoWrap, originalRsp, returnCanonical, stackNoWrap⟩
  cases operation with
  | load address =>
    obtain ⟨_af, worker, _issuing, live, _actual, _observed, _resources, _registers,
      _counter, _operand, _selected, fetched, _effect, _value⟩ := origin.evidence
    cases issued with
    | @ordinary _af issuingWorker instruction _store _observation _issuing _success issuingLive
        issuingFetched _effect intent _admission _committed =>
      have workerEq : issuingWorker = worker := Option.some.inj (issuingLive.symm.trans live)
      subst issuingWorker
      have instructionEq : instruction = .loadMem64 .rax address :=
        Decoded.ordinary.inj (Except.ok.inj (issuingFetched.symm.trans fetched))
      subst instruction
      cases intent
  | store address source =>
    obtain ⟨_af, worker, _issuing, live, _actual, _observed, _resources, _registers,
      _counter, _operand, selected, fetched, _effect, originalSource, originalCounter, _queue⟩ :=
      origin.evidence
    cases issued with
    | @ordinary _af issuingWorker instruction _store _observation _issuing _success issuingLive
        issuingFetched _effect intent admission _committed =>
      have workerEq : issuingWorker = worker := Option.some.inj (issuingLive.symm.trans live)
      subst issuingWorker
      have instructionEq : instruction = .storeMem64 address source :=
        Decoded.ordinary.inj (Except.ok.inj (issuingFetched.symm.trans fetched))
      subst instruction
      have queued : QueueEffect state worker (.storeMem64 address source)
          ⟨worker.pending ++ [entry], worker.nextStore + 1⟩ .sharedCell := .enqueued intent admission
      have update := ManagedAccess.queue_storeMem64_identity valid selected queued
      have fifo := congrArg Queue.Cursor.pending update
      have exactEntry := (List.cons.inj (List.append_cancel_left fifo)).1
      rw [originalSource, originalCounter] at exactEntry
      exact ⟨address, source, rfl, exactEntry⟩

private theorem issued_at_cut {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} {action : Action}
    {result : OS.TSO64.State × Observation} {entry : Pending}
    (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker)
    (issued : StoreHistory.Issued state action result .sharedCell tid entry) :
    ∃ address source, method.operation = .store address source ∧
      entry = .managed method.reference (method.entry source) method.initialQueue.nextStore := by
  have access := issued_access current live located issued
  have actual : OS.TSO64.step state action .sharedCell = .ok result := by
    cases issued with
    | ordinary _issuing success => exact success
  obtain ⟨_next, _after, emitted, _live, _located, _progress, _replies, captured⟩ :=
    step_preserves current live located actual
  have present := captured.complete.mp access
  cases emitted with
  | none => simp only [Option.isSome_none, Bool.false_eq_true] at present
  | some reply =>
    exact access_issued_entry current.valid.1 (captured.sound reply rfl) issued

/-- Every actual issued entry belongs to an actual initial worker slot and is
that invocation's exact managed store. No completed-call or sequencing premise
is needed, and neither the counter nor the initial FIFO need be zero/empty. -/
theorem issued_entry {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {tid index : Nat} {entry : Pending}
    (issued : StoreHistory.IssuedAt .sharedCell tid entry index initial actions result) :
    ∃ slot : Fin initial.workers.length, slot.val = tid ∧
      ∃ address source, (invocations slot).method.operation = .store address source ∧
        entry = .managed (invocations slot).method.reference
          ((invocations slot).method.entry source) (invocations slot).initial.nextStore := by
  obtain ⟨before, _action, _first, prefixRun, _selected, _actual, origin⟩ := issued.prestate
  have issuingLive : ∃ worker, before.workers[tid]? = some worker := by
    cases origin with
    | ordinary _issuing _success live => exact ⟨_, live⟩
  obtain ⟨issuingWorker, live⟩ := issuingLive
  have bound := (List.getElem_of_getElem? live).1
  have length : before.workers.length = initial.workers.length :=
    ScheduleTrace.workers_length prefixRun
  let slot : Fin initial.workers.length := ⟨tid, by omega⟩
  let admitted := invocations slot
  obtain ⟨current, _point, worker, _emissions, workerLive, located, _remaining, _replies, _trace⟩ :=
    schedule_preserves admitted.current admitted.live admitted.entry prefixRun
  obtain ⟨address, source, operationEq, entryEq⟩ := issued_at_cut current workerLive located origin
  have counter : admitted.initial.nextStore = admitted.method.initialQueue.nextStore :=
    admitted.entry.queue.counter
  rw [← counter] at entryEq
  exact ⟨slot, rfl, address, source, operationEq, entryEq⟩

/-- An actual next drain has an exact incoming entry or an indexed real store
issue by its admitted slot. This retains ordinary width and complete managed
descriptors without demanding ordered/empty incoming FIFOs or final quiescence. -/
theorem drained_entry {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    {tid : Nat} {entry : Pending} {after : OS.TSO64.State}
    (drained : drain result.1 tid .sharedCell = .ok (after, .drained tid entry)) :
    StoreHistory.Queued initial tid entry ∨
      ∃ (slot : Fin initial.workers.length) (index : Nat)
        (address : Sequential.Address) (source : Register),
        slot.val = tid ∧ StoreHistory.IssuedAt .sharedCell tid entry index initial actions result ∧
        (invocations slot).method.operation = .store address source ∧
        entry = .managed (invocations slot).method.reference
          ((invocations slot).method.entry source) (invocations slot).initial.nextStore := by
  rcases StoreHistory.drain_after_schedule_origin success drained with incoming | issued
  · exact .inl incoming
  · obtain ⟨index, indexed⟩ := issued.indexed
    obtain ⟨slot, thread, address, source, operationEq, entryEq⟩ := issued_entry invocations indexed
    exact .inr ⟨slot, index, address, source, thread, indexed, operationEq, entryEq⟩

/-- Boundary-or-actual-issue provenance contains every byte of every current
entry in the stated footprint. Ordinary incoming entries retain their width. -/
theorem pending_footprint {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    {tid : Nat} {entry : Pending} (queued : StoreHistory.Queued result.1 tid entry)
    {query : Word} (inside : (storeRegion entry.store).Contains query) :
    affected invocations query := by
  rcases StoreHistory.schedule_pending_origin success queued with boundaryEntry | issued
  · exact .inr ⟨tid, entry, boundaryEntry, inside⟩
  · obtain ⟨index, indexed⟩ := issued.indexed
    obtain ⟨slot, _thread, _address, _source, _operation, entryEq⟩ := issued_entry invocations indexed
    refine .inl ⟨slot, ?_⟩
    simpa only [entryEq, Queue.Entry.store, storeRegion, StoreBuffer.Mixed.Store.width,
      qwordRegion] using inside

/-- Each actual next action after a real prior frames cells outside the fixed
initial footprint. All-worker admission rules out any unmatched locked issue. -/
private theorem step_cells_at_prefix {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {prior : List Action} {before : OS.TSO64.State} {observations : List Observation}
    (prefixRun : schedule initial prior .sharedCell = .ok (before, observations))
    {action : Action} {result : OS.TSO64.State × Observation}
    (success : OS.TSO64.step before action .sharedCell = .ok result)
    (query : Word) (outside : ¬affected invocations query) :
    result.1.world.legacy.shared.resources.space.cells query =
      before.world.legacy.shared.resources.space.cells query := by
  cases action with
  | issue tid af =>
    obtain ⟨issuingWorker, live, _running, _code, _caller, decoded, fetched, effect⟩ :=
      issue_effect (profile := .sharedCell) success
    have bound := (List.getElem_of_getElem? live).1
    have length : before.workers.length = initial.workers.length :=
      ScheduleTrace.workers_length prefixRun
    let slot : Fin initial.workers.length := ⟨tid, by omega⟩
    let admitted := invocations slot
    obtain ⟨current, _point, worker, _emissions, workerLive, located, _remaining, _replies, _trace⟩ :=
      schedule_preserves admitted.current admitted.live admitted.entry prefixRun
    have workerEq : issuingWorker = worker := Option.some.inj (live.symm.trans workerLive)
    subst issuingWorker
    obtain ⟨instruction, ordinaryFetched, _kind⟩ := dispatch_at_issue current workerLive located success
    have decodedEq : decoded = .ordinary instruction := Except.ok.inj (fetched.symm.trans ordinaryFetched)
    subst decoded
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _executed finish =>
      cases finish <;> rfl
  | drain tid =>
    obtain ⟨worker, head, tail, output, live, fifo, _gate, changed, resultEq⟩ :=
      drain_effect (profile := .sharedCell) success
    have queued : StoreHistory.Queued before tid head :=
      ⟨worker, live, by rw [fifo]; exact List.mem_cons_self⟩
    have outsideHead : ¬(storeRegion head.store).Contains query := by
      intro inside
      exact outside (pending_footprint invocations prefixRun queued inside)
    rw [resultEq]
    exact publication_cells changed query outsideHead

private theorem append_schedule {state : OS.TSO64.State} {prior suffix : List Action}
    {middle result : OS.TSO64.State × List Observation} {profile : Profile}
    (firstRun : schedule state prior profile = .ok middle)
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

private theorem cells_from_prefix {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (query : Word) (outside : ¬affected invocations query)
    {prior actions : List Action} {before : OS.TSO64.State} {observations : List Observation}
    {result : OS.TSO64.State × List Observation}
    (prefixRun : schedule initial prior .sharedCell = .ok (before, observations))
    (success : schedule before actions .sharedCell = .ok result) :
    result.1.world.legacy.shared.resources.space.cells query =
      before.world.legacy.shared.resources.space.cells query := by
  induction actions generalizing prior before observations result with
  | nil =>
    have same : (before, []) = result := Except.ok.inj success
    subst result
    rfl
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    have single : schedule before [action] .sharedCell = .ok (first.1, [first.2]) := by
      simp only [schedule, stepped, ok_bind, pure_ok]
    have headPrefix := append_schedule prefixRun single
    have tailFrame := ih headPrefix following
    have headFrame := step_cells_at_prefix invocations prefixRun stepped query outside
    rw [same]
    exact tailFrame.trans headFrame

/-- Full-cell/permission frame for every actual successful finite interleaving.
The only cohort premise is one raw initial Invocation per actual initial slot.
Future progress, issue classification and drain footprints are derived. -/
theorem cells_frame {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    (query : Word) (outside : ¬affected invocations query) :
    result.1.world.legacy.shared.resources.space.cells query =
      initial.world.legacy.shared.resources.space.cells query :=
  cells_from_prefix invocations query outside (prior := []) (observations := []) rfl success

/-- Actual empty initial FIFOs remove the incoming footprint; counters may
still be nonzero. No final quiescence or method completion is required. -/
theorem cells_frame_empty {initial : OS.TSO64.State}
    (invocations : (tid : Fin initial.workers.length) → Invocation initial tid.val)
    (empty : Quiescent initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule initial actions .sharedCell = .ok result)
    (query : Word) (outside : ¬targets invocations query) :
    result.1.world.legacy.shared.resources.space.cells query =
      initial.world.legacy.shared.resources.space.cells query := by
  apply cells_frame invocations success query
  rintro (target | incoming)
  · exact outside target
  · obtain ⟨_tid, _entry, ⟨worker, live, member⟩, _inside⟩ := incoming
    have none := empty worker (List.mem_of_getElem? live)
    rw [none] at member
    cases member

end EDSL.X86.VCGen.PlainMethods.Footprint

#audit_edsl
