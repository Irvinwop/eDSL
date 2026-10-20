/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Domain
import EDSL.OS.AtomicSetThreads64.Trace

set_option warningAsError true

namespace EDSL.OS.AtomicSetThreads64.Programs
open X86 AddressSpace

/-- The supplied syntax determines the mathematical request list through the
external tag adapter. Every occurrence remains, including unchanged updates
and cancelling XORs. This definition does not evaluate any machine operation. -/
def expectedRequests (operations : List Sequential.LogicalOp) (mask : Word) :
    List (Logical64.Operation × Word) :=
  operations.map (fun operation => (Atomics64.operationOfLogicalOp operation, mask))

@[simp] theorem expectedRequests_length (operations : List Sequential.LogicalOp) (mask : Word) :
    (expectedRequests operations mask).length = operations.length := List.length_map _

/-- Completed captured events determine the original body's requests, rather
than a task guessed from the final word. The length follows from the actual
terminal cursor and the checked event-prefix invariant. -/
theorem completed_requests {shared : Atomics64.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (completed : worker.phase = .completed) :
    worker.events.map Atomics64.Event.orderedRequest =
      expectedRequests worker.operations (worker.entry.registers .rsi) := by
  have shape := valid.phase.shape
  rw [completed] at shape
  have length : worker.events.length = worker.operations.length :=
    valid.phase.counted.symm.trans shape.1
  apply List.ext_getElem (by simp only [List.length_map, expectedRequests, length])
  intro index left right
  have inside : index < worker.events.length := by simpa only [List.length_map] using left
  have captured := valid.captured index worker.events[index] (List.getElem?_eq_getElem inside)
  have tag : worker.operations[index] = worker.events[index].logical.op :=
    (List.getElem?_eq_some_iff.mp captured.1).2
  simp only [List.getElem_map, expectedRequests, Atomics64.Event.orderedRequest]
  rw [tag, captured.2.2.2.2.2]

private theorem own_workerEvents (identifier : Nat) (observations : List Observation)
    (selected : ∀ observation ∈ observations, observation.1.1 = identifier)
    (actors : ∀ selection event, (selection, some event) ∈ observations →
      event.actor = principal selection.1) :
    workerEvents identifier (observations.map Prod.snd) = events observations := by
  induction observations with
  | nil => rfl
  | cons observation observations induction =>
    obtain ⟨selection, label⟩ := observation
    have rest := induction (fun observation member =>
      selected observation (List.mem_cons_of_mem _ member))
      (fun selection event member => actors selection event (List.mem_cons_of_mem _ member))
    cases label with
    | none =>
      change workerEvents identifier (observations.map Prod.snd) = events observations
      exact rest
    | some event =>
      have actor : event.actor = principal identifier :=
        (actors selection event (by simp)).trans
          (congrArg principal (selected (selection, some event) (by simp)))
      simpa [workerEvents, emittedFor, events, actor] using congrArg (List.cons event) rest

/-- For an actual own-only schedule, all emitted events belong to that worker.
Together with the managed prefix theorem this identifies the entire completed
event list, without dropping any no-change or cancelled occurrence. -/
theorem ownSelections_events (state : State) (identifier : Nat) (afs : List Bool)
    (result : State × List Observation) (previous current : Worker)
    (valid : WellFormed state) (live : state.workers identifier = some previous)
    (empty : previous.events = [])
    (success : schedule state (ownSelections identifier afs) = .ok result)
    (survives : result.1.workers identifier = some current) :
    previous.origin = current.origin ∧ current.events = events result.2 := by
  have trace := schedule_instructions _ _ _ success
  have selected : ∀ observation ∈ result.2, observation.1.1 = identifier := by
    intro observation member
    have present : observation.1 ∈ ownSelections identifier afs := by
      rw [← schedule_selections _ _ _ success]
      exact List.mem_map.mpr ⟨observation, member, rfl⟩
    obtain ⟨af, _, same⟩ := List.mem_map.mp present
    exact (congrArg Prod.fst same).symm
  have actors : ∀ selection event, (selection, some event) ∈ result.2 →
      event.actor = principal selection.1 := by
    intro selection event member
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, actor, _⟩ := trace.event_bound valid selection event member
    exact actor
  obtain ⟨origin, exactEvents⟩ := trace.worker_events valid identifier previous current live survives
  exact ⟨origin, by rw [exactEvents, empty, List.nil_append,
    own_workerEvents identifier result.2 selected actors]⟩

/-- A successful prefix followed by the actual final RET. Its CPU successor
uses the entire current shared RAM and its original caller-slot footprint. -/
def ActualReturn (state : State) (identifier : Nat) (afs : List Bool)
    (result : State × List Observation) : Prop :=
    ∃ priorAFs af before observations worker,
      afs = priorAFs ++ [af] ∧
      schedule state (ownSelections identifier priorAFs) = .ok (before, observations) ∧
      result.2 = observations ++ [((identifier, af), none)] ∧
      WellFormed before ∧ before.workers identifier = some worker ∧
      WorkerValid before.shared identifier worker ∧ worker.phase = .running ∧
      worker.cursor = worker.operations.length ∧
      dispatch before identifier af = .ok (result.1, none) ∧
      LockedSet64.decodeAt (worker.context.snapshot before.shared.legacy.shared.resources.space) = .ok .ret ∧
      LockedSet64.step af (worker.context.snapshot before.shared.legacy.shared.resources.space) =
        .ok ⟨.returned ((returned worker.context worker.returnAddress).snapshot
          before.shared.legacy.shared.resources.space), [.stack8 (worker.entry.registers .rsp)]⟩ ∧
      result.1.shared = before.shared

theorem ownSelections_return (state : State) (identifier : Nat) (afs : List Bool)
    (result : State × List Observation) (current : Worker)
    (valid : WellFormed state) (positive : 0 < afs.length)
    (success : schedule state (ownSelections identifier afs) = .ok result)
    (live : result.1.workers identifier = some current) (completed : current.phase = .completed) :
    ActualReturn state identifier afs result := by
  have nonempty : afs ≠ [] := by intro empty; simp [empty] at positive
  obtain ⟨priorAFs, split⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast nonempty)
  have planned : ownSelections identifier afs =
      ownSelections identifier priorAFs ++ [(identifier, afs.getLast nonempty)] := by
    simpa only [ownSelections, List.map_append, List.map_cons, List.map_nil] using
      congrArg (ownSelections identifier) split
  obtain ⟨prior, tail, scheduled, suffix, same⟩ := schedule_append_ok _ _ _ _ (planned ▸ success)
  obtain ⟨last, rest, dispatched, done, tailSame⟩ := schedule_cons_ok _ _ _ _ suffix
  obtain ⟨lastState, lastLabel⟩ := last
  simp only [schedule, Except.ok.injEq] at done
  have finalState : result.1 = lastState := by rw [same, tailSame, ← done]
  have beforeValid := schedule_wellFormed _ _ _ valid scheduled
  have lastLive : lastState.workers identifier = some current := by rw [← finalState]; exact live
  have label : lastLabel = none := by
    cases emitted : lastLabel with
    | none => rfl
    | some event =>
      have hasEvent : dispatch prior.1 identifier (afs.getLast nonempty) = .ok (lastState, some event) := by
        simpa only [emitted] using dispatched
      obtain ⟨_, actual, _, _, found, _, _, _, _, _, _, _, _, _, _, _, _, _, _, running⟩ :=
        dispatch_atomic_spec _ _ _ _ _ beforeValid hasEvent
      have equal := Option.some.inj (found.symm.trans lastLive)
      subst actual
      rw [completed] at running
      cases running
  have ret : dispatch prior.1 identifier (afs.getLast nonempty) = .ok (result.1, none) := by
    simpa only [label, ← finalState] using dispatched
  obtain ⟨worker, workerAt, workerValid, running, terminal, decoded, _, _, machine, shared, _⟩ :=
    dispatch_return_origin _ _ _ _ beforeValid ret
  refine ⟨priorAFs, afs.getLast nonempty, prior.1, prior.2, worker, split, scheduled,
    ?_, beforeValid, workerAt, workerValid, running, terminal, ret, decoded, machine, shared⟩
  rw [same, tailSame, ← done, label]

private theorem spawned_allOn (operations : List Sequential.LogicalOp) (old mask : Word)
    (registers : Register → Word) (flags : Word) (result : State × Nat)
    (success : spawn (Domain.prepared (bodyBytes operations) old) 0
      (Domain.start (bodyBytes operations) mask registers flags) true = .ok result) :
    AllOn result.1 ⟨0⟩ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ :=
    spawn_ok _ _ _ _ _ success
  rw [same]
  intro identifier worker found
  change (if identifier = 0 then some _ else none) = some worker at found
  split at found
  · cases found
    rfl
  · cases found

/-- Checked setup, creation, every selected instruction, actual return and
collection for one worker. Readback is from the current full64 RAM after join.
The mathematical request list is fixed by the supplied body and mask, before
any execution witness is chosen. This is a finite abstract managed execution;
physical refinement, source memory order and compound-call linearizability are
separate properties. The 4096-byte capacity belongs only to this loader. -/
structure BodyExecution (operations : List Sequential.LogicalOp) (old mask : Word)
    (registers : Register → Word) (flags : Word) (afs : List Bool) where
  created : State × Nat
  initial : Worker
  scheduled : State × List Observation
  completed : Worker
  joined : State × Context
  final : Word
  setupSuccess : Domain.setup (bodyBytes operations) old =
    .ok (Domain.prepared (bodyBytes operations) old)
  ready : SpawnReady (Domain.prepared (bodyBytes operations) old)
    (Domain.start (bodyBytes operations) mask registers flags)
  spawnSuccess : spawn (Domain.prepared (bodyBytes operations) old) 0
    (Domain.start (bodyBytes operations) mask registers flags) true = .ok created
  identifier : created.2 = 0
  createdValid : WellFormed created.1
  initialAt : created.1.workers 0 = some initial
  initialOperations : initial.operations = operations
  initialEntry : initial.entry = Domain.entry mask registers flags
  initialEvents : initial.events = []
  initialRank : initial.rank = operations.length + 1
  createdResources : created.1.shared.legacy.shared.resources =
    (Domain.prepared (bodyBytes operations) old).shared.legacy.shared.resources
  initialRead : loadQWord (toMemory created.1.shared.legacy.shared.resources.space) 65536 = .ok old
  legal : Legal created.1 (ownSelections 0 afs)
  scheduleSuccess : schedule created.1 (ownSelections 0 afs) = .ok scheduled
  instructionTrace : InstructionTrace created.1 scheduled.2 scheduled.1
  selections : scheduled.2.map Prod.fst = ownSelections 0 afs
  afChoices : (scheduled.2.map Prod.fst).map Prod.snd = afs
  instructionCount : scheduled.2.length = operations.length + 1
  scheduledValid : WellFormed scheduled.1
  completedAt : scheduled.1.workers 0 = some completed
  completedPhase : completed.phase = .completed
  completedValid : WorkerValid scheduled.1.shared 0 completed
  completedOperations : completed.operations = operations
  completedEntry : completed.entry = Domain.entry mask registers flags
  actualEvents : completed.events = events scheduled.2
  eventCount : (events scheduled.2).length = operations.length
  requests : (events scheduled.2).map Atomics64.Event.orderedRequest = expectedRequests operations mask
  actualReturn : ActualReturn created.1 0 afs scheduled
  logicalTrace : Atomics64.LogicalTrace ⟨0⟩ ⟨0, ⟨0, 0⟩, 65536⟩
    created.1.shared (events scheduled.2) scheduled.1.shared
  joinSuccess : join scheduled.1 0 0 = .ok joined
  joinedValid : WellFormed joined.1
  returnedContext : joined.2 = completed.context
  workerGone : joined.1.workers 0 = none
  handleRevoked : Atomics64.HandleRevoked joined.1.shared completed.handle
  codeRevoked : Borrowing.Revoked joined.1.shared.legacy.shared completed.codeLoan
  stackRevoked : Borrowing.Revoked joined.1.shared.legacy.shared completed.stackLoan
  currentResources : joined.1.shared.legacy.shared.resources = scheduled.1.shared.legacy.shared.resources
  currentCells : joined.1.shared.cells = scheduled.1.shared.cells
  persistentCell : joined.1.shared.cells ⟨0⟩ = some ⟨0, ⟨0, 0⟩, 65536⟩
  beforeCollectionRead : loadQWord (toMemory scheduled.1.shared.legacy.shared.resources.space) 65536 = .ok final
  readback : loadQWord (toMemory joined.1.shared.legacy.shared.resources.space) 65536 = .ok final
  mathematicalResult : Logical64.OrderedMathematicalResult old (expectedRequests operations mask) final
  stackPointer : joined.2.registers .rsp = 32776
  returnAddress : joined.2.rip = 8192
  registersPreserved : ∀ register, register ≠ .rsp →
    joined.2.registers register = (Domain.entry mask registers flags).registers register
  flagsPreserved : joined.2.flags &&& ~~~arithmeticFlagMask = flags &&& ~~~arithmeticFlagMask
  managedHistory : History (Domain.prepared (bodyBytes operations) old)
    ([none] ++ scheduled.2.map Prod.snd ++ [none]) joined.1

/-- Every loader-supported finite body has an actual checked one-worker
execution for arbitrary full64 inputs, caller context and the entire supplied
AF list. Present resources construct spawn; Legal and remaining rank construct
the schedule and join. No future success or desired result is an input. -/
theorem arbitrary_body_execution (operations : List Sequential.LogicalOp)
    (bound : (bodyBytes operations).length ≤ 4096) (old mask : Word)
    (registers : Register → Word) (flags : Word) (afs : List Bool)
    (length : afs.length = operations.length + 1) :
    Nonempty (BodyExecution operations old mask registers flags afs) := by
  obtain ⟨created, setup, ready, spawned, createdValid, resources, initialRead⟩ :=
    Domain.arbitrary_body operations bound old mask registers flags
  obtain ⟨identifier, initial, initialAt, initialOperations, _, initialContext,
    _, initialEvents, initialRunning, initialRank⟩ :=
    Domain.spawned_body operations old mask registers flags created spawned
  have initialValid := (createdValid.2 0 initial initialAt).2
  have initialEntry : initial.entry = Domain.entry mask registers flags := by
    have chain := initialValid.phase.shape
    rw [initialRunning, initialEvents] at chain
    exact chain.nil_context.symm.trans initialContext
  have target : initial.returnAddress = 8192 := by
    have read := initialValid.target
    rw [initialEntry] at read
    change readWord (toMemory created.1.shared.legacy.shared.resources.space) 32768 =
      .ok initial.returnAddress at read
    rw [resources, Domain.prepared_caller _ bound old] at read
    exact (Except.ok.inj read).symm
  have rankLength : afs.length = initial.rank := length.trans initialRank.symm
  have legal := legal_ownSelections created.1 0 initial afs initialAt (Nat.le_of_eq rankLength)
  obtain ⟨scheduled, current, joined, success, currentAt, completed, collected,
    joinedValid, context, gone, currentResources, currentCells⟩ :=
    ownSelections_join created.1 0 initial afs createdValid initialAt rankLength
  have scheduledValid := schedule_wellFormed _ _ _ createdValid success
  have currentValid := (scheduledValid.2 0 current currentAt).2
  have trace := schedule_instructions _ _ _ success
  obtain ⟨origin, actualEvents⟩ := ownSelections_events _ _ _ _ _ _
    createdValid initialAt initialEvents success currentAt
  have currentOperations : current.operations = operations :=
    (congrArg WorkerOrigin.operations origin).symm.trans initialOperations
  have currentEntry : current.entry = Domain.entry mask registers flags :=
    (congrArg WorkerOrigin.entry origin).symm.trans initialEntry
  have requests : (events scheduled.2).map Atomics64.Event.orderedRequest =
      expectedRequests operations mask := by
    rw [← actualEvents, completed_requests currentValid completed, currentOperations, currentEntry]
    rfl
  have eventCount : (events scheduled.2).length = operations.length := by
    have counted := congrArg List.length requests
    simpa only [List.length_map, expectedRequests_length] using counted
  have preparedValid := Domain.prepared_valid (bodyBytes operations) (by simp) bound old
  have cellLive : created.1.shared.cells ⟨0⟩ = some ⟨0, ⟨0, 0⟩, 65536⟩ := by
    rw [(spawn_keeps _ _ _ _ _ preparedValid spawned).2.1]
    rfl
  have logicalTrace := trace.logicalTrace ⟨0⟩ ⟨0, ⟨0, 0⟩, 65536⟩ createdValid
    cellLive (spawned_allOn _ _ _ _ _ _ spawned)
  obtain ⟨final, finalRead, mathematical⟩ := logicalTrace.orderedMathematicalResult old initialRead
  rw [requests] at mathematical
  have finalReadback : loadQWord (toMemory joined.1.shared.legacy.shared.resources.space) 65536 = .ok final := by
    rw [currentResources]
    exact finalRead
  obtain ⟨revokedWorker, revokedAt, handleRevoked, codeRevoked, stackRevoked⟩ :=
    join_revokes _ _ _ _ scheduledValid collected
  have sameWorker := Option.some.inj (revokedAt.symm.trans currentAt)
  subst revokedWorker
  obtain ⟨rsp, rip, registersFrame, flagsFrame⟩ :=
    joined_private_frame trace.managed createdValid 0 initial initialAt 0 joined collected
  rw [initialEntry] at rsp registersFrame flagsFrame
  rw [target] at rip
  have history : History (Domain.prepared (bodyBytes operations) old)
      ([none] ++ scheduled.2.map Prod.snd ++ [none]) joined.1 :=
    (History.next (.spawn spawned) trace.managed).trans (.next (.join collected) .refl)
  exact ⟨{
    created := created, initial := initial, scheduled := scheduled, completed := current,
    joined := joined, final := final, setupSuccess := setup, ready := ready,
    spawnSuccess := spawned, identifier := identifier, createdValid := createdValid,
    initialAt := initialAt, initialOperations := initialOperations, initialEntry := initialEntry,
    initialEvents := initialEvents, initialRank := initialRank, createdResources := resources,
    initialRead := initialRead, legal := legal, scheduleSuccess := success,
    instructionTrace := trace, selections := schedule_selections _ _ _ success,
    afChoices := by rw [schedule_selections _ _ _ success]; exact ownSelections_afs 0 afs,
    instructionCount := (schedule_length _ _ _ success).trans ((ownSelections_length 0 afs).trans length),
    scheduledValid := scheduledValid, completedAt := currentAt, completedPhase := completed,
    completedValid := currentValid, completedOperations := currentOperations, completedEntry := currentEntry,
    actualEvents := actualEvents, eventCount := eventCount, requests := requests,
    actualReturn := ownSelections_return _ _ _ _ _ createdValid (by omega) success currentAt completed,
    logicalTrace := logicalTrace, joinSuccess := collected, joinedValid := joinedValid,
    returnedContext := context, workerGone := gone, handleRevoked := handleRevoked,
    codeRevoked := codeRevoked, stackRevoked := stackRevoked, currentResources := currentResources,
    currentCells := currentCells, persistentCell := by rw [currentCells]; exact logicalTrace.final_cell,
    beforeCollectionRead := finalRead, readback := finalReadback, mathematicalResult := mathematical,
    stackPointer := rsp, returnAddress := rip, registersPreserved := registersFrame,
    flagsPreserved := flagsFrame, managedHistory := history }⟩

/-- This uninterrupted body solves the independent union task for all full64
inputs and every four AF choices. Its three actual events remain visible in
the execution witness. No claim is made about arbitrary peer interleavings. -/
theorem union_xor_xor_execution (old mask : Word) (registers : Register → Word)
    (flags : Word) (afs : List Bool) (length : afs.length = 4) :
    ∃ execution : BodyExecution [.bor, .bxor, .bxor] old mask registers flags afs,
      Logical64.MathematicalResult .union old mask execution.final := by
  obtain ⟨execution⟩ := arbitrary_body_execution [.bor, .bxor, .bxor] (by decide)
    old mask registers flags afs length
  refine ⟨execution, Logical64.OrderedMathematicalResult.union_xor_xor ?_⟩
  exact execution.mathematicalResult

/-- RET-only bodies execute and collect for every initial word and caller
context, produce no RMW events, and preserve the independent initial value. -/
theorem return_only_execution (old mask : Word) (registers : Register → Word)
    (flags : Word) (afs : List Bool) (length : afs.length = 1) :
    ∃ execution : BodyExecution [] old mask registers flags afs,
      execution.final = old ∧ events execution.scheduled.2 = [] := by
  obtain ⟨execution⟩ := arbitrary_body_execution [] (by decide) old mask registers flags afs length
  exact ⟨execution, Logical64.OrderedMathematicalResult.nil_iff.mp execution.mathematicalResult,
    List.eq_nil_of_length_eq_zero execution.eventCount⟩

end EDSL.OS.AtomicSetThreads64.Programs
