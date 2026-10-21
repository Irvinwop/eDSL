/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Progress
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Capture

/-!
The checked plain-method access is the production atomic scanner's actual
access at the same original action position. The source order is an explicit
interface annotation: MOV bytes alone do not encode acquire or release.

Loads retain their actual selected full reference, current mixed-FIFO/RAM
read and exact writer key. Stores retain their original complete queued entry,
including the occurrence allocated by the actual prestate counter. Incoming
queues and writer maps stay explicit boundaries. No C23 legality, graph-checker
success, quiescence, fresh queue history or native correspondence is assumed.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods.AtomicEvents
open OS OS.TSO64 OS.TSO64.C23Projection

/-- The declared primitive interface, independent of decoding or observations.
The RMW field makes this annotation usable with a mixed scanner; this module
does not construct an RMW method or infer a source language's memory order. -/
def orders : AtomicTrace.Orders :=
  ⟨fun _ _ => .acquire, fun _ _ => .release, fun _ _ => .acqRel⟩

/-- Exact interface access data. In a store, the writer occurrence belongs to
the saved allocation counter, rather than to FIFO length or a later drain. -/
def access (operation : Operation) (reference : Queue.ManagedRef)
    (entry : Register → Word) (occurrence : Nat) (source : AtomicTrace.WriterId) :
    operation.Reply → AtomicTrace.Access :=
  match operation with
  | .load _ => fun value => .load reference value source
  | .store _ register => fun _ => .store reference (entry register) occurrence

def event (method : Method) (tid position : Nat) (reply : method.operation.Reply)
    (source : AtomicTrace.WriterId) : AtomicTrace.Event :=
  ⟨position, tid, access method.operation method.reference method.entry
    method.initialQueue.nextStore source reply⟩

theorem event_position (method : Method) (tid position : Nat)
    (reply : method.operation.Reply) (source : AtomicTrace.WriterId) :
    (event method tid position reply source).position = position := rfl

theorem event_thread (method : Method) (tid position : Nat)
    (reply : method.operation.Reply) (source : AtomicTrace.WriterId) :
    (event method tid position reply source).tid = tid := rfl

theorem event_object (method : Method) (tid position : Nat)
    (reply : method.operation.Reply) (source : AtomicTrace.WriterId) :
    (event method tid position reply source).object = method.reference.handle.cell := by
  cases method with
  | mk bytes operation base entry entryFlags resources reference returnAddress initialQueue
      size codeNoWrap originalRsp returnCanonical stackNoWrap =>
    cases operation <;> rfl

/-- The source event equals the independently fixed request and its typed
reply, including the thread, persistent object identity, full value and order.
This equation asserts no atomic-fragment legality theorem. -/
theorem event_toSource (method : Method) (tid position : Nat)
    (reply : method.operation.Reply) (source : AtomicTrace.WriterId) :
    (event method tid position reply source).toSource orders =
      ⟨some tid, method.request.object,
        method.request.access (method.requestReply reply)⟩ := by
  cases method with
  | mk bytes operation base entry entryFlags resources reference returnAddress initialQueue
      size codeNoWrap originalRsp returnCanonical stackNoWrap =>
    cases operation <;> rfl

private theorem store_issued {state : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {tid : Nat} {af : Bool} {worker : Worker}
    {address : Sequential.Address} {register : Register} {reference : Queue.ManagedRef}
    (valid : Atomics64.WellFormed state.world)
    (issuing : action = .issue tid af)
    (success : OS.TSO64.step state action .sharedCell = .ok result)
    (live : state.workers[tid]? = some worker)
    (fetched : OS.TSO64.decode (fetchCPU state worker) =
      .ok (.ordinary (.storeMem64 address register)))
    (selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
      some (reference.identifier, reference.handle, reference.cell))
    (effect : OrdinaryEffect state tid worker (.storeMem64 address register) af result .sharedCell) :
    StoreHistory.Issued state action result .sharedCell tid
      (.managed reference (worker.context.registers register) worker.nextStore) := by
  have originalEffect := effect
  cases effect with
  | intro supported bounds decoded reads queue executed finish =>
    have update := ManagedAccess.queue_storeMem64_identity valid selected queue
    rw [update] at finish
    obtain ⟨current, operand⟩ := ManagedAccess.selected_current selected
    change reference.cell.address = address.eval (localCPU state worker) at operand
    have absent : grantFor state.world worker.resources
        ⟨address.eval (localCPU state worker), .qword (worker.context.registers register)⟩ = none := by
      rw [← operand]
      exact ManagedAccess.grantFor_managed_none valid current _
    exact .ordinary issuing success live fetched originalEffect rfl
      (.managed reference (worker.context.registers register) absent rfl rfl selected) finish

/-- Construct the production atomic access directly from the plain method's
real access origin. Load source existence uses present WF and sequencing; store
issue uses the actual decoded OrdinaryEffect and its exact QueueEffect.
Neither scanner acceptance nor a later cutpoint is an input. -/
theorem atomicStep {method : Method} {tid position : Nat} {state : OS.TSO64.State}
    {action : Action} {result : OS.TSO64.State × Observation} {reply : method.operation.Reply}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (origin : AccessOrigin method tid state action result reply)
    (writers : PublishedHistory.Writers) :
    ∃ source, AtomicTrace.AtomicStep state action result .sharedCell position writers
      (event method tid position reply source) := by
  rcases method with ⟨bytes, operation, base, entry, entryFlags, resources, reference,
    returnAddress, initialQueue, size, codeNoWrap, originalRsp, returnCanonical, stackNoWrap⟩
  cases operation with
  | load address =>
    obtain ⟨af, worker, issuing, live, actual, observed, sameResources, registers, counter,
      operandAddress, selected, fetched, effect, loaded, read⟩ := origin.evidence
    obtain ⟨current, operand⟩ := ManagedAccess.selected_current selected
    change reference.cell.address = address.eval (localCPU state worker) at operand
    have absent : grantFor state.world worker.resources
        ⟨address.eval (localCPU state worker), .qword 0⟩ = none := by
      rw [← operand]
      exact ManagedAccess.grantFor_managed_none valid.1 current 0
    obtain ⟨source, sourceOrigin⟩ := AtomicTrace.load_source_exists
      valid sequenced live current loaded writers
    exact ⟨source, .load
      (.intro issuing live fetched effect rfl absent selected current operand loaded)
      live sourceOrigin⟩
  | store address register =>
    obtain ⟨af, worker, issuing, live, actual, observed, sameResources, registers, counter,
      operandAddress, selected, fetched, effect, originalSource, originalCounter, queue⟩ :=
      origin.evidence
    have issued := store_issued valid.1 issuing actual live fetched selected effect
    rw [originalSource, originalCounter] at issued
    exact ⟨.initial reference.handle.cell, .store issued⟩

/-- Deterministic classification excludes a second different event at this
actual access. This identifies the complete event, including its source key;
matching values or addresses alone would not suffice. -/
theorem atomicStep_unique {method : Method} {tid position : Nat} {state : OS.TSO64.State}
    {action : Action} {result : OS.TSO64.State × Observation} {reply : method.operation.Reply}
    {writers : PublishedHistory.Writers} {actualEvent : AtomicTrace.Event}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (origin : AccessOrigin method tid state action result reply)
    (actual : AtomicTrace.AtomicStep state action result .sharedCell position writers actualEvent) :
    ∃ source, actualEvent = event method tid position reply source := by
  obtain ⟨source, expected⟩ := atomicStep valid sequenced origin writers
  exact ⟨source, Option.some.inj ((AtomicTrace.capture_complete actual).symm.trans
    (AtomicTrace.capture_complete expected))⟩

/-- The bridge preserves the original action index and writer-map boundary.
Every prefix observation advances the map, even a drain or blocked peer issue.
No store occurrence is created for a queue entry already present initially. -/
theorem eventAt {method : Method} {tid index offset : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {reply : method.operation.Reply}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : schedule state actions .sharedCell = .ok result)
    (origin : AccessAt method tid state actions result index reply)
    (writers : PublishedHistory.Writers) :
    ∃ source, AtomicTrace.EventAt .sharedCell (event method tid (offset + index) reply source)
      index state actions result offset writers := by
  obtain ⟨before, action, first, prefixRun, selected, observed, executed, origin⟩ := origin
  obtain ⟨source, actual⟩ := atomicStep (schedule_wellFormed valid prefixRun)
    (schedule_sequenced sequenced prefixRun) origin
    (PublishedHistory.after offset (result.2.take index) writers)
  exact ⟨source, AtomicTrace.EventAt.of_prestate success prefixRun selected executed actual⟩

/-- Every actual plain access is emitted by the real atomic scanner. The scan
is ordinary production execution with an observation annotation; this theorem
does not use a caller-supplied successful capture or legality check. -/
theorem scan_coverage {method : Method} {tid index offset : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : AtomicTrace.Result} {reply : method.operation.Reply}
    {writers : PublishedHistory.Writers}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : AtomicTrace.scan state actions .sharedCell offset writers = .ok result)
    (origin : AccessAt method tid state actions result.execution index reply) :
    ∃ source, event method tid (offset + index) reply source ∈ result.events := by
  obtain ⟨source, actual⟩ := eventAt valid sequenced (AtomicTrace.scan_scheduled success)
    origin writers
  exact ⟨source, AtomicTrace.scan_complete success actual⟩

/-- Independent MOV64 dispatch coverage composes with the production scanner.
The reply is obtained from the complete access trace, never from a requested
final register value or a selected event with a matching payload. -/
theorem scan_dispatched {method : Method} {tid index offset : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : AtomicTrace.Result}
    {emissions : List (Option method.operation.Reply)} {writers : PublishedHistory.Writers}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : AtomicTrace.scan state actions .sharedCell offset writers = .ok result)
    (trace : AccessTrace method tid state actions result.execution emissions)
    (dispatched : DispatchedAt tid state actions result.execution index) :
    ∃ reply source, emissions[index]? = some (some reply) ∧
      event method tid (offset + index) reply source ∈ result.events := by
  obtain ⟨reply, captured, origin⟩ := trace.coverage_at dispatched
  obtain ⟨source, emitted⟩ := scan_coverage valid sequenced success origin
  exact ⟨reply, source, captured, emitted⟩

/-- A rival event at the same original index is the same complete event.
Determinism aligns its independently supplied real prefix with the plain
method prefix before applying the primitive event uniqueness theorem. -/
theorem eventAt_unique {method : Method} {tid index offset : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {reply : method.operation.Reply} {writers : PublishedHistory.Writers}
    {actualEvent : AtomicTrace.Event}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (origin : AccessAt method tid state actions result index reply)
    (actual : AtomicTrace.EventAt .sharedCell actualEvent index state actions result offset writers) :
    ∃ source, actualEvent = event method tid (offset + index) reply source := by
  obtain ⟨before, action, first, prefixRun, selected, observed, executed, origin⟩ := origin
  obtain ⟨atomicBefore, atomicAction, atomicFirst, atomicPrefix, atomicSelected,
    atomicObserved, atomicExecuted, atomicOrigin⟩ := actual.prestate
  have sameBefore : atomicBefore = before :=
    congrArg Prod.fst (Except.ok.inj (atomicPrefix.symm.trans prefixRun))
  have sameAction : atomicAction = action := Option.some.inj (atomicSelected.symm.trans selected)
  subst atomicBefore
  subst atomicAction
  have sameFirst : atomicFirst = first := Except.ok.inj (atomicExecuted.symm.trans executed)
  subst atomicFirst
  exact atomicStep_unique (schedule_wellFormed valid prefixRun)
    (schedule_sequenced sequenced prefixRun) origin atomicOrigin

/-- The scanner cannot insert a different event at a known plain access.
This is stronger than payload equality: reference, occurrence, source identity,
thread and original position are identified together. -/
theorem scan_unique_at {method : Method} {tid index offset : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : AtomicTrace.Result} {reply : method.operation.Reply}
    {writers : PublishedHistory.Writers} {actualEvent : AtomicTrace.Event}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : AtomicTrace.scan state actions .sharedCell offset writers = .ok result)
    (origin : AccessAt method tid state actions result.execution index reply)
    (member : actualEvent ∈ result.events) (position : actualEvent.position = offset + index) :
    ∃ source, actualEvent = event method tid (offset + index) reply source := by
  obtain ⟨actualIndex, actual⟩ := AtomicTrace.scan_sound valid sequenced success member
  have sameIndex : actualIndex = index := by have := actual.position; omega
  subst actualIndex
  exact eventAt_unique valid sequenced origin actual

private theorem full_store_access {instruction : Sequential.Instruction}
    {state : X86.State} {address value : Word}
    (intent : instruction.storeIntent64 state = some (address, value)) : IsAccess instruction := by
  cases instruction <;>
    simp only [Sequential.Instruction.storeIntent64, reduceCtorEq] at intent
  exact True.intro

/-- Recognize only the scanner's ordinary full-width accesses, independently
of the method's expected operation, reference, source register or result. -/
def PlainAccess : AtomicTrace.Access → Prop
  | .load .. | .store .. => True
  | .rmw .. => False

/-- An actual classified ordinary atomic access is an independently recognized
MOV64 dispatch by its event thread. Managed stores cannot arise from a DWORD
intent: the real admission requires the actual store's qword value. -/
theorem plain_dispatched {state : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {position : Nat}
    {writers : PublishedHistory.Writers} {actualEvent : AtomicTrace.Event}
    (actual : AtomicTrace.AtomicStep state action result .sharedCell position writers actualEvent)
    (plain : PlainAccess actualEvent.access) : OwnAccess actualEvent.tid state action := by
  cases actual with
  | load origin sourceLive source =>
    cases origin with
    | @intro af worker destination address issuing live fetched effect shared absent selected current operand loaded =>
      exact ⟨af, worker, .loadMem64 destination address, issuing, live, fetched, True.intro⟩
  | store issued =>
    cases issued with
    | @ordinary af worker instruction store observation issuing success live fetched effect intent admission committed =>
      have qword : ∃ value, store.value = .qword value := by
        cases admission with
        | managed reference value absent shared width selected => exact ⟨_, width⟩
      obtain ⟨value, width⟩ := qword
      have access : IsAccess instruction := by
        rcases storeIntent_origin intent with full | narrow
        · obtain ⟨stored, _, full⟩ := full
          exact full_store_access full
        · obtain ⟨stored, narrowWidth, _⟩ := narrow
          rw [width] at narrowWidth
          cases narrowWidth
      exact ⟨af, worker, instruction, issuing, live, fetched, access⟩
  | rmw observed origin => exact False.elim plain

/-- Every scanner-classified plain access by this thread is accounted for in
the method's complete access trace. This excludes extra own load/store events
even at an unexpected address or with an unexpected decoded register. The
RMW case is explicitly outside this theorem's plain-access premise. -/
theorem scan_plain_converse {method : Method} {tid offset : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : AtomicTrace.Result}
    {emissions : List (Option method.operation.Reply)} {writers : PublishedHistory.Writers}
    {actualEvent : AtomicTrace.Event}
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : AtomicTrace.scan state actions .sharedCell offset writers = .ok result)
    (trace : AccessTrace method tid state actions result.execution emissions)
    (member : actualEvent ∈ result.events) (thread : actualEvent.tid = tid)
    (plain : PlainAccess actualEvent.access) :
    ∃ index reply source, emissions[index]? = some (some reply) ∧
      actualEvent = event method tid (offset + index) reply source := by
  obtain ⟨index, actual⟩ := AtomicTrace.scan_sound valid sequenced success member
  obtain ⟨before, action, first, prefixRun, selected, observed, executed, origin⟩ := actual.prestate
  have own : OwnAccess tid before action := by
    rw [← thread]
    exact plain_dispatched origin plain
  have dispatched : DispatchedAt tid state actions result.execution index :=
    ⟨before, action, first, prefixRun, selected, executed, own⟩
  obtain ⟨reply, captured, methodOrigin⟩ := trace.coverage_at dispatched
  obtain ⟨source, equal⟩ := eventAt_unique valid sequenced methodOrigin actual
  exact ⟨index, reply, source, captured, equal⟩

private theorem ordinary_at_issue {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} {af : Bool}
    {result : OS.TSO64.State × Observation} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (success : OS.TSO64.step state (.issue tid af) .sharedCell = .ok result) :
    ∃ instruction, OS.TSO64.decode (fetchCPU state worker) = .ok (.ordinary instruction) := by
  cases point with
  | preamble offset padding =>
    obtain ⟨running, pc, registers, shape⟩ := located.location
    cases shape with
    | body node ret extent =>
      exact ⟨_, (current.decode_node live located.resources node pc).1⟩
    | pad node tail =>
      exact ⟨_, (current.decode_node live located.resources node pc).1⟩
  | ret offset reply =>
    obtain ⟨running, pc, registers, node, extent⟩ := located.location
    exact ⟨_, (current.decode_node live located.resources node pc).1⟩
  | done reply =>
    have returned := located.location.1
    simp [OS.TSO64.step, issue, live, returned] at success

private theorem rmw_dispatch {state : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {tid : Nat} {changed : Atomics64.FetchAddEvent}
    (observed : result.2 = .rmw tid changed)
    (origin : OS.TSO64.Origin state action result .sharedCell) :
    ∃ af worker instruction, action = .issue tid af ∧ state.workers[tid]? = some worker ∧
      OS.TSO64.decode (fetchCPU state worker) = .ok (.locked instruction) := by
  cases origin with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish =>
      cases finish <;> cases observed
  | blocked => cases observed
  | drained => cases observed
  | rmw live running code caller fetched bounds empty grant effect =>
    cases observed
    exact ⟨_, _, _, rfl, live, fetched⟩

/-- Every classified event of this currently checked method is a plain access.
A locked RMW at this own worker is excluded by the independently decoded
cutpoint, rather than being silently omitted from the coverage theorem. -/
theorem atomicStep_plain {method : Method} {tid position : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} {action : Action}
    {result : OS.TSO64.State × Observation} {writers : PublishedHistory.Writers}
    {actualEvent : AtomicTrace.Event}
    (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker)
    (success : OS.TSO64.step state action .sharedCell = .ok result)
    (actual : AtomicTrace.AtomicStep state action result .sharedCell position writers actualEvent)
    (thread : actualEvent.tid = tid) : PlainAccess actualEvent.access := by
  cases actual with
  | load => exact True.intro
  | store => exact True.intro
  | rmw observed origin =>
    obtain ⟨af, issuing, instruction, actionEq, issuingLive, fetched⟩ := rmw_dispatch observed origin
    dsimp only at thread
    rw [thread] at actionEq issuingLive
    have same : issuing = worker := Option.some.inj (issuingLive.symm.trans live)
    subst issuing
    rw [actionEq] at success
    obtain ⟨ordinaryInstruction, ordinaryFetched⟩ := ordinary_at_issue current live located success
    rw [fetched] at ordinaryFetched
    cases ordinaryFetched

/-- Full own-event coverage for a checked method, including exclusion of own
RMW events. Initial admission is present `Current`/`At`; all intermediate
cutpoints are derived from the actual production prefix. This conclusion
neither assumes future cutpoints nor discards unrecognized own events. -/
theorem scan_converse {method : Method} {tid offset : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} {actions : List Action}
    {result : AtomicTrace.Result} {emissions : List (Option method.operation.Reply)}
    {writers : PublishedHistory.Writers} {actualEvent : AtomicTrace.Event}
    (current : Current method state) (sequenced : Sequenced state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (success : AtomicTrace.scan state actions .sharedCell offset writers = .ok result)
    (trace : AccessTrace method tid state actions result.execution emissions)
    (member : actualEvent ∈ result.events) (thread : actualEvent.tid = tid) :
    ∃ index reply source, emissions[index]? = some (some reply) ∧
      actualEvent = event method tid (offset + index) reply source := by
  obtain ⟨index, actual⟩ := AtomicTrace.scan_sound current.valid sequenced success member
  obtain ⟨before, action, first, prefixRun, selected, observed, executed, origin⟩ := actual.prestate
  obtain ⟨currentBefore, next, after, prefixEmissions, afterLive, afterAt, remaining,
    replies, prefixTrace⟩ := schedule_preserves current live located prefixRun
  have plain := atomicStep_plain currentBefore afterLive afterAt executed origin thread
  exact scan_plain_converse current.valid sequenced success trace member thread plain

end EDSL.X86.VCGen.PlainMethods.AtomicEvents

#audit_edsl
