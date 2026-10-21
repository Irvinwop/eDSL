/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Behavior
import EDSL.OS.PlainCallSafety64
import EDSL.X86.VCGen.PlainMethods.ABI

/-!
Reusable transport of actual plain-method access/return evidence into the
independent Plain64 completed-behavior contract. Input kinds fix both full64
operand directions; dependent replies are transported only along the actual
admission operation equality. All dynamic evidence refers to the same original
production schedule, access positions, local read and RET origin.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallBehavior64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open X86.VCGen
open PlainCallAdmission64

/-- Transport an actual operation's reply along its checked admission equality.
The load branch retains the full word; the store branch retains unit. -/
def transportReply (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind)
    (reply : operation.Reply) : input.Reply := by
  cases input <;> cases same <;> exact reply

/-- Broad independent recognition agrees with the existing broad engine
recognition, including incorrect operands and opposite operation directions. -/
theorem data_instruction_iff (instruction : Sequential.Instruction) :
    DataInstruction instruction ↔ PlainMethods.IsAccess instruction := by
  cases instruction <;> rfl

theorem data_access_dispatched {before : TSO64.State} {actions : List Action}
    {actual : TSO64.State × List Observation} {tid index : Nat}
    (access : DataAccessAt before actions actual tid index) :
    PlainMethods.DispatchedAt tid before actions actual index := by
  obtain ⟨boundary, worker, instruction, af, issued, live, fetched, recognized⟩ := access
  exact ⟨boundary.prior, boundary.action, boundary.next, boundary.prefixRun,
    boundary.selected, boundary.actualStep, af, worker, instruction, issued, live,
    fetched, (data_instruction_iff instruction).mp recognized⟩

/-- Exact payload membership is obtained from newestQWord's production lookup,
not inferred from equal bits, a desired graph writer or invocation RAM. -/
theorem selected_read {state : TSO64.State} {worker : Worker} {address value : Word}
    (loaded : loadQWord (localCPU state worker).memory address = .ok value)
    (source : (match StoreBuffer.Mixed.newestQWord (payload worker.pending) address with
      | some origin => Except.ok origin.value
      | none => loadQWord (published state.world) address) = .ok value) :
    SelectedRead state worker address value := by
  refine ⟨loaded, ?_⟩
  cases found : StoreBuffer.Mixed.newestQWord (payload worker.pending) address with
  | none => simpa only [found] using source
  | some origin =>
    have same : origin.value = value := by
      exact Except.ok.inj (by simpa only [found] using source)
    refine ⟨same, ?_⟩
    simpa only [same] using (StoreBuffer.Mixed.newestQWord_spec
      (payload worker.pending) address origin found).1

private theorem arguments_registers {input : Input} {initial current : Worker}
    (arguments : Arguments input initial)
    (registers : current.context.registers = initial.context.registers) :
    Arguments input current := by
  intro index argument supplied
  rw [registers]
  exact arguments index argument supplied

/-- The response word agrees with the independently selected input, including
preserved full RAX for a unit-returning store. -/
theorem response_rax (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind) {initial : Worker}
    {entry : Register → Word} (original : entry = initial.context.registers)
    (reply : operation.Reply) :
    operation.registers entry reply .rax = replyRAX input initial (transportReply input same reply) := by
  subst entry
  cases input <;> cases same
  · exact AtomicMethods.written_same _ _ _
  · rfl

private theorem response_other (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind) (entry : Register → Word)
    (reply : operation.Reply) (register : Register)
    (preserved : input.site.kind = .loadAcquire → register ≠ .rax) :
    operation.registers entry reply register = entry register := by
  cases input <;> cases same
  · exact AtomicMethods.written_other _ _ _ _ (preserved rfl)
  · rfl

/-- Lift the production body result into the complete independent scalar call
frame. Current resources/ABI and the actual original caller are retained. -/
theorem call_frame {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok actual) {final : Worker}
    (live : actual.1.workers[tid]? = some final)
    {reply : admitted.invocation.method.operation.Reply}
    (post : PlainMethods.BodyPost admitted.invocation.method final reply) :
    CallFrame input (transportReply input admitted.operation reply) before actual.1 tid
      admitted.invocation.initial final admitted.invocation.method.reference := by
  have abi := post.return_frame admitted.invocation.current admitted.invocation.live
    admitted.invocation.entry admitted.scalar
    (schedule_wellFormed admitted.invocation.current.valid success) live
  refine ⟨abi, ?_, ?_, ?_, abi.collect⟩
  · intro register notRsp preserved
    rw [post.registers, AtomicMethods.written_other _ .rsp _ register notRsp]
    exact (response_other input admitted.operation _ reply register preserved).trans
      (congrFun admitted.registers register)
  · exact post.rax.trans (response_rax input admitted.operation admitted.registers reply)
  · have queue := post.queue
    rw [PlainCallSafety64.queue_after admitted] at queue
    exact ⟨queue.counter, queue.suffix⟩

/-- Access effects specialize through the actual admitted operation equality;
there is no selection of a result by a postcondition or final RAM snapshot. -/
theorem data_effect (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind)
    {initial worker : Worker} {reference : Queue.ManagedRef}
    {state : TSO64.State} {action : Action} {next : TSO64.State × Observation}
    {tid : Nat} {af : Bool} {entry : Register → Word} {counter : Nat}
    {reply : operation.Reply}
    (original : entry = initial.context.registers) (count : counter = initial.nextStore)
    (arguments : Arguments input initial) (descriptor : reference.cell = input.cell)
    (issued : action = .issue tid af) (live : state.workers[tid]? = some worker)
    (registers : worker.context.registers = entry)
    (effect : OrdinaryEffect state tid worker operation.instruction af next .sharedCell)
    (value : PlainMethods.AccessValue operation reference entry counter state worker reply)
    (observed : next.2 = .ordinary tid) :
    DataEffect input initial worker reference state action next tid
      (transportReply input same reply) := by
  cases input with
  | loadAcquire image target cell occurrence =>
    cases same
    have read : SelectedRead state worker cell.address reply := by
      have selected := selected_read value.1 value.2
      simpa only [descriptor, Input.cell] using selected
    obtain ⟨loaded, actualRead, _authority, installed⟩ := effect.loadMem64
    have operand : (Sequential.Address.base .rdi).eval (localCPU state worker) = cell.address := by
      change worker.context.registers .rdi = cell.address
      rw [registers, original]
      exact arguments.rdi
    rw [operand] at actualRead
    have equal : loaded = reply := Except.ok.inj (actualRead.symm.trans read.1)
    subst loaded
    refine ⟨af, issued, effect, read, ?_, ?_⟩
    · rw [installed]
      rfl
    · rw [installed]
      refine ⟨_, List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl, rfl, ?_⟩
      simp only [Context.ofCPU, X86.State.writeRegister, ↓reduceIte]
      rfl
  | storeRelease image target cell word occurrence =>
    cases same
    have source : entry .rsi = word := by
      rw [original]
      exact arguments.store_rsi
    have actualSource : worker.context.registers .rsi = word :=
      (congrFun registers .rsi).trans source
    have actualCount : worker.nextStore = initial.nextStore := value.2.1.trans count
    have queued : QueueEffect state worker (.storeMem64 (.base .rdi) .rsi)
        ⟨worker.pending ++ [.managed reference word initial.nextStore], initial.nextStore + 1⟩
        .sharedCell := by
      simpa only [source, count] using value.2.2
    refine ⟨af, issued, actualSource, actualCount, effect, ?_⟩
    cases effect with
    | @intro update observation _supported _bounds _decoded _reads queue _executed finish =>
      have updateEq : update =
          ⟨worker.pending ++ [.managed reference word initial.nextStore], initial.nextStore + 1⟩ :=
        Except.ok.inj ((ManagedRules.queue_checked queue).symm.trans
          (ManagedRules.queue_checked queued))
      cases updateEq
      cases finish with
      | next _outcome =>
        exact ⟨rfl, _, List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl, rfl⟩
      | returned _outcome => cases observed

/-- Deterministic actual accesses cannot acquire different typed replies.
Equality is proved from the same local read, not assumed from final RAX. -/
private theorem origin_reply_unique {method : PlainMethods.Method} {tid : Nat}
    {state : TSO64.State} {action : Action} {next : TSO64.State × Observation}
    {first second : method.operation.Reply}
    (one : PlainMethods.AccessOrigin method tid state action next first)
    (two : PlainMethods.AccessOrigin method tid state action next second) : first = second := by
  rcases method with ⟨bytes, operation, base, entry, flags, resources, reference,
    continuation, initialQueue, size, codeNoWrap, originalRsp, canonicalReturn, stackBound⟩
  cases operation with
  | store address source =>
    change PUnit at first second
    cases first
    cases second
    rfl
  | load address =>
    obtain ⟨_af, worker, _issuing, live, _actual, _observed, _resources, _registers,
      _counter, _operand, _selected, _fetched, _effect, value⟩ := one.evidence
    obtain ⟨_af, other, _issuing, otherLive, _actual, _observed, _resources, _registers,
      _counter, _operand, _selected, _fetched, _effect, otherValue⟩ := two.evidence
    have same : other = worker := Option.some.inj (otherLive.symm.trans live)
    subst other
    exact Except.ok.inj (value.1.symm.trans otherValue.1)

private theorem access_reply_unique {method : PlainMethods.Method} {tid : Nat}
    {before : TSO64.State} {actions : List Action} {actual : TSO64.State × List Observation}
    {index : Nat} {first second : method.operation.Reply}
    (one : PlainMethods.AccessAt method tid before actions actual index first)
    (two : PlainMethods.AccessAt method tid before actions actual index second) : first = second := by
  obtain ⟨state, action, next, prior, selected, _observed, step, origin⟩ := one
  obtain ⟨other, otherAction, otherNext, otherPrior, otherSelected, _observed,
    otherStep, otherOrigin⟩ := two
  have stateEq : other = state := congrArg Prod.fst (Except.ok.inj (otherPrior.symm.trans prior))
  have actionEq : otherAction = action := Option.some.inj (otherSelected.symm.trans selected)
  subst other
  subst otherAction
  have nextEq : otherNext = next := Except.ok.inj (otherStep.symm.trans step)
  subst otherNext
  exact origin_reply_unique origin otherOrigin

/-- A CompletedCall's own actual access reply is the one retained by the final
body result. This connects existing witnesses without a future-At premise. -/
theorem completed_body {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (completed : PlainMethods.CompletedCall admitted.invocation.method tid before actions actual)
    {final : Worker} (live : actual.1.workers[tid]? = some final)
    (returned : final.phase = .returned) :
    PlainMethods.BodyPost admitted.invocation.method final completed.reply := by
  obtain ⟨_current, reply, body, one, _issues, _observed⟩ := PlainMethods.all_completed
    admitted.invocation.current admitted.invocation.live admitted.invocation.entry
      completed.execution live returned
  have equal : completed.reply = reply := access_reply_unique completed.access
    (one.at completed.access.dispatched)
  simpa only [equal] using body

/-- The engine request reply and independent reply are the same typed datum
along the checked operation equality, without choosing a replacement word. -/
private theorem request_reply_heq (input : Input) {operation : PlainMethods.Operation}
    (same : operation = fixedOperation input.site.kind) (object : Atomics64.CellId64)
    (entry : Register → Word) (reply : operation.Reply) :
    HEq (operation.requestReply object entry reply) (transportReply input same reply) := by
  cases input <;> cases same <;> exact HEq.rfl

private theorem call_ext (left right : Concurrency.AtomicCalls.Call Atomics64.CellId64 Word)
    (thread : left.thread = right.thread) (occurrence : left.occurrence = right.occurrence)
    (request : left.request = right.request) (reply : HEq left.reply right.reply)
    (invoked : left.invoked = right.invoked) (performed : left.performed = right.performed)
    (returned : left.returned = right.returned) : left = right := by
  cases left
  cases right
  cases thread
  cases occurrence
  cases request
  cases reply
  cases invoked
  cases performed
  cases returned
  rfl

/-- A complete independent output for one admitted slot and this exact
CompletedCall. Its call is literally the existing batch call, with actual
request/operation/occurrence equalities transporting the typed reply. -/
theorem outcome {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (completed : PlainMethods.CompletedCall admitted.invocation.method tid before actions actual)
    {final : Worker} (finalLive : actual.1.workers[tid]? = some final)
    (returned : final.phase = .returned) :
    ∃ output : Outcome input before actions actual tid,
      output.performed = completed.performed ∧ output.returned = completed.returned ∧
      output.call = completed.call admitted.invocation.occurrence := by
  have body := completed_body admitted completed finalLive returned
  obtain ⟨state, action, next, prior, selected, observed, stepped, origin⟩ := completed.access
  obtain ⟨af, worker, issued, live, _actual, ordinary, resources, registers, _counter,
    operand, selection, fetched, effect, value⟩ := origin.evidence
  obtain ⟨responseState, responseAction, responseNext, responsePrior, responseSelected,
    responseObserved, responseStep, _responseValue, responseOrigin⟩ := completed.response
  let accessBoundary : StepAt before actions actual completed.performed :=
    ⟨state, action, next, prior, selected, observed, stepped⟩
  let responseBoundary : StepAt before actions actual completed.returned :=
    ⟨responseState, responseAction, (responseNext, .returned tid), responsePrior,
      responseSelected, responseObserved, responseStep⟩
  let reply := transportReply input admitted.operation completed.reply
  have accessingArguments : Arguments input worker :=
    arguments_registers admitted.entryFacts.arguments (registers.trans admitted.registers)
  have accessingSelection : atomicFor state.world worker.resources input.cell.address =
      some (admitted.invocation.method.reference.identifier,
        admitted.invocation.method.reference.handle, admitted.invocation.method.reference.cell) := by
    rw [← admitted.address, ← operand]
    exact selection
  have access : DataEffect input admitted.invocation.initial worker
      admitted.invocation.method.reference state action next tid reply :=
    data_effect input admitted.operation admitted.registers admitted.counter
      admitted.entryFacts.arguments admitted.descriptor issued live registers effect value ordinary
  have dispatched : DataAccessAt before actions actual tid completed.performed := by
    refine ⟨accessBoundary, worker, admitted.invocation.method.operation.instruction, af,
      issued, live, fetched, ?_⟩
    cases admitted.invocation.method.operation <;> exact True.intro
  have response : Return.ReturnOrigin responseState responseAction
      (responseNext, .returned tid) tid (replyRAX input admitted.invocation.initial reply)
      .sharedCell := by
    have agrees := response_rax input admitted.operation admitted.registers completed.reply
    change Return.ReturnOrigin responseState responseAction (responseNext, .returned tid) tid
      (admitted.invocation.method.operation.registers admitted.invocation.method.entry
        completed.reply .rax) .sharedCell at responseOrigin
    rw [agrees] at responseOrigin
    exact responseOrigin
  let output : Outcome input before actions actual tid := {
    initial := admitted.invocation.initial
    initialLive := admitted.invocation.live
    final := final
    reference := admitted.invocation.method.reference
    target := admitted.target
    descriptor := admitted.descriptor
    originalSelection := admitted.selected
    reply := reply
    performed := completed.performed
    returned := completed.returned
    accessBoundary := accessBoundary
    accessing := worker
    accessingLive := live
    accessingResources := resources.trans admitted.resources
    accessingArguments := accessingArguments
    accessingSelection := accessingSelection
    access := access
    dispatched := dispatched
    uniqueAccess := fun index recognized => completed.performed_unique (data_access_dispatched recognized)
    responseBoundary := responseBoundary
    response := response
    responseObserved := rfl
    uniqueResponse := completed.responseUnique
    beforeReturn := completed.beforeReturn
    frame := call_frame admitted completed.execution finalLive body }
  refine ⟨output, rfl, rfl, ?_⟩
  apply call_ext
  · rfl
  · exact admitted.occurrence.symm
  · exact admitted.request.symm
  · exact (request_reply_heq input admitted.operation _ _ completed.reply).symm
  · rfl
  · rfl
  · rfl

/-- A currently checked method dispatches an ordinary instruction at every
actual own issue. This excludes hidden LOCK effects independently of access
coverage or a chosen reply. -/
private theorem ordinary_dispatch {method : PlainMethods.Method} {tid : Nat}
    {state : TSO64.State} {point : PlainMethods.Point method.operation} {worker : Worker}
    {af : Bool} {next : TSO64.State × Observation}
    (current : PlainMethods.Current method state) (live : state.workers[tid]? = some worker)
    (located : PlainMethods.At method point worker)
    (success : TSO64.step state (.issue tid af) .sharedCell = .ok next) :
    ∃ instruction, TSO64.decode (fetchCPU state worker) = .ok (.ordinary instruction) := by
  cases point with
  | preamble offset padding =>
    obtain ⟨_running, pc, _registers, shape⟩ := located.location
    cases shape with
    | body node _ret _extent => exact ⟨_, (current.decode_node live located.resources node pc).1⟩
    | pad node _tail => exact ⟨_, (current.decode_node live located.resources node pc).1⟩
  | ret offset reply =>
    obtain ⟨_running, pc, _registers, node, _extent⟩ := located.location
    exact ⟨_, (current.decode_node live located.resources node pc).1⟩
  | done reply =>
    have phase := located.location.1
    simp [TSO64.step, issue, live, phase] at success

/-- Every observation of the actual admitted whole population is an ordinary
issue, an actual return, or an exact FIFO drain. No RMW/blocked observation is
silently dropped by the independent completed contract. -/
theorem observation_kind {before : TSO64.State}
    (invocations : (tid : Fin before.workers.length) → PlainMethods.Invocation before tid.val)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok actual)
    {index : Nat} {observation : Observation}
    (observed : actual.2[index]? = some observation) :
    (∃ tid, observation = .ordinary tid) ∨ (∃ tid, observation = .returned tid) ∨
      ∃ tid entry, observation = .drained tid entry := by
  obtain ⟨state, action, next, prior, _selected, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  cases action with
  | drain tid =>
    obtain ⟨_worker, entry, _tail, _output, _live, _fifo, _valid, _effect, same⟩ :=
      drain_effect stepped
    exact .inr (.inr ⟨tid, entry, congrArg Prod.snd same⟩)
  | issue tid af =>
    obtain ⟨issuing, live, _running, _code, _caller, _instruction, _fetched, _effect⟩ :=
      issue_effect stepped
    have bound : tid < before.workers.length := by
      have currentBound := (List.getElem_of_getElem? live).1
      have length : state.workers.length = before.workers.length :=
        ScheduleTrace.workers_length prior
      omega
    let slot : Fin before.workers.length := ⟨tid, bound⟩
    let admitted := invocations slot
    obtain ⟨current, _point, worker, _emissions, workerLive, located, _remaining,
      _replies, _trace⟩ := PlainMethods.schedule_preserves admitted.current admitted.live
        admitted.entry prior
    have same : issuing = worker := Option.some.inj (live.symm.trans workerLive)
    subst issuing
    obtain ⟨instruction, ordinary⟩ := ordinary_dispatch current workerLive located stepped
    cases step_origin stepped with
    | ordinary issuingLive _running _code _caller fetched effect =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish =>
        cases finish with
        | next _outcome => exact .inl ⟨tid, rfl⟩
        | returned _outcome => exact .inr (.inl ⟨tid, rfl⟩)
    | blocked issuingLive _running _code _caller fetched _bounds _nonempty =>
      have equal : _ = worker := Option.some.inj (issuingLive.symm.trans workerLive)
      rw [equal, ordinary] at fetched
      cases fetched
    | rmw issuingLive _running _code _caller fetched _bounds _empty _grant _effect =>
      have equal : _ = worker := Option.some.inj (issuingLive.symm.trans workerLive)
      rw [equal, ordinary] at fetched
      cases fetched

/-- Generic full completed behavior from independently admitted data and an
actual batch. The output's calls are exactly the original batch's calls. -/
theorem post_of_batch {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (batch : PlainMethods.BatchResult before actions actual (invocations static pre))
    (returned : TSO64.Returned actual.1) :
    ∃ post : Post before inputs actions actual, post.calls = batch.calls := by
  classical
  have ready : ∀ tid : Fin before.workers.length,
      ∃ output : Outcome (inputs tid) before actions actual tid.val,
        output.performed = (batch.completed tid).performed ∧
        output.returned = (batch.completed tid).returned ∧
        output.call = batch.call tid := by
    intro tid
    let admitted := admission static pre tid
    obtain ⟨final, live, _resources⟩ := schedule_worker_resources batch.success admitted.invocation.live
    exact outcome admitted (batch.completed tid) live (returned final (List.mem_of_getElem? live))
  let outputs := fun tid => Classical.choose (ready tid)
  have performed := fun tid => (Classical.choose_spec (ready tid)).1
  have responses := fun tid => (Classical.choose_spec (ready tid)).2.1
  have calls := fun tid => (Classical.choose_spec (ready tid)).2.2
  let post : Post before inputs actions actual := {
    scheduled := batch.success
    safe := PlainCallSafety64.safe_prefix static pre batch.success
    outcomes := outputs
    slots := batch.slots
    permutation := batch.slots_perm
    ordered := batch.slots_ordered.imp (by
      intro first second less
      change (outputs first).performed < (outputs second).performed
      rw [performed first, performed second]
      exact less)
    allReturns := by
      intro tid index observed
      obtain ⟨extracted, member, thread, position⟩ := batch.responded observed
      obtain ⟨slot, equal⟩ := batch.origin member
      subst extracted
      exact ⟨slot, thread, (responses slot).trans position⟩
    allAccesses := by
      intro tid index access
      obtain ⟨extracted, member, thread, position⟩ := batch.dispatched (data_access_dispatched access)
      obtain ⟨slot, equal⟩ := batch.origin member
      subst extracted
      exact ⟨slot, thread, (performed slot).trans position⟩
    noRMW := by
      intro tid event member
      obtain ⟨index, observed⟩ := List.mem_iff_getElem?.mp member
      rcases observation_kind (invocations static pre) batch.success observed with
        ⟨_other, impossible⟩ | ⟨_other, impossible⟩ | ⟨_other, _entry, impossible⟩ <;> cases impossible
    noBlocked := by
      intro tid member
      obtain ⟨index, observed⟩ := List.mem_iff_getElem?.mp member
      rcases observation_kind (invocations static pre) batch.success observed with
        ⟨_other, impossible⟩ | ⟨_other, impossible⟩ | ⟨_other, _entry, impossible⟩ <;> cases impossible }
  refine ⟨post, ?_⟩
  apply List.map_congr_left
  intro tid _member
  exact calls tid

/-- Actual returned executions admit the complete independent Post without a
caller-supplied batch, outcome, future point, source witness or desired reply. -/
theorem post {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok actual)
    (returned : TSO64.Returned actual.1) : Nonempty (Post before inputs actions actual) := by
  have slotsReturned : ∀ tid : Fin before.workers.length,
      ∃ worker, actual.1.workers[tid.val]? = some worker ∧ worker.phase = .returned := by
    intro tid
    obtain ⟨worker, live, _resources⟩ := schedule_worker_resources success
      (invocations static pre tid).live
    exact ⟨worker, live, returned worker (List.mem_of_getElem? live)⟩
  obtain ⟨batch⟩ := PlainMethods.completed_batch (invocations static pre) success slotsReturned
  obtain ⟨output, _calls⟩ := post_of_batch static pre batch returned
  exact ⟨output⟩

end EDSL.OS.PlainCallBehavior64

#audit_edsl
