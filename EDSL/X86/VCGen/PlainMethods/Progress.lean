/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Model
import EDSL.X86.VCGen.ManagedAccess

/-!
One progress engine for checked padding/MOV64/RET methods, under sharedCell.
All execution is production execution. Proof-side access annotations retain
the actual prestate, admission, local read source or allocated store entry.
They assert neither invocation nor publication linearization, C23 legality,
compiler correspondence, nor a complete call-history adapter.
-/

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

def Point.replies {operation : Operation} : Point operation → List operation.Reply
  | .preamble .. => []
  | .ret _ reply | .done reply => [reply]

/-- Plain full-width MOV data accesses, independently of a method's expected
opcode, address or registers. RET's protected stack read is not a MOV access. -/
def IsAccess : Sequential.Instruction → Prop
  | .loadMem64 .. | .storeMem64 .. => True
  | _ => False

/-- Actual own MOV64 data dispatch, at any address and destination/source.
A successful step is provided separately by the trace; ordinary observations
alone do not identify an access, since padding also emits them. -/
def OwnAccess (tid : Nat) (state : OS.TSO64.State)
    (action : Action) : Prop :=
  ∃ af worker instruction, action = .issue tid af ∧ state.workers[tid]? = some worker ∧
    OS.TSO64.decode (fetchCPU state worker) = .ok (.ordinary instruction) ∧ IsAccess instruction

private theorem ownAccess_iff {tid : Nat} {state : OS.TSO64.State}
    {worker : Worker} {instruction : Sequential.Instruction} {af : Bool}
    (live : state.workers[tid]? = some worker)
    (decoded : OS.TSO64.decode (fetchCPU state worker) = .ok (.ordinary instruction)) :
    OwnAccess tid state (.issue tid af) ↔ IsAccess instruction := by
  constructor
  · rintro ⟨_, issuing, actualInstruction, _, issuingLive, fetched, access⟩
    have same : issuing = worker := Option.some.inj (issuingLive.symm.trans live)
    subst issuing
    have sameInstruction : instruction = actualInstruction :=
      OS.TSO64.Decoded.ordinary.inj (Except.ok.inj (decoded.symm.trans fetched))
    rw [sameInstruction]
    exact access
  · intro access
    exact ⟨af, worker, instruction, rfl, live, decoded, access⟩

private theorem padding_no_access (padding : Padding) : ¬ IsAccess padding.instruction := by
  cases padding <;> simp [AtomicMethods.Padding.instruction, IsAccess]

private theorem ret_no_access : ¬ IsAccess (.legacy .ret) := by
  simp [IsAccess]

/-- The load word is justified by the actual local qword read and its real
mixed-FIFO forwarding/published-RAM source. A store retains its exact complete
reference, original full source value and original nextStore occurrence. -/
def AccessValue (operation : Operation) (reference : Queue.ManagedRef)
    (entry : Register → Word) (occurrence : Nat) (state : OS.TSO64.State)
    (worker : Worker) : operation.Reply → Prop :=
  match operation with
  | .load _ => fun value =>
      loadQWord (localCPU state worker).memory reference.cell.address = .ok value ∧
      (match StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
      | some origin => Except.ok origin.value
      | none => loadQWord (published state.world) reference.cell.address) = .ok value
  | .store address source => fun _ =>
      worker.context.registers source = entry source ∧ worker.nextStore = occurrence ∧
      QueueEffect state worker (.storeMem64 address source)
        ⟨worker.pending ++ [.managed reference (entry source) occurrence], occurrence + 1⟩ .sharedCell

/-- Evidence about one actual access, including its input worker and actual
OrdinaryEffect. In particular a load response is never chosen from the final
RAX alone. No invocation-memory snapshot or desired return value is an input. -/
structure AccessOrigin (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (action : Action) (result : OS.TSO64.State × Observation)
    (reply : method.operation.Reply) : Prop where
  evidence : ∃ af worker,
    action = .issue tid af ∧ state.workers[tid]? = some worker ∧
    OS.TSO64.step state action .sharedCell = .ok result ∧ result.2 = .ordinary tid ∧
    worker.resources = method.resources ∧ worker.context.registers = method.entry ∧
    worker.nextStore = method.initialQueue.nextStore ∧
    method.operation.address.eval (localCPU state worker) = method.address ∧
    atomicFor state.world worker.resources (method.operation.address.eval (localCPU state worker)) =
      some (method.reference.identifier, method.reference.handle, method.reference.cell) ∧
    OS.TSO64.decode (fetchCPU state worker) = .ok (.ordinary method.operation.instruction) ∧
    OrdinaryEffect state tid worker method.operation.instruction af result .sharedCell ∧
    AccessValue method.operation method.reference method.entry method.initialQueue.nextStore
      state worker reply

theorem AccessOrigin.dispatched {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {action : Action} {result : OS.TSO64.State × Observation} {reply : method.operation.Reply}
    (origin : AccessOrigin method tid state action result reply) : OwnAccess tid state action := by
  obtain ⟨af, worker, actionEq, live, _, _, _, _, _, _, _, fetched, _, _⟩ := origin.evidence
  refine ⟨af, worker, method.operation.instruction, actionEq, live, fetched, ?_⟩
  cases method.operation <;> exact True.intro

/-- One annotation per real action, with both soundness and coverage. Coverage
excludes unrecorded own accesses; peers and head drains are quiet annotations. -/
structure Capture (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (action : Action) (result : OS.TSO64.State × Observation)
    (emitted : Option method.operation.Reply) : Prop where
  sound : ∀ reply, emitted = some reply → AccessOrigin method tid state action result reply
  complete : OwnAccess tid state action ↔ emitted.isSome = true

private theorem Capture.none {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {action : Action} {result : OS.TSO64.State × Observation}
    (absent : ¬ OwnAccess tid state action) : Capture method tid state action result none := by
  refine ⟨?_, ?_⟩
  · intro reply impossible
    cases impossible
  · simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
    exact absent

private theorem Capture.some {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {action : Action} {result : OS.TSO64.State × Observation} {reply : method.operation.Reply}
    (origin : AccessOrigin method tid state action result reply) :
    Capture method tid state action result (some reply) := by
  refine ⟨?_, ⟨fun _ => rfl, fun _ => origin.dispatched⟩⟩
  intro other same
  have equal : reply = other := Option.some.inj same
  subst other
  exact origin

private theorem install_self {state : OS.TSO64.State} {tid : Nat} {worker : Worker}
    (live : state.workers[tid]? = some worker) (world : World) (replacement : Worker) :
    (install state tid world replacement).workers[tid]? = some replacement :=
  List.getElem?_set_self (List.getElem_of_getElem? live).1

/-- The worker is the one actually installed by issue, not a postulated live
worker. Exactly one instruction retires for every constructed own advance. -/
structure Advance (method : Method) (tid : Nat) (state : OS.TSO64.State)
    (point : Point method.operation) (af : Bool) where
  result : OS.TSO64.State × Observation
  next : Point method.operation
  worker : Worker
  emitted : Option method.operation.Reply
  actual : OS.TSO64.step state (.issue tid af) .sharedCell = .ok result
  live : result.1.workers[tid]? = some worker
  located : At method next worker
  progress : next.remaining + 1 = point.remaining
  replies : point.replies ++ emitted.toList = next.replies
  capture : Capture method tid state (.issue tid af) result emitted
  retired : result.2.retired = 1

private theorem padding_execute (state : X86.State) (padding : Padding) (af : Bool) :
    Sequential.execute state padding.instruction af = .ok
      ⟨.next { state with rip := state.rip + BitVec.ofNat 64 padding.instruction.length }, []⟩ := by
  cases padding <;> rfl

private theorem advance_pc {rip base : Word} {offset length : Nat}
    (pc : rip = base + BitVec.ofNat 64 offset) :
    rip + BitVec.ofNat 64 length = base + BitVec.ofNat 64 (offset + length) := by
  rw [pc]
  exact (BitVec.add_assoc _ _ _).trans
    (congrArg (fun value => base + value) (BitVec.ofNat_add offset length).symm)

/-- The only operation split in the engine: both cases use the production
managed-access rule, with the same progress, queue-frame and trace interface. -/
private theorem advance_access {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {worker : Worker} {offset : Nat} (current : Current method state)
    (live : state.workers[tid]? = some worker)
    (located : At method (.preamble offset []) worker)
    (node : Node method.bytes offset (.ordinary method.operation.instruction))
    (ret : Node method.bytes (offset + method.operation.length) (.ordinary (.legacy .ret)))
    (extent : offset + method.operation.length + 1 = method.bytes.length) (af : Bool) :
    Nonempty (Advance method tid state (.preamble offset []) af) := by
  rcases method with ⟨bytes, operation, base, entry, entryFlags, resources, reference,
    returnAddress, initialQueue, size, codeNoWrap, originalRsp, returnCanonical, stackNoWrap⟩
  cases operation with
  | load address =>
    let method : Method := ⟨bytes, .load address, base, entry, entryFlags, resources, reference,
      returnAddress, initialQueue, size, codeNoWrap, originalRsp, returnCanonical, stackNoWrap⟩
    change Current method state at current
    change At method (.preamble offset []) worker at located
    change Nonempty (Advance method tid state (.preamble offset []) af)
    have fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region := by
      rw [located.resources]
      exact current.fits
    have selected := current.preamble_selected located
    obtain ⟨value, after, actual, effect, _, loaded, source, frame⟩ :=
      ManagedAccess.issue_loadMem64 (reference := reference) node size current.valid live
        located.location.1 current.code fits located.location.2.1 selected af
    have fetched := (current.decode_node live located.resources node located.location.2.1).1
    have origin : AccessOrigin method tid state (.issue tid af)
        (install state tid state.world after, .ordinary tid) value := by
      refine ⟨⟨af, worker, rfl, live, actual, rfl, located.resources,
        located.location.2.2.1, located.queue.counter, located.preamble_address,
        selected, fetched, effect, loaded, source⟩⟩
    refine ⟨⟨_, .ret (offset + method.operation.length) value, after, some value,
      actual, install_self live _ _, ?_, rfl, rfl, Capture.some origin, rfl⟩⟩
    refine ⟨frame.resources.trans located.resources, frame.flags.trans located.flags, ?_,
      frame.phase.trans located.location.1, ?_, ?_, ret, extent⟩
    · change QueueFrame initialQueue ⟨after.pending, after.nextStore⟩
      rw [frame.pending, frame.nextStore]
      exact located.queue
    · exact frame.rip.trans (advance_pc located.location.2.1)
    · rw [frame.context]
      change written worker.context.registers .rax value = written entry .rax value
      exact congrArg (fun registers => written registers .rax value) located.location.2.2.1
  | store address sourceRegister =>
    let method : Method := ⟨bytes, .store address sourceRegister, base, entry, entryFlags,
      resources, reference, returnAddress, initialQueue, size, codeNoWrap, originalRsp,
      returnCanonical, stackNoWrap⟩
    change Current method state at current
    change At method (.preamble offset []) worker at located
    change Nonempty (Advance method tid state (.preamble offset []) af)
    have fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region := by
      rw [located.resources]
      exact current.fits
    have selected := current.preamble_selected located
    obtain ⟨after, actual, effect, queue, _, frame⟩ :=
      ManagedAccess.issue_storeMem64 (reference := reference) node size current.valid live
        located.location.1 current.code fits located.location.2.1 selected af
    have fetched := (current.decode_node live located.resources node located.location.2.1).1
    have originalSource : worker.context.registers sourceRegister = entry sourceRegister :=
      congrFun located.location.2.2.1 sourceRegister
    have originalCounter : worker.nextStore = initialQueue.nextStore := located.queue.counter
    have origin : AccessOrigin method tid state (.issue tid af)
        (install state tid state.world after, .ordinary tid) PUnit.unit := by
      refine ⟨⟨af, worker, rfl, live, actual, rfl, located.resources,
        located.location.2.2.1, originalCounter, located.preamble_address,
        selected, fetched, effect, originalSource, originalCounter, ?_⟩⟩
      simpa only [originalSource, originalCounter] using queue
    refine ⟨⟨_, .ret (offset + method.operation.length) PUnit.unit, after, some PUnit.unit,
      actual, install_self live _ _, ?_, rfl, rfl, Capture.some origin, rfl⟩⟩
    refine ⟨frame.resources.trans located.resources, frame.flags.trans located.flags, ?_,
      frame.phase.trans located.location.1, ?_, ?_, ret, extent⟩
    · have appended := located.queue.enqueueManaged reference (entry sourceRegister)
      change QueueFrame (initialQueue.enqueueManaged reference (entry sourceRegister))
        ⟨after.pending, after.nextStore⟩
      rw [frame.pending, frame.nextStore, originalSource]
      exact appended
    · exact frame.rip.trans (advance_pc located.location.2.1)
    · exact frame.registers.trans located.location.2.2.1

/-- Construct a successful actual issue from the present independent contract,
for arbitrary AF, at every unfinished cutpoint. Initial mixed queues and any
number of previous head drains are admitted by QueueFrame and current WF. -/
theorem advance {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (unfinished : point.remaining ≠ 0) (af : Bool) :
    Nonempty (Advance method tid state point af) := by
  have fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩
      worker.resources.code.loan.region := by
    rw [located.resources]
    exact current.fits
  cases point with
  | preamble offset padding =>
    obtain ⟨running, pc, registers, shape⟩ := located.location
    cases shape with
    | @body offset node ret extent =>
      exact advance_access current live located node ret extent af
    | @pad offset padding rest node tail =>
      let output : X86.State := { localCPU state worker with
        rip := worker.context.rip + BitVec.ofNat 64 padding.instruction.length }
      let after : Worker := { worker with context := .ofCPU output }
      have executed : Sequential.execute (localCPU state worker) padding.instruction af =
          .ok ⟨.next output, []⟩ := padding_execute _ _ _
      have admitted : supported padding.instruction = true := by cases padding <;> rfl
      have reads : ∃ units, (padding.instruction.operandReads (localCPU state worker)).mapM
          (fun read => checkRead state worker read .sharedCell) = .ok units := by
        refine ⟨[], ?_⟩
        cases padding <;> rfl
      have queue : QueueEffect state worker padding.instruction
          ⟨worker.pending, worker.nextStore⟩ .sharedCell :=
        .unchanged (by cases padding <;> rfl)
      have finish : FinishEffect state tid worker worker.pending ⟨.next output, []⟩
          (install state tid state.world after, .ordinary tid) worker.nextStore := .next rfl
      have actual := ManagedRules.step_ordinary node method.size current.valid live running
        current.code fits pc admitted reads queue executed finish
      have fetched := (current.decode_node live located.resources node pc).1
      have absent : ¬ OwnAccess tid state (.issue tid af) := by
        rw [ownAccess_iff live fetched]
        exact padding_no_access padding
      refine ⟨⟨_, .preamble (offset + padding.instruction.length) rest, after, none,
        actual, install_self live _ _, ?_, ?_, rfl, Capture.none absent, rfl⟩⟩
      · refine ⟨located.resources, located.flags, located.queue, running, ?_, registers, tail⟩
        change worker.context.rip + BitVec.ofNat 64 padding.instruction.length = _
        exact advance_pc pc
      · simp only [Point.remaining, List.length_cons]
  | ret offset reply =>
    obtain ⟨running, pc, registers, node, _⟩ := located.location
    have stack : worker.context.registers .rsp = worker.resources.callerAddress := by
      rw [located.resources]
      exact located.ret_rsp
    have caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
        worker.resources.caller.identifier worker.resources.callerAddress = .ok method.returnAddress := by
      rw [located.resources]
      exact current.caller
    have actual := ManagedReturn.step_ret node method.size current.valid live running current.code
      fits pc stack caller method.returnCanonical af
    have fetched := (current.decode_node live located.resources node pc).1
    have absent : ¬ OwnAccess tid state (.issue tid af) := by
      rw [ownAccess_iff live fetched]
      exact ret_no_access
    refine ⟨⟨_, .done reply, ManagedReturn.returnedWorker worker method.returnAddress, none,
      actual, install_self live _ _, ?_, rfl, rfl, Capture.none absent, rfl⟩⟩
    refine ⟨located.resources, located.flags, located.queue, rfl, rfl, ?_⟩
    change written worker.context.registers .rsp (worker.context.registers .rsp + 8) = _
    rw [registers]
    change written (method.responded reply) .rsp
      (method.operation.registers method.entry reply .rsp + 8) = _
    rw [method.operation.registers_rsp]
  | done reply => exact False.elim (unfinished rfl)

theorem At.zero_returned {method : Method} {point : Point method.operation} {worker : Worker}
    (located : At method point worker) (zero : point.remaining = 0) : worker.phase = .returned := by
  cases point with
  | preamble offset padding => simp [Point.remaining] at zero
  | ret offset reply => cases zero
  | done reply => exact located.location.1

theorem At.returned_done {method : Method} {point : Point method.operation} {worker : Worker}
    (located : At method point worker) (returned : worker.phase = .returned) :
    ∃ reply, point = .done reply := by
  cases point with
  | done reply => exact ⟨reply, rfl⟩
  | preamble offset padding | ret offset reply =>
    have running := located.location.1
    rw [returned] at running
    cases running

private theorem no_peer_access {tid : Nat} {state : OS.TSO64.State}
    {action : Action}
    (different : tid ≠ (match action with | .issue thread _ | .drain thread => thread)) :
    ¬ OwnAccess tid state action := by
  rintro ⟨af, _, _, rfl, _⟩
  exact different rfl

private theorem no_drain_access (tid thread : Nat) (state : OS.TSO64.State) :
    ¬ OwnAccess tid state (.drain thread) := by
  rintro ⟨_, _, _, impossible, _⟩
  cases impossible

/-- Closure under every actual successful sharedCell step. An own issue is
identified with the constructive advance by determinism. An own drain removes
only the actual head and retains the counter, all registers, flags and phase. -/
theorem step_preserves {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    {action : Action} {result : OS.TSO64.State × Observation}
    (success : OS.TSO64.step state action .sharedCell = .ok result) :
    ∃ next after emitted, result.1.workers[tid]? = some after ∧ At method next after ∧
      next.remaining + ownIssue tid action = point.remaining ∧
      point.replies ++ emitted.toList = next.replies ∧
      Capture method tid state action result emitted := by
  cases action with
  | issue thread af =>
    by_cases same : thread = tid
    · subst thread
      have unfinished : point.remaining ≠ 0 := by
        intro zero
        have returned := located.zero_returned zero
        simp [OS.TSO64.step, issue, live, returned] at success
      obtain ⟨advanced⟩ := advance current live located unfinished af
      have equal : advanced.result = result := Except.ok.inj (advanced.actual.symm.trans success)
      subst result
      exact ⟨advanced.next, advanced.worker, advanced.emitted, advanced.live, advanced.located,
        by simpa [AtomicMethods.ownIssue] using advanced.progress,
        advanced.replies, advanced.capture⟩
    · have different : tid ≠ thread := Ne.symm same
      exact ⟨point, worker, none, (step_peer success different).trans live, located,
        by simp [AtomicMethods.ownIssue, same], by simp,
        Capture.none (no_peer_access different)⟩
  | drain thread =>
    by_cases same : thread = tid
    · subst thread
      obtain ⟨issuing, head, tail, output, issuingLive, pending, _, _, resultEq⟩ :=
        drain_effect (profile := .sharedCell) success
      have equal : issuing = worker := Option.some.inj (issuingLive.symm.trans live)
      subst issuing
      rw [resultEq]
      refine ⟨point, { worker with pending := tail }, none, install_self live _ _, ?_,
        by simp [AtomicMethods.ownIssue], by simp,
        Capture.none (no_drain_access tid tid state)⟩
      refine ⟨located.resources, located.flags, ?_, ?_⟩
      · simpa only [Queue.Cursor.dropHead, pending, List.tail_cons] using located.queue.dropHead
      · cases point <;> exact located.location
    · have different : tid ≠ thread := Ne.symm same
      exact ⟨point, worker, none, (step_peer success different).trans live, located,
        by simp [AtomicMethods.ownIssue], by simp,
        Capture.none (no_drain_access tid thread state)⟩

/-- A proof annotation of the actual schedule, with exactly one optional reply
per action. It is not another interpreter: each constructor contains the real
step and Capture's independent dispatch-coverage contract. -/
inductive AccessTrace (method : Method) (tid : Nat) :
    OS.TSO64.State → List Action → (OS.TSO64.State × List Observation) →
      List (Option method.operation.Reply) → Prop where
  | nil (state : OS.TSO64.State) : AccessTrace method tid state [] (state, []) []
  | cons {state : OS.TSO64.State} {action : Action}
      {first : OS.TSO64.State × Observation} {rest : List Action}
      {result : OS.TSO64.State × List Observation}
      {emitted : Option method.operation.Reply} {emissions : List (Option method.operation.Reply)}
      (actual : OS.TSO64.step state action .sharedCell = .ok first)
      (capture : Capture method tid state action first emitted)
      (tail : AccessTrace method tid first.1 rest result emissions) :
      AccessTrace method tid state (action :: rest)
        (result.1, first.2 :: result.2) (emitted :: emissions)

theorem AccessTrace.scheduled {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {emissions : List (Option method.operation.Reply)}
    (trace : AccessTrace method tid state actions result emissions) :
    schedule state actions .sharedCell = .ok result := by
  induction trace with
  | nil => rfl
  | cons actual capture tail ih =>
    simp only [schedule, actual, ok_bind, ih, pure_ok]

theorem AccessTrace.length {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {emissions : List (Option method.operation.Reply)}
    (trace : AccessTrace method tid state actions result emissions) :
    emissions.length = actions.length := by
  induction trace with
  | nil => rfl
  | cons actual capture tail ih => exact congrArg Nat.succ ih

/-- At a supplied annotation position expose the same-run production prefix,
action, observation and capture. Thus intervening drains keep their actual
positions, even when two accesses happen to have equal values. -/
theorem AccessTrace.at {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {emissions : List (Option method.operation.Reply)}
    (trace : AccessTrace method tid state actions result emissions)
    {index : Nat} {emitted : Option method.operation.Reply}
    (found : emissions[index]? = some emitted) :
    ∃ before action first,
      schedule state (actions.take index) .sharedCell = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧ result.2[index]? = some first.2 ∧
      OS.TSO64.step before action .sharedCell = .ok first ∧
      Capture method tid before action first emitted := by
  induction trace generalizing index with
  | nil => simp at found
  | @cons state action first rest result head emissions actual capture tail ih =>
    cases index with
    | zero =>
      have same : head = emitted := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using found
      subst emitted
      exact ⟨state, action, first, rfl, rfl, rfl, actual, capture⟩
    | succ index =>
      have nextFound : emissions[index]? = some emitted := by
        simpa only [List.getElem?_cons_succ] using found
      obtain ⟨before, selectedAction, next, prefixRun, actionAt, observationAt, executed, captured⟩ :=
        ih nextFound
      refine ⟨before, selectedAction, next, ?_, ?_, ?_, executed, captured⟩
      · simp only [List.take_succ_cons, schedule, actual, ok_bind, prefixRun, pure_ok]
      · simpa only [List.getElem?_cons_succ] using actionAt
      · simpa only [List.getElem?_cons_succ] using observationAt

/-- Same-run origin at an original action index, including the actual local
load/source or exact store QueueEffect. No source-history labels are assumed. -/
def AccessAt (method : Method) (tid : Nat) (state : OS.TSO64.State) (actions : List Action)
    (result : OS.TSO64.State × List Observation) (index : Nat)
    (reply : method.operation.Reply) : Prop :=
  ∃ before action first,
    schedule state (actions.take index) .sharedCell = .ok (before, result.2.take index) ∧
    actions[index]? = some action ∧ result.2[index]? = some first.2 ∧
    OS.TSO64.step before action .sharedCell = .ok first ∧
    AccessOrigin method tid before action first reply

/-- A weaker independently recognized actual access position, without a
chosen reply, input-register assertion or supplied postcondition. -/
def DispatchedAt (tid : Nat) (state : OS.TSO64.State) (actions : List Action)
    (result : OS.TSO64.State × List Observation) (index : Nat) : Prop :=
  ∃ before action first,
    schedule state (actions.take index) .sharedCell = .ok (before, result.2.take index) ∧
    actions[index]? = some action ∧ OS.TSO64.step before action .sharedCell = .ok first ∧
    OwnAccess tid before action

theorem AccessAt.dispatched {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation} {index : Nat}
    {reply : method.operation.Reply} (origin : AccessAt method tid state actions result index reply) :
    DispatchedAt tid state actions result index := by
  obtain ⟨before, action, first, prefixRun, selected, _, actual, access⟩ := origin
  exact ⟨before, action, first, prefixRun, selected, actual, access.dispatched⟩

theorem AccessTrace.origin_at {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {emissions : List (Option method.operation.Reply)}
    (trace : AccessTrace method tid state actions result emissions)
    {index : Nat} {reply : method.operation.Reply}
    (found : emissions[index]? = some (some reply)) :
    AccessAt method tid state actions result index reply := by
  obtain ⟨before, action, first, prefixRun, selected, observed, actual, captured⟩ := trace.at found
  exact ⟨before, action, first, prefixRun, selected, observed, actual, captured.sound reply rfl⟩

/-- Every independently recognized own access at a supplied action position
is captured. Determinism identifies the supplied prefix and step with the
annotated production run, without supplying an intermediate At assertion. -/
theorem AccessTrace.coverage_at {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {emissions : List (Option method.operation.Reply)}
    (trace : AccessTrace method tid state actions result emissions) {index : Nat}
    (dispatched : DispatchedAt tid state actions result index) :
    ∃ reply, emissions[index]? = some (some reply) ∧
      AccessAt method tid state actions result index reply := by
  obtain ⟨before, action, first, prefixRun, selected, actual, own⟩ := dispatched
  have bound : index < emissions.length := by
    rw [trace.length]
    exact (List.getElem_of_getElem? selected).1
  have found : emissions[index]? = some emissions[index] := List.getElem?_eq_getElem bound
  obtain ⟨capturedBefore, capturedAction, capturedFirst, capturedPrefix, capturedSelected,
    _, capturedActual, captured⟩ := trace.at found
  have sameBefore : capturedBefore = before :=
    congrArg Prod.fst (Except.ok.inj (capturedPrefix.symm.trans prefixRun))
  have sameAction : capturedAction = action := Option.some.inj (capturedSelected.symm.trans selected)
  subst capturedBefore
  subst capturedAction
  have sameFirst : capturedFirst = first := Except.ok.inj (capturedActual.symm.trans actual)
  subst capturedFirst
  have present := captured.complete.mp own
  cases emittedEq : emissions[index] with
  | none => simp only [emittedEq, Option.isSome_none, Bool.false_eq_true] at present
  | some reply =>
    have atIndex : emissions[index]? = some (some reply) := by rw [emittedEq] at found; exact found
    exact ⟨reply, atIndex, trace.origin_at atIndex⟩

private theorem filterMap_cons {α : Type _} {head : Option α} {tail : List (Option α)} :
    (head :: tail).filterMap id = head.toList ++ tail.filterMap id := by
  cases head <;> rfl

/-- Arbitrary successful finite sharedCell interleavings preserve the complete
cutpoint contract, the exact remaining own-instruction count, and a complete
annotation of actual own accesses. Current carries the original caller read. -/
theorem schedule_preserves {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result) :
    Current method result.1 ∧ ∃ next after emissions,
      result.1.workers[tid]? = some after ∧ At method next after ∧
      next.remaining + ownIssues tid actions = point.remaining ∧
      point.replies ++ emissions.filterMap id = next.replies ∧
      AccessTrace method tid state actions result emissions := by
  induction actions generalizing state point worker result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact ⟨current, point, worker, [], live, located, rfl,
      by simp, .nil state⟩
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok success
    obtain ⟨middle, middleWorker, emitted, middleLive, middleAt, progress, replies, captured⟩ :=
      step_preserves current live located first
    obtain ⟨finalCurrent, final, after, emissions, finalLive, finalAt, tailProgress,
      tailReplies, trace⟩ := ih (current.step first) middleLive middleAt following
    rw [same]
    refine ⟨finalCurrent, final, after, emitted :: emissions, finalLive, finalAt, ?_, ?_,
      .cons first captured trace⟩
    · simp only [AtomicMethods.ownIssues]
      omega
    · rw [filterMap_cons, ← List.append_assoc, replies]
      exact tailReplies

/-- Enabledness is derived from the current code/resources, not an assumption
about a future successful action. It does not assert scheduler fairness. -/
theorem enabled {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (unfinished : point.remaining ≠ 0) (af : Bool) :
    ∃ result, OS.TSO64.step state (.issue tid af) .sharedCell = .ok result ∧ result.2.retired = 1 := by
  obtain ⟨advanced⟩ := advance current live located unfinished af
  exact ⟨advanced.result, advanced.actual, advanced.retired⟩

/-- From every current cutpoint construct a completion containing exactly the
remaining number of own issues, with arbitrary AF at each instruction. No
drain or empty-FIFO requirement is inserted to make RET or access succeed. -/
theorem complete {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {worker : Worker} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (choices : Nat → Bool) :
    ∃ actions result after reply,
      actions = (List.range point.remaining).map (fun index => .issue tid (choices index)) ∧
      actions.length = point.remaining ∧
      (∀ action ∈ actions, ∃ af, action = .issue tid af) ∧
      schedule state actions .sharedCell = .ok result ∧
      result.1.workers[tid]? = some after ∧ At method (.done reply) after := by
  have termination : ∀ count state (point : Point method.operation) worker,
      point.remaining = count → Current method state → state.workers[tid]? = some worker →
      At method point worker → ∀ choices : Nat → Bool, ∃ actions result after reply,
        actions = (List.range count).map (fun index => .issue tid (choices index)) ∧
        actions.length = count ∧ (∀ action ∈ actions, ∃ af, action = .issue tid af) ∧
        schedule state actions .sharedCell = .ok result ∧
        result.1.workers[tid]? = some after ∧ At method (.done reply) after := by
    intro count
    induction count with
    | zero =>
      intro state point worker zero current live located choices
      cases point with
      | preamble offset padding => simp [Point.remaining] at zero
      | ret offset reply => cases zero
      | done reply => exact ⟨[], (state, []), worker, reply, rfl, rfl, by simp, rfl, live, located⟩
    | succ count ih =>
      intro state point worker remaining current live located choices
      have unfinished : point.remaining ≠ 0 := by omega
      obtain ⟨advanced⟩ := advance current live located unfinished (choices 0)
      have nextCount : advanced.next.remaining = count := by have := advanced.progress; omega
      obtain ⟨actions, result, after, reply, plan, length, own, scheduled, finalLive, finalAt⟩ :=
        ih advanced.result.1 advanced.next advanced.worker nextCount
          (current.step advanced.actual) advanced.live advanced.located
          (fun index => choices (index + 1))
      refine ⟨.issue tid (choices 0) :: actions, (result.1, advanced.result.2 :: result.2), after,
        reply, ?_, by simp [length], ?_, ?_, finalLive, finalAt⟩
      · rw [plan, List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Function.comp_def]
      · intro action member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨choices 0, rfl⟩
        · exact own action later
      · simp only [schedule, advanced.actual, ok_bind, scheduled, pure_ok]
  exact termination point.remaining state point worker rfl current live located choices

/-- Independent return/body postcondition. Pending stores may have drained;
the exact allocation counter and FIFO suffix are retained, not emptiness. -/
structure BodyPost (method : Method) (worker : Worker) (reply : method.operation.Reply) : Prop where
  phase : worker.phase = .returned
  resources : worker.resources = method.resources
  flags : worker.context.flags = method.entryFlags
  rip : worker.context.rip = method.returnAddress
  registers : worker.context.registers =
    written (method.responded reply) .rsp (method.entry .rsp + 8)
  rsp : worker.context.registers .rsp = method.entry .rsp + 8
  rax : worker.context.registers .rax = method.responded reply .rax
  queue : QueueFrame (method.queueAfter method.initialQueue) ⟨worker.pending, worker.nextStore⟩

theorem At.done_post {method : Method} {worker : Worker} {reply : method.operation.Reply}
    (located : At method (.done reply) worker) : BodyPost method worker reply := by
  refine ⟨located.location.1, located.resources, located.flags, located.location.2.1,
    located.location.2.2, ?_, ?_, located.queue⟩
  · rw [located.location.2.2]
    exact written_same _ _ _
  · rw [located.location.2.2]
    exact written_other _ .rsp _ .rax (by decide)

private theorem single_reply_position {α : Type _} {emissions : List (Option α)} {reply : α}
    (single : emissions.filterMap id = [reply]) :
    ∃ index : Nat, emissions[index]? = some (some reply) ∧
      ∀ (other : Nat) (value : α), emissions[other]? = some (some value) → other = index ∧ value = reply := by
  revert single
  induction emissions with
  | nil => intro single; simp at single
  | cons head tail ih =>
    intro single
    cases head with
    | none =>
      have tailSingle : tail.filterMap id = [reply] := single
      obtain ⟨index, found, unique⟩ := ih tailSingle
      refine ⟨index + 1, ?_, ?_⟩
      · simpa only [List.getElem?_cons_succ] using found
      · intro other value selected
        cases other with
        | zero => cases selected
        | succ other =>
          obtain ⟨sameIndex, sameValue⟩ := unique other value selected
          exact ⟨congrArg Nat.succ sameIndex, sameValue⟩
    | some value =>
      have parts : value = reply ∧ tail.filterMap id = [] := List.cons.inj single
      obtain ⟨rfl, empty⟩ := parts
      refine ⟨0, rfl, ?_⟩
      intro other value selected
      cases other with
      | zero =>
        exact ⟨rfl, (Option.some.inj (Option.some.inj selected)).symm⟩
      | succ other =>
        have member : value ∈ tail.filterMap id :=
          List.mem_filterMap.mpr ⟨some value, List.mem_of_getElem? selected, rfl⟩
        rw [empty] at member
        cases member

/-- Exactly one actual own access at one original action position, together
with its actual value origin. Uniqueness covers independently recognized
dispatches, not just the annotations or equality of their returned words. -/
def OneAccess (method : Method) (tid : Nat) (state : OS.TSO64.State) (actions : List Action)
    (result : OS.TSO64.State × List Observation) (reply : method.operation.Reply) : Prop :=
  ∃ index, AccessAt method tid state actions result index reply ∧
    ∀ other, DispatchedAt tid state actions result other → other = index

/-- Recover the retained response's actual origin at a supplied independently
recognized access position, including all intervening peer/drain actions. -/
theorem OneAccess.at {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {reply : method.operation.Reply} (one : OneAccess method tid state actions result reply)
    {index : Nat} (dispatched : DispatchedAt tid state actions result index) :
    AccessAt method tid state actions result index reply := by
  obtain ⟨position, origin, unique⟩ := one
  have same : index = position := unique index dispatched
  simpa only [same] using origin

theorem AccessTrace.one_access {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {emissions : List (Option method.operation.Reply)}
    (trace : AccessTrace method tid state actions result emissions) {reply : method.operation.Reply}
    (single : emissions.filterMap id = [reply]) : OneAccess method tid state actions result reply := by
  obtain ⟨index, found, unique⟩ := single_reply_position single
  refine ⟨index, trace.origin_at found, ?_⟩
  intro other dispatched
  obtain ⟨value, selected, _⟩ := trace.coverage_at dispatched
  exact (unique other value selected).1

/-- Every completed actual interleaving has the independent full body result,
exactly padding.length+2 own instructions, and exactly one actual own access.
The load's retained reply comes from that access's actual local read/source;
the store's occurrence/value/reference come from its real QueueEffect. Neither
a desired final At nor a proposed history is a premise. The current original
caller read and code survive to the final state. -/
theorem all_completed {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {padding : List Padding} {initial : Worker} (current : Current method state)
    (live : state.workers[tid]? = some initial) (entry : At method (.preamble 0 padding) initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result) {final : Worker}
    (finalLive : result.1.workers[tid]? = some final) (returned : final.phase = .returned) :
    Current method result.1 ∧ ∃ reply,
      BodyPost method final reply ∧ OneAccess method tid state actions result reply ∧
      ownIssues tid actions = padding.length + 2 ∧
      OS.TSO64.Return.returnValue (result.1, .returned tid) =
        some (tid, method.responded reply .rax) := by
  obtain ⟨finalCurrent, point, after, emissions, afterLive, located, progress, replies, trace⟩ :=
    schedule_preserves current live entry success
  have equal : after = final := Option.some.inj (afterLive.symm.trans finalLive)
  subst after
  obtain ⟨reply, rfl⟩ := located.returned_done returned
  have single : emissions.filterMap id = [reply] := by
    simpa only [Point.replies, List.nil_append] using replies
  exact ⟨finalCurrent, reply, located.done_post, trace.one_access single,
    by simpa only [Point.remaining, Nat.zero_add] using progress,
    At.done_returnValue finalLive located⟩

/-- A successful finite interleaving that has used the available own-issue
budget has already returned. This permits arbitrary peer actions and own
drains, and makes no quiescence or scheduling-fairness claim. -/
theorem enough_own_issues {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {point : Point method.operation} {initial : Worker} (current : Current method state)
    (live : state.workers[tid]? = some initial) (entry : At method point initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions .sharedCell = .ok result)
    (enough : point.remaining ≤ ownIssues tid actions) :
    ∃ final reply, result.1.workers[tid]? = some final ∧
      At method (.done reply) final ∧ BodyPost method final reply := by
  obtain ⟨_, next, final, _, finalLive, located, progress, _, _⟩ :=
    schedule_preserves current live entry success
  have zero : next.remaining = 0 := by omega
  obtain ⟨reply, nextEq⟩ := located.returned_done (located.zero_returned zero)
  subst next
  exact ⟨final, reply, finalLive, located, located.done_post⟩

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
