/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ScalarCall64
import EDSL.OS.TSO64.Return
import EDSL.OS.TSO64.EffectSimulation.Mixed.EventCounts
import EDSL.OS.TSO64.EffectSimulation.Mixed.ChoiceTrace
import Init.Data.List.FinRange
import EDSL.Audit

/-!
Independent behavioral contracts for closed batches of counted void calls.
A candidate must separately supply a proof of Claim for its exact image.

One entry context represents one invocation of the same complete callable
image. Its low32 RSI requests that many full64 unit RMWs of the common cell;
peer increments may occur between any two of its own increments. Chronology
belongs to those individual RMWs, with the actual call's RET strictly later.

The first model fixes ownedOnly/arithmetic execution, protected original
code/callers, an unchanging finite worker population and empty FIFOs. Present
admission is independent of proof annotations and future behavior. Candidate
proofs must separately establish every safety, return, history and progress
obligation below. Suffix bounds and arbitrary-trace own-progress bounds have
different quantifiers and neither is assumed by admission.

The represented model assumes coherent scalar ordinary RAM, the documented
full64 address/alignment profile, stable translations without hidden aliases,
long mode/CET-off, represented CPU feature state and resource-mediated access.
These definitions supply no physical CPU/OS, native lifetime, source/compiler,
minimum-operation, fairness or wall-clock termination guarantee.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Grading.ConcurrentTask.Counted64
open X86 OS OS.TSO64 Concurrency

abbrev Image := ScalarCall64.Image
abbrev Requests (before : TSO64.State) := Fin before.workers.length → BitVec 32

/-- Only current entry facts. ResourcesValid retains original code/caller
loan descriptors and every listed grant/atomic handle. atomicFor binds the
first current authorized match in the actual ordered handle list. -/
structure Entry (image : Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (count : BitVec 32) (before : TSO64.State) (worker : Worker) : Prop where
  running : worker.phase = .running
  pc : worker.context.rip = image.base
  pointer : (PureCall.Argument.word64 cell.address).Holds (worker.context.registers .rdi)
  request : (PureCall.Argument.low32 count).Holds (worker.context.registers .rsi)
  resources : ResourcesValid before.world worker.resources
  nonempty : 0 < image.bytes.length
  baseCanonical : canonical image.base = true
  code : CodeAt (published before.world) image.base image.bytes
  fits : Borrowing.Subregion ⟨image.base, image.bytes.length⟩ worker.resources.code.loan.region
  originalRsp : worker.context.registers .rsp = worker.resources.callerAddress
  scalar : ScalarCall64.Entry worker
  selected : ∃ identifier handle,
    atomicFor before.world worker.resources cell.address = some (identifier, handle, cell) ∧
      handle.cell = target
  caller : ∃ continuation,
    Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok continuation ∧
      canonical continuation = true

/-- Closed actual slots, not an arbitrary caller-supplied tid enumeration.
Zero/max uint32 requests, arbitrary upper RSI and arbitrary nextStore counters
remain admitted. Actor principals need not equal tids or be pairwise distinct.
The live target is required even for an empty worker list. -/
structure Pre (image : Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (before : TSO64.State) (requests : Requests before) : Prop where
  valid : WellFormed before .ownedOnly
  empty : Quiescent before
  liveTarget : before.world.cells target = some cell
  validCell : Atomics64.ValidCell before.world.legacy.shared cell
  entries : ∀ slot : Fin before.workers.length,
    ∃ worker, before.workers[slot.val]? = some worker ∧
      Entry image target cell (requests slot) before worker
  privateCallers : ∀ (i j : Fin before.workers.length) first second,
    i ≠ j → before.workers[i.val]? = some first → before.workers[j.val]? = some second →
      Ownership.Disjoint first.resources.caller.loan.region second.resources.caller.loan.region
  codeCallerSeparation : ∀ (slot : Fin before.workers.length) worker,
    before.workers[slot.val]? = some worker →
      Ownership.Disjoint ⟨image.base, image.bytes.length⟩ worker.resources.caller.loan.region

/-- Sum in Nat; reduction occurs only at the final full64 word. -/
def requestedTotal {before : TSO64.State} (requests : Requests before) : Nat :=
  ((List.finRange before.workers.length).map fun slot => (requests slot).toNat).sum

/-- Every RMW, without a target or expected-value filter. Internal point ids
are original observation indices; thread labels are actual scheduler tids.
The native event still lives at that index in the original observation list.
These mathematical point records do not treat a whole void call as fetch-add. -/
def incrementCalls (observations : List Observation) : List (ModuloCounter.Call 64 Nat Nat) :=
  observations.zipIdx.filterMap fun entry =>
    match entry.1 with
    | .rmw tid event => some (AtomicFetchAddHistory64.asCall entry.2 tid event)
    | _ => none

def ownPositions (tid : Nat) (observations : List Observation) : List Nat :=
  (incrementCalls observations).filterMap fun call =>
    if call.thread = tid then some call.id else none

/-- A boundary of this exact execution under the fixed profile and family.
The selected action and observation share the same original index. -/
structure StepAt (before : TSO64.State) (actions : List Action)
    (actual : TSO64.State × List Observation) (index : Nat) where
  prior : TSO64.State
  action : Action
  next : TSO64.State × Observation
  prefixRun : schedule before (actions.take index) .ownedOnly .arithmetic =
    .ok (prior, actual.2.take index)
  selected : actions[index]? = some action
  observed : actual.2[index]? = some next.2
  actualStep : TSO64.step prior action .ownedOnly .arithmetic = .ok next

/-- Narrow void return frame. The preserved flag mask is fixed here, not a
candidate choice. Arithmetic flags and caller-saved registers, including RAX,
have no required result. Collection observes the actual RAX without cleanup. -/
structure ReturnFrame (before after : TSO64.State) (tid : Nat)
    (initial final : Worker) : Prop where
  initialLive : before.workers[tid]? = some initial
  live : after.workers[tid]? = some final
  phase : final.phase = .returned
  empty : final.pending = []
  nextStore : final.nextStore = initial.nextStore
  resources : final.resources = initial.resources
  current : ResourcesValid after.world final.resources
  registers : ∀ register ∈ PureCall.calleeSaved,
    final.context.registers register = initial.context.registers register
  flags : final.context.flags &&& ~~~arithmeticFlagMask =
    initial.context.flags &&& ~~~arithmeticFlagMask
  stack : final.context.registers .rsp = initial.context.registers .rsp + 8
  stackCanonical : canonical (final.context.registers .rsp) = true
  direction : final.context.flags.getLsbD 10 = false
  returnCanonical : canonical final.context.rip = true
  continuation : ∃ address,
    Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
      initial.resources.caller.identifier initial.resources.callerAddress = .ok address ∧
      final.context.rip = address
  collection : collect after tid = .ok (final.context.registers .rax)

/-- Observations required at every successful finite prefix. No callee-saved
GPR is frozen while a call is running; its return must restore the ABI frame.
All actual RMW payloads are covered, including wrong-target or add-two events.
Empty queues and unchanged counters exclude ordinary buffered stores in this
first model. Full RAM cells outside the common qword remain byte-for-byte equal. -/
structure SafePrefix (image : Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (before : TSO64.State) (requests : Requests before)
    (actual : TSO64.State × List Observation) : Prop where
  valid : WellFormed actual.1 .ownedOnly
  stable : Stable before.world actual.1.world
  population : actual.1.workers.length = before.workers.length
  empty : Quiescent actual.1
  memory : ∀ address, ¬(AddressSpace.qwordRegion cell.address).Contains address →
    actual.1.world.legacy.shared.resources.space.cells address =
      before.world.legacy.shared.resources.space.cells address
  frames : ∀ (slot : Fin before.workers.length) (initial : Worker),
    before.workers[slot.val]? = some initial →
    ∃ (current : Worker) (identifier : Atomics64.HandleId64) (handle : Atomics64.Handle),
      actual.1.workers[slot.val]? = some current ∧
      current.resources = initial.resources ∧ ResourcesValid actual.1.world current.resources ∧
      current.nextStore = initial.nextStore ∧
      atomicFor before.world initial.resources cell.address = some (identifier, handle, cell) ∧
      atomicFor actual.1.world current.resources cell.address = some (identifier, handle, cell) ∧
      handle.cell = target ∧
      CodeAt (published actual.1.world) image.base image.bytes ∧
      current.context.flags &&& ~~~arithmeticFlagMask =
        initial.context.flags &&& ~~~arithmeticFlagMask ∧
      (∀ continuation,
        Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
          initial.resources.caller.identifier initial.resources.callerAddress = .ok continuation →
        Borrowing.loadWord64 actual.1.world.legacy.shared current.resources.actor
          current.resources.caller.identifier current.resources.callerAddress = .ok continuation) ∧
      (current.phase = .returned →
        ReturnFrame before actual.1 slot.val initial current ∧
        EffectSimulation.Mixed.Counts.countRMW slot.val actual.2 = (requests slot).toNat)
  increments : ∀ (index tid : Nat) (event : Atomics64.FetchAddEvent),
    actual.2[index]? = some (Observation.rmw tid event) →
    ∃ slot : Fin before.workers.length, slot.val = tid ∧
      ∃ (initial : Worker) (handle : Atomics64.Handle),
        before.workers[slot.val]? = some initial ∧ event.actor = initial.resources.actor ∧
        atomicFor before.world initial.resources cell.address = some (event.handle, handle, cell) ∧
        handle.cell = target ∧ event.cell = target ∧ event.arithmetic.event.address = cell.address ∧
        event.arithmetic.delta = 1 ∧
        ModuloCounter.Step event.arithmetic.event.before event.arithmetic.delta
          event.arithmetic.event.before event.arithmetic.event.after
  counts : ∀ slot : Fin before.workers.length,
    EffectSimulation.Mixed.Counts.countRMW slot.val actual.2 ≤ (requests slot).toNat
  retiring : ∀ seen ∈ actual.2, seen.retired = 1

/-- Exact own count, every own increment position before a unique actual RET,
and the original protected caller frame. A zero request still needs its RET.
The RET's RAX is merely the actual machine value, not a void-call reply. -/
structure Outcome (count : BitVec 32) (before : TSO64.State) (actions : List Action)
    (actual : TSO64.State × List Observation) (tid : Nat) where
  initial : Worker
  final : Worker
  countExact : EffectSimulation.Mixed.Counts.countRMW tid actual.2 = count.toNat
  returned : Nat
  responseBoundary : StepAt before actions actual returned
  responseObserved : responseBoundary.next.2 = .returned tid
  response : TSO64.Return.ReturnOrigin responseBoundary.prior responseBoundary.action
    responseBoundary.next tid (final.context.registers .rax) .ownedOnly .arithmetic
  uniqueResponse : ∀ index, actual.2[index]? = some (.returned tid) → index = returned
  beforeReturn : ∀ index ∈ ownPositions tid actual.2, index < returned
  frame : ReturnFrame before actual.1 tid initial final

/-- Complete same-run output. The chronological unit history has no supplied
serial permutation. Its old and final full64 words are actual current reads;
the final total uses the independent requests, not observed deltas as inputs.
Per-slot outcomes and exhaustive response coverage retain actual positions. -/
structure Post (image : Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (before : TSO64.State) (requests : Requests before) (actions : List Action)
    (actual : TSO64.State × List Observation) where
  scheduled : schedule before actions .ownedOnly .arithmetic = .ok actual
  safe : SafePrefix image target cell before requests actual
  finished : Finished actual.1
  outcomes : (slot : Fin before.workers.length) →
    Outcome (requests slot) before actions actual slot.val
  allReturns : ∀ index tid, actual.2[index]? = some (.returned tid) →
    ∃ slot : Fin before.workers.length, slot.val = tid ∧ (outcomes slot).returned = index
  old : Word
  current : Word
  oldWord : loadQWord (published before.world) cell.address = .ok old
  currentWord : loadQWord (published actual.1.world) cell.address = .ok current
  sequential : ModuloCounter.Sequential old (incrementCalls actual.2) current
  total : current.toNat = (old.toNat + requestedTotal requests) % 2^64

/-- Required candidate obligations, with no asserted implementation or proof.
Completion is existence of a finite chosen suffix after each successful cut;
its bound is chosen before all future AF functions/offsets, at that cut only.
The prior need not match choices. Only when it does is the whole trace chosen.

ownProgress is a separate, stronger obligation: one input-dependent positive
budget per actual slot must work for every successful finite trace and every
interleaving/AF choice from that entry. Reaching the budget requires return;
no successful trace may exceed it. Constructing one bounded suffix does not
prove this field. Neither field asserts that a scheduler gives a worker turns. -/
structure Claim (image : Image) : Prop where
  prefixes : ∀ (before : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (requests : Requests before),
    Pre image target cell before requests → ∀ actions actual,
    schedule before actions .ownedOnly .arithmetic = .ok actual →
    SafePrefix image target cell before requests actual
  completed : ∀ (before : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (requests : Requests before),
    Pre image target cell before requests → ∀ actions actual,
    schedule before actions .ownedOnly .arithmetic = .ok actual → Returned actual.1 →
    Nonempty (Post image target cell before requests actions actual)
  enabled : ∀ (before : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (requests : Requests before),
    Pre image target cell before requests → ∀ actions actual,
    schedule before actions .ownedOnly .arithmetic = .ok actual →
    ∀ (slot : Fin before.workers.length) (worker : Worker),
    actual.1.workers[slot.val]? = some worker → worker.phase = .running → ∀ af,
    ∃ next, TSO64.step actual.1 (.issue slot.val af) .ownedOnly .arithmetic = .ok next ∧
      next.2.retired = 1
  completion : ∀ (before : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (requests : Requests before),
    Pre image target cell before requests → ∀ prior actual,
    schedule before prior .ownedOnly .arithmetic = .ok actual →
    ∃ bound : Nat, ∀ (choices : Nat → Nat → Bool) (offset : Nat → Nat),
    ∃ suffix finished,
      EffectSimulation.Mixed.ChoiceTrace.ChosenFrom choices
        (fun tid => offset tid + EffectSimulation.Mixed.ChoiceTrace.issues tid prior) suffix ∧
      schedule actual.1 suffix .ownedOnly .arithmetic = .ok finished ∧
      Finished finished.1 ∧ suffix.length ≤ bound ∧
      schedule before (prior ++ suffix) .ownedOnly .arithmetic =
        .ok (finished.1, actual.2 ++ finished.2) ∧
      (EffectSimulation.Mixed.ChoiceTrace.ChosenFrom choices offset prior →
        EffectSimulation.Mixed.ChoiceTrace.ChosenFrom choices offset (prior ++ suffix)) ∧
      Nonempty (Post image target cell before requests (prior ++ suffix)
        (finished.1, actual.2 ++ finished.2))
  ownProgress : ∀ (before : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (requests : Requests before),
    Pre image target cell before requests →
    ∃ bounds : Fin before.workers.length → Nat,
      (∀ slot, 0 < bounds slot) ∧
      ∀ actions actual, schedule before actions .ownedOnly .arithmetic = .ok actual →
      ∀ slot : Fin before.workers.length,
        EffectSimulation.Mixed.ChoiceTrace.issues slot.val actions ≤ bounds slot ∧
        (bounds slot ≤ EffectSimulation.Mixed.ChoiceTrace.issues slot.val actions →
          ∃ worker, actual.1.workers[slot.val]? = some worker ∧
            worker.phase = .returned ∧ worker.pending = [])

end EDSL.Grading.ConcurrentTask.Counted64

#audit_edsl
