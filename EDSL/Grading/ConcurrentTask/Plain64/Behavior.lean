/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Safety
import EDSL.OS.TSO64.Return
import EDSL.X86.StoreBuffer.WholeQWord

/-!
Independent completed behavior of full64 acquire-load/release-store cohorts.
Every access and response names the original action and observation positions
of the same actual production schedule. Broad dispatch recognition includes
wrong operands/destinations and opposite operations, so coverage cannot hide an
unexpected MOV64 access. Replies come from the actual access, with exact local
FIFO/published read provenance or exact full-descriptor store allocation.

Scalar return framing, queue suffixes, counters, flags and saved registers are
independent observations. A store can return before publication. These are
completed-run output contracts, not admission, a whole-graph contract, a Claim,
a corpus certificate or a physical/source/compiler memory-model guarantee.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS OS.TSO64 Concurrency

/-- One original boundary of this exact run, never a replacement execution. -/
structure StepAt (before : TSO64.State) (actions : List Action)
    (actual : TSO64.State × List Observation) (index : Nat) where
  prior : TSO64.State
  action : Action
  next : TSO64.State × Observation
  prefixRun : schedule before (actions.take index) .sharedCell =
    .ok (prior, actual.2.take index)
  selected : actions[index]? = some action
  observed : actual.2[index]? = some next.2
  actualStep : TSO64.step prior action .sharedCell = .ok next

/-- Recognition deliberately does not require the expected address,
register choice or load/store direction of a candidate body. -/
def DataInstruction : Sequential.Instruction → Prop
  | .loadMem64 .. | .storeMem64 .. => True
  | _ => False

def DataAccessAt (before : TSO64.State) (actions : List Action)
    (actual : TSO64.State × List Observation) (tid index : Nat) : Prop :=
  ∃ boundary : StepAt before actions actual index,
    ∃ worker instruction af,
      boundary.action = .issue tid af ∧ boundary.prior.workers[tid]? = some worker ∧
      TSO64.decode (fetchCPU boundary.prior worker) = .ok (.ordinary instruction) ∧
      DataInstruction instruction

/-- The actual local load plus its literal newest whole-qword payload position,
or actual published fallback. A FIFO position is not a persistent writer ID;
nonempty incoming queues do not fabricate earlier issuing instructions. -/
def SelectedRead (state : TSO64.State) (worker : Worker) (address value : Word) : Prop :=
  loadQWord (localCPU state worker).memory address = .ok value ∧
  match StoreBuffer.Mixed.newestQWord (payload worker.pending) address with
  | some origin => origin.value = value ∧
      (payload worker.pending)[origin.index]? = some ⟨address, .qword value⟩
  | none => loadQWord (published state.world) address = .ok value

def DataEffect (input : Input) (initial worker : Worker) (reference : Queue.ManagedRef)
    (state : TSO64.State) (action : Action) (next : TSO64.State × Observation)
    (tid : Nat) (reply : input.Reply) : Prop :=
  match input with
  | .loadAcquire _ _ cell _ =>
      ∃ af, action = .issue tid af ∧
        OrdinaryEffect state tid worker (.loadMem64 .rax (.base .rdi)) af next .sharedCell ∧
        SelectedRead state worker cell.address reply ∧ next.1.world = state.world ∧
        ∃ after, next.1.workers[tid]? = some after ∧ after.pending = worker.pending ∧
          after.nextStore = worker.nextStore ∧ after.context.registers .rax = reply
  | .storeRelease _ _ _ value _ =>
      ∃ af, action = .issue tid af ∧ worker.context.registers .rsi = value ∧
        worker.nextStore = initial.nextStore ∧
        OrdinaryEffect state tid worker (.storeMem64 (.base .rdi) .rsi) af next .sharedCell ∧
        next.1.world = state.world ∧
        ∃ after, next.1.workers[tid]? = some after ∧
          after.pending = worker.pending ++ [.managed reference value initial.nextStore] ∧
          after.nextStore = initial.nextStore + 1

def replyRAX (input : Input) (initial : Worker) : input.Reply → Word :=
  match input with
  | .loadAcquire .. => fun reply => reply
  | .storeRelease .. => fun _ => initial.context.registers .rax

/-- Stronger call-specific return observations supplement the shared scalar
ABI frame. Every queue entry and actual allocation counter remains visible. -/
structure CallFrame (input : Input) (reply : input.Reply) (before after : TSO64.State)
    (tid : Nat) (initial final : Worker) (reference : Queue.ManagedRef) : Prop where
  abi : ScalarCall64.ReturnFrame before after tid initial final
  unclobbered : ∀ register, register ≠ .rsp →
    (input.site.kind = .loadAcquire → register ≠ .rax) →
    final.context.registers register = initial.context.registers register
  rax : final.context.registers .rax = replyRAX input initial reply
  queue : QueueFrame
    ⟨initial.pending ++ extra input reference initial, initial.nextStore + writes input⟩
    ⟨final.pending, final.nextStore⟩
  collectWhenEmpty : final.pending = [] →
    collect after tid = .ok (final.context.registers .rax)

/-- A derived same-run output. Logical occurrence labels and machine nextStore
allocation are distinct; a store reply is unit while machine RAX is preserved. -/
structure Outcome (input : Input) (before : TSO64.State) (actions : List Action)
    (actual : TSO64.State × List Observation) (tid : Nat) where
  initial : Worker
  initialLive : before.workers[tid]? = some initial
  final : Worker
  reference : Queue.ManagedRef
  target : reference.handle.cell = input.target
  descriptor : reference.cell = input.cell
  originalSelection : atomicFor before.world initial.resources input.cell.address =
    some (reference.identifier, reference.handle, reference.cell)
  reply : input.Reply
  performed : Nat
  returned : Nat
  accessBoundary : StepAt before actions actual performed
  accessing : Worker
  accessingLive : accessBoundary.prior.workers[tid]? = some accessing
  accessingResources : accessing.resources = initial.resources
  accessingArguments : Arguments input accessing
  accessingSelection : atomicFor accessBoundary.prior.world accessing.resources input.cell.address =
    some (reference.identifier, reference.handle, reference.cell)
  access : DataEffect input initial accessing reference accessBoundary.prior
    accessBoundary.action accessBoundary.next tid reply
  dispatched : DataAccessAt before actions actual tid performed
  uniqueAccess : ∀ index, DataAccessAt before actions actual tid index → index = performed
  responseBoundary : StepAt before actions actual returned
  response : TSO64.Return.ReturnOrigin responseBoundary.prior responseBoundary.action
    responseBoundary.next tid (replyRAX input initial reply) .sharedCell
  responseObserved : responseBoundary.next.2 = .returned tid
  uniqueResponse : ∀ index, actual.2[index]? = some (.returned tid) → index = returned
  beforeReturn : performed < returned
  frame : CallFrame input reply before actual.1 tid initial final reference

def Outcome.call {input : Input} {before : TSO64.State} {actions : List Action}
    {actual : TSO64.State × List Observation} {tid : Nat}
    (outcome : Outcome input before actions actual tid) : AtomicCalls.Call Atomics64.CellId64 Word :=
  ⟨tid, input.occurrence, input.request, outcome.reply, 0, outcome.performed, outcome.returned⟩

/-- One output per actual original slot, ordered by actual data-access position,
with exhaustive broad access and RET coverage for this exact run. -/
structure Post (before : TSO64.State) (inputs : Fin before.workers.length → Input)
    (actions : List Action) (actual : TSO64.State × List Observation) where
  scheduled : schedule before actions .sharedCell = .ok actual
  safe : SafePrefix before actual.1 inputs
  outcomes : (tid : Fin before.workers.length) → Outcome (inputs tid) before actions actual tid.val
  slots : List (Fin before.workers.length)
  permutation : slots.Perm (List.finRange before.workers.length)
  ordered : slots.Pairwise (fun i j => (outcomes i).performed < (outcomes j).performed)
  allReturns : ∀ tid index, actual.2[index]? = some (.returned tid) →
    ∃ slot, slot.val = tid ∧ (outcomes slot).returned = index
  allAccesses : ∀ tid index, DataAccessAt before actions actual tid index →
    ∃ slot, slot.val = tid ∧ (outcomes slot).performed = index
  noRMW : ∀ tid event, Observation.rmw tid event ∉ actual.2
  noBlocked : ∀ tid, Observation.blocked tid ∉ actual.2

def Post.calls {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    {actions : List Action} {actual : TSO64.State × List Observation}
    (post : Post before inputs actions actual) : List (AtomicCalls.Call Atomics64.CellId64 Word) :=
  post.slots.map fun tid => (post.outcomes tid).call

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
