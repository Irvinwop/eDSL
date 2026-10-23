/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import tests.Support.ExceptDecidable
import EDSL.OS.TSO64.Invariant
import EDSL.X86.CodeCheck
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Present-input preparation for an independent mixed blocking integration test.
All programs and resources are project-owned synthetic inputs. The nonempty
FIFO is an admitted initial boundary, with no asserted prior execution history.
No schedule, generated residual, future-success premise, or regression theorem
is supplied here. Successful admission establishes setup facts only.
-/

namespace EDSL.Tests.Support.MixedBlockingFixture
open X86 OS.TSO64
open scoped EDSL.Tests.Support

/-- Shared literal backing: LOCK INC [RDI]; RET; LOCK XADD [RDI],RSI; RET;
five NOP bytes. These words are memory input, never dispatch annotations. -/
def low : Word := 0x0f48f0c307ff48f0
def high : Word := 0x9090909090c337c1

def ownBytes : List Byte := [0xf0, 0x48, 0xff, 0x07, 0xc3]
def peerBytes : List Byte := [0xf0, 0x48, 0x0f, 0xc1, 0x37, 0xc3]
def firstStore : Store := ⟨131072, .qword 0x1122334455667788⟩
def secondStore : Store := ⟨131080, .qword 0x99aabbccddeeff00⟩
def ownContext : Context := TSO64.context 262144 131072 7 99
def peerContext : Context :=
  { TSO64.context 327680 196608 4 123 with rip := 393221 }

/-- A finite current-input check. Failure rejects setup; it is never interpreted
as a program defect. This helper is not used to decide WellFormed states. -/
private def require (condition : Prop) [Decidable condition] : Except Fault (PLift condition) :=
  if checked : condition then .ok ⟨checked⟩ else .error .resource

structure HandleView (world : World) (actor : Nat) (identifier : OS.Atomics64.HandleId64) where
  handle : OS.Atomics64.Handle
  cell : OS.Atomics64.Cell
  actual : OS.Atomics64.authorize world actor identifier = .ok (handle, cell)

def readHandle (world : World) (actor : Nat) (identifier : OS.Atomics64.HandleId64) :
    Except Fault (HandleView world actor identifier) :=
  match actual : OS.Atomics64.authorize world actor identifier with
  | .error fault => .error (.os fault)
  | .ok descriptor => .ok ⟨descriptor.1, descriptor.2, actual⟩

/-- Keep the real original fixture, original authorization and actual checked
issuance. No numeric handle ID is chosen by this setup. -/
structure Issued where
  ready : TSO64.Ready
  old : HandleView ready.checked.world 11 ready.atomicA
  checked : TSO64.Checked
  identifier : OS.Atomics64.HandleId64
  actual : TSO64.handle ready.checked old.handle.cell 11 = .ok (checked, identifier)

def issueOwn : Except Fault Issued := do
  let ready ← (TSO64.fixture low high 9).mapError Fault.os
  let old ← readHandle ready.checked.world 11 ready.atomicA
  match actual : TSO64.handle ready.checked old.handle.cell 11 with
  | .error fault => .error (.os fault)
  | .ok result => .ok ⟨ready, old, result.1, result.2, actual⟩

/-- Both original workers come from the production resource checker. The
following state is exactly the result of the two actual attach operations. -/
structure Workers (issued : Issued) where
  own : Worker
  peer : Worker
  ownMade : makeWorker issued.checked.world 11 ownContext
    issued.ready.codeA issued.ready.callerA [issued.ready.dataA]
    [issued.identifier, issued.ready.atomicA] = .ok own
  peerMade : makeWorker issued.checked.world 12 peerContext
    issued.ready.codeB issued.ready.callerB [issued.ready.dataB]
    [issued.ready.atomicB] = .ok peer

def Workers.state {issued : Issued} (workers : Workers issued) : OS.TSO64.State :=
  ⟨issued.checked.world, [workers.own, workers.peer]⟩

/-- Derive global validity through attach_valid_for rather than deciding a
proof-carrying scheduler state. -/
theorem Workers.valid {issued : Issued} (workers : Workers issued) :
    WellFormed workers.state .sharedCell := by
  let empty : OS.TSO64.State := ⟨issued.checked.world, []⟩
  let one : OS.TSO64.State := ⟨issued.checked.world, [workers.own]⟩
  have seed : WellFormed empty .sharedCell := ⟨issued.checked.valid, by simp [empty]⟩
  have first : attach empty 11 ownContext issued.ready.codeA issued.ready.callerA
      [issued.ready.dataA] [issued.identifier, issued.ready.atomicA] = .ok one := by
    simp only [attach, empty, one, workers.ownMade, ok_bind, pure_ok, List.nil_append]
  have second : attach one 12 peerContext issued.ready.codeB issued.ready.callerB
      [issued.ready.dataB] [issued.ready.atomicB] = .ok workers.state := by
    simp only [attach, one, Workers.state, workers.peerMade, ok_bind, pure_ok,
      List.cons_append, List.nil_append]
  exact attach_valid_for .sharedCell (attach_valid_for .sharedCell seed first) second

def attachWorkers (issued : Issued) : Except Fault (Workers issued) := do
  match ownMade : makeWorker issued.checked.world 11 ownContext
      issued.ready.codeA issued.ready.callerA [issued.ready.dataA]
      [issued.identifier, issued.ready.atomicA] with
  | .error fault => .error fault
  | .ok own =>
    match peerMade : makeWorker issued.checked.world 12 peerContext
        issued.ready.codeB issued.ready.callerB [issued.ready.dataB]
        [issued.ready.atomicB] with
    | .error fault => .error fault
    | .ok peer => .ok ⟨own, peer, ownMade, peerMade⟩

/-- The two enqueue results and their exact ordinary tags are retained. These
are admission-boundary facts, not claims about past machine instructions. -/
structure InitialFIFO (world : World) (resources : Resources) (ticket : OS.Ownership.Ticket) where
  first : Queue.Cursor
  last : Queue.Cursor
  firstSuccess : Queue.Cursor.empty.enqueue world resources firstStore .sharedCell = .ok first
  secondSuccess : first.enqueue world resources secondStore .sharedCell = .ok last
  firstShape : first.pending = [.ordinary ticket firstStore]
  shape : last.pending = [.ordinary ticket firstStore, .ordinary ticket secondStore]

def admitInitial (world : World) (resources : Resources) (ticket : OS.Ownership.Ticket) :
    Except Fault (InitialFIFO world resources ticket) := do
  match firstSuccess : Queue.Cursor.empty.enqueue world resources firstStore .sharedCell with
  | .error fault => .error fault
  | .ok first =>
    match secondSuccess : first.enqueue world resources secondStore .sharedCell with
    | .error fault => .error fault
    | .ok last => do
      let firstShape ← require (first.pending = [.ordinary ticket firstStore])
      let shape ← require (last.pending =
        [.ordinary ticket firstStore, .ordinary ticket secondStore])
      return ⟨first, last, firstSuccess, secondSuccess, firstShape.down, shape.down⟩

/-- Admission comes from the actual enqueue_effect witnesses, including the
ordinary enqueue's consumption of its occurrence number. -/
theorem InitialFIFO.admissions {world : World} {resources : Resources}
    {ticket : OS.Ownership.Ticket} (fifo : InitialFIFO world resources ticket) :
    Queue.Admission world resources firstStore 0 .sharedCell (.ordinary ticket firstStore) ∧
    Queue.Admission world resources secondStore 1 .sharedCell (.ordinary ticket secondStore) := by
  obtain ⟨firstEntry, firstAdmission, firstPending, _firstCounter⟩ :=
    Queue.Cursor.enqueue_effect .empty world resources firstStore .sharedCell
      fifo.first fifo.firstSuccess
  obtain ⟨secondEntry, secondAdmission, secondPending, _secondCounter⟩ :=
    Queue.Cursor.enqueue_effect fifo.first world resources secondStore .sharedCell
      fifo.last fifo.secondSuccess
  have firstPending' : fifo.first.pending = [firstEntry] := by
    simpa only [Queue.Cursor.empty, List.nil_append] using firstPending
  have firstEq : Queue.Entry.ordinary ticket firstStore = firstEntry :=
    (List.cons.inj (fifo.firstShape.symm.trans firstPending')).1
  have counter : fifo.first.nextStore = 1 :=
    Queue.Cursor.enqueue_nextStore .empty world resources firstStore .sharedCell
      fifo.first fifo.firstSuccess
  have secondPending' : fifo.last.pending = [firstEntry, secondEntry] := by
    simpa only [firstPending', List.cons_append, List.nil_append] using secondPending
  have secondEq : Queue.Entry.ordinary ticket secondStore = secondEntry :=
    (List.cons.inj (List.cons.inj (fifo.shape.symm.trans secondPending')).2).1
  constructor
  · simpa only [Queue.Cursor.empty, ← firstEq] using firstAdmission
  · simpa only [counter, ← secondEq] using secondAdmission

/-- The worker-installation obligation follows from real Admission.valid. -/
theorem InitialFIFO.valid {world : World} {resources : Resources}
    {ticket : OS.Ownership.Ticket} (fifo : InitialFIFO world resources ticket) :
    ∀ entry ∈ fifo.last.pending, PendingValid world resources entry .sharedCell := by
  intro entry member
  rw [fifo.shape] at member
  rcases List.mem_cons.mp member with same | member
  · subst entry
    exact fifo.admissions.1.valid
  · have same := List.mem_singleton.mp member
    subst entry
    exact fifo.admissions.2.valid

theorem InitialFIFO.nextStore {world : World} {resources : Resources}
    {ticket : OS.Ownership.Ticket} (fifo : InitialFIFO world resources ticket) :
    fifo.last.nextStore = 2 := by
  have first := Queue.Cursor.enqueue_nextStore .empty world resources firstStore .sharedCell
    fifo.first fifo.firstSuccess
  have second := Queue.Cursor.enqueue_nextStore fifo.first world resources secondStore .sharedCell
    fifo.last fifo.secondSuccess
  calc
    fifo.last.nextStore = fifo.first.nextStore + 1 := second
    _ = Queue.Cursor.empty.nextStore + 1 + 1 := congrArg (fun count : Nat => count + 1) first
    _ = 2 := rfl

theorem InitialFIFO.ordered {world : World} {resources : Resources}
    {ticket : OS.Ownership.Ticket} (fifo : InitialFIFO world resources ticket) :
    fifo.last.Ordered :=
  Queue.Cursor.enqueue_ordered fifo.first world resources secondStore .sharedCell fifo.last
    (Queue.Cursor.enqueue_ordered .empty world resources firstStore .sharedCell fifo.first
      Queue.Cursor.empty_ordered fifo.firstSuccess) fifo.secondSuccess

/-- Small finite observations of original resource identities, without equality
or decisions on context functions or proof-carrying worlds. -/
def resourceView (worker : Worker) :
    Nat × Nat × Nat × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64 :=
  (worker.resources.actor, worker.resources.code.identifier, worker.resources.caller.identifier,
    worker.resources.callerAddress, worker.resources.grants, worker.resources.atomics)

structure Fixture where
  issued : Issued
  workers : Workers issued
  fifo : InitialFIFO workers.state.world workers.own.resources issued.ready.dataA
  old : HandleView workers.state.world 11 issued.ready.atomicA
  fresh : HandleView workers.state.world 11 issued.identifier
  peer : HandleView workers.state.world 12 issued.ready.atomicB
  reverseCreation : issued.ready.atomicA.index < issued.identifier.index
  commonHandleCell : fresh.handle.cell = old.handle.cell ∧ peer.handle.cell = old.handle.cell
  commonCell : fresh.cell = old.cell ∧ peer.cell = old.cell
  counterAddress : old.cell.address = 65536
  initialCounter : loadQWord (published workers.state.world) 65536 = .ok 9
  ownResources : resourceView workers.own =
    (11, issued.ready.codeA, issued.ready.callerA, 262144, [issued.ready.dataA],
      [issued.identifier, issued.ready.atomicA])
  peerResources : resourceView workers.peer =
    (12, issued.ready.codeB, issued.ready.callerB, 327680, [issued.ready.dataB],
      [issued.ready.atomicB])
  ownCode : CodeAt (published workers.state.world) 393216 ownBytes
  peerCode : CodeAt (published workers.state.world) 393221 peerBytes
  ownFits : OS.Borrowing.Subregion ⟨393216, ownBytes.length⟩ workers.own.resources.code.loan.region
  peerFits : OS.Borrowing.Subregion ⟨393221, peerBytes.length⟩ workers.peer.resources.code.loan.region
  ownCaller : OS.Borrowing.loadWord64 workers.state.world.legacy.shared 11
    workers.own.resources.caller.identifier workers.own.resources.callerAddress = .ok 0x7000
  peerCaller : OS.Borrowing.loadWord64 workers.state.world.legacy.shared 12
    workers.peer.resources.caller.identifier workers.peer.resources.callerAddress = .ok 0x8000

/-- Only pending and nextStore are installed at the admitted initial boundary.
The original own worker and peer are retained separately in Fixture.workers. -/
def Fixture.own (fixture : Fixture) : Worker :=
  { fixture.workers.own with
    pending := fixture.fifo.last.pending
    nextStore := fixture.fifo.last.nextStore }

def Fixture.state (fixture : Fixture) : OS.TSO64.State :=
  install fixture.workers.state 0 fixture.workers.state.world fixture.own

theorem Fixture.valid (fixture : Fixture) : WellFormed fixture.state .sharedCell := by
  have original := fixture.workers.valid.2 fixture.workers.own
    (by change fixture.workers.own ∈ [fixture.workers.own, fixture.workers.peer]; simp)
  exact install_valid fixture.workers.valid (Stable.refl _) fixture.workers.valid.1
    ⟨original.1, fixture.fifo.valid⟩

structure Checked where
  state : OS.TSO64.State
  valid : WellFormed state .sharedCell

def Fixture.checked (fixture : Fixture) : Checked := ⟨fixture.state, fixture.valid⟩

/-- Present worker observations for admission by the later integration client. -/
theorem Fixture.own_live (fixture : Fixture) :
    fixture.state.workers[0]? = some fixture.own := rfl

theorem Fixture.peer_live (fixture : Fixture) :
    fixture.state.workers[1]? = some fixture.workers.peer := rfl

theorem Fixture.own_context (fixture : Fixture) : fixture.own.context = ownContext :=
  (makeWorker_valid_for .sharedCell fixture.workers.ownMade).2.2.2

theorem Fixture.own_running (fixture : Fixture) : fixture.own.phase = .running :=
  (makeWorker_valid_for .sharedCell fixture.workers.ownMade).2.1

theorem Fixture.own_pending (fixture : Fixture) :
    fixture.own.pending = [.ordinary fixture.issued.ready.dataA firstStore,
      .ordinary fixture.issued.ready.dataA secondStore] := fixture.fifo.shape

theorem Fixture.own_nextStore (fixture : Fixture) : fixture.own.nextStore = 2 :=
  fixture.fifo.nextStore

theorem Fixture.handles_different (fixture : Fixture) :
    fixture.issued.identifier ≠ fixture.issued.ready.atomicA := by
  intro same
  have order := fixture.reverseCreation
  rw [same] at order
  exact Nat.lt_irrefl _ order

/-- All rejection paths concern current setup only. Handles are issued through
TSO64.handle, workers through makeWorker/attach_valid_for, and both entries
through Cursor.enqueue. There is no execution or desired output in this builder. -/
def blockingFixture : Except Fault Fixture := do
  let issued ← issueOwn
  let workers ← attachWorkers issued
  let fifo ← admitInitial workers.state.world workers.own.resources issued.ready.dataA
  let old ← readHandle workers.state.world 11 issued.ready.atomicA
  let fresh ← readHandle workers.state.world 11 issued.identifier
  let peer ← readHandle workers.state.world 12 issued.ready.atomicB
  let reverseCreation ← require (issued.ready.atomicA.index < issued.identifier.index)
  let commonHandleCell ← require
    (fresh.handle.cell = old.handle.cell ∧ peer.handle.cell = old.handle.cell)
  let commonCell ← require (fresh.cell = old.cell ∧ peer.cell = old.cell)
  let counterAddress ← require (old.cell.address = 65536)
  let initialCounter ← require (loadQWord (published workers.state.world) 65536 = .ok 9)
  let ownResources ← require (resourceView workers.own =
    (11, issued.ready.codeA, issued.ready.callerA, 262144, [issued.ready.dataA],
      [issued.identifier, issued.ready.atomicA]))
  let peerResources ← require (resourceView workers.peer =
    (12, issued.ready.codeB, issued.ready.callerB, 327680, [issued.ready.dataB],
      [issued.ready.atomicB]))
  let ownCode ← require (checkCode (published workers.state.world) 393216 ownBytes = true)
  let peerCode ← require (checkCode (published workers.state.world) 393221 peerBytes = true)
  let ownFits ← require (OS.Borrowing.Subregion ⟨393216, ownBytes.length⟩
    workers.own.resources.code.loan.region)
  let peerFits ← require (OS.Borrowing.Subregion ⟨393221, peerBytes.length⟩
    workers.peer.resources.code.loan.region)
  let ownCaller ← require (OS.Borrowing.loadWord64 workers.state.world.legacy.shared 11
    workers.own.resources.caller.identifier workers.own.resources.callerAddress = .ok 0x7000)
  let peerCaller ← require (OS.Borrowing.loadWord64 workers.state.world.legacy.shared 12
    workers.peer.resources.caller.identifier workers.peer.resources.callerAddress = .ok 0x8000)
  return ⟨issued, workers, fifo, old, fresh, peer, reverseCreation.down,
    commonHandleCell.down, commonCell.down, counterAddress.down, initialCounter.down,
    ownResources.down, peerResources.down,
    checkCode_sound _ _ _ ownCode.down, checkCode_sound _ _ _ peerCode.down,
    ownFits.down, peerFits.down, ownCaller.down, peerCaller.down⟩

/-- Small stage views for the parent's serialized admission checks. They retain
production results without requiring decidable equality on any setup witness.
No equality to an expected observation is asserted in this preparation file. -/
def issueView : Except Fault (Nat × Nat × Nat × Word) := do
  let issued ← issueOwn
  return (issued.ready.atomicA.index, issued.ready.atomicB.index,
    issued.identifier.index, issued.old.cell.address)

def queueView : Except Fault (List Queue.Entry × Nat) := do
  let issued ← issueOwn
  let workers ← attachWorkers issued
  let fifo ← admitInitial workers.state.world workers.own.resources issued.ready.dataA
  return (fifo.last.pending, fifo.last.nextStore)

def presentView : Except Fault Unit := blockingFixture.map (fun _ => ())

#print axioms Workers.valid
#print axioms InitialFIFO.admissions
#print axioms InitialFIFO.valid
#print axioms InitialFIFO.nextStore
#print axioms InitialFIFO.ordered
#print axioms Fixture.valid
#print axioms Fixture.own_context
#print axioms Fixture.handles_different
#print axioms blockingFixture
#audit_edsl

end EDSL.Tests.Support.MixedBlockingFixture
