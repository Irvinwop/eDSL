/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Model
import EDSL.OS.Futex.Predicate.Resources
import EDSL.OS.Futex.ClientModel
import EDSL.OS.Futex.ClientFIFO
import EDSL.OS.Futex.ClientResources
import EDSL.OS.Futex.ClientControlDecode

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

/-- The loop and the unchanged publishing/peer profiles have distinct control
representations. A loop is never relabeled as the old thirteen-byte WAIT. -/
inductive Kind where
  | waitLoop (client : Client)
  | legacy (client : Clients.Client)

def Kind.binding : Kind → CodeBinding
  | .waitLoop client =>
      ⟨client.subject, client.codeLoan, client.stackLoan, client.entry, bytes, client.returnTarget⟩
  | .legacy client =>
      ⟨client.subject, client.codeLoan, client.stackLoan, client.entry, client.role.bytes, client.returnTarget⟩

def Kind.operation : Kind → Op
  | .waitLoop _ => .wait 0
  | .legacy client => client.operation

def Kind.Family : Kind → SyscallRequest → Prop
  | .waitLoop client => client.Family
  | .legacy client => client.Family

def Kind.Published : Kind → Memory → Prop
  | .waitLoop _ => fun _ => True
  | .legacy client => client.Published

structure Cohort where
  seed : Futex.State
  profile : Physical.Profile
  registration : Resources.Registration
  clients : List Kind
  waiter : Nat
  pinFloor : Nat
  fixedHandles : List (Nat × Atomics.Handle)

/-- Only the old descriptor's environment parameters are reused. This empty
metadata carrier supplies no old client membership, control or admission. -/
def Cohort.legacyEnvironment (cohort : Cohort) : Clients.Cohort :=
  ⟨cohort.seed, cohort.profile, cohort.registration, [], cohort.pinFloor, cohort.fixedHandles⟩

def Descriptor (cohort : Cohort) (worker : Nat) : Kind → Prop
  | .waitLoop client =>
      client.entry.registers .rdi = cohort.registration.address ∧ client.ABI ∧
      cohort.profile.payload worker = none ∧ cohort.profile.atomic worker = none ∧ worker = cohort.waiter
  | .legacy client =>
      Clients.Descriptor cohort.legacyEnvironment worker client ∧ Clients.PayloadRole client.role

structure Static (cohort : Cohort) : Prop where
  frontier : cohort.pinFloor = cohort.seed.authority.nextHandle
  fixedBelow : ∀ identifier handle, (identifier, handle) ∈ cohort.fixedHandles → identifier < cohort.pinFloor
  keeperFixed : (cohort.registration.keeper, cohort.registration.handle) ∈ cohort.fixedHandles
  designated : ∃ client, cohort.clients[cohort.waiter]? = some (.waitLoop client)
  descriptors : ∀ worker kind, cohort.clients[worker]? = some kind → Descriptor cohort worker kind
  loopTargets : ∀ (worker : Nat) (client : Client), cohort.clients[worker]? = some (.waitLoop client) →
    canonical client.entry.rip = true ∧ canonical (client.entry.rip + 29) = true
  payloadSeparate : ∀ left a right b, left ≠ right → cohort.profile.payload left = some a →
    cohort.profile.payload right = some b → StoreBuffer.Separate a.address b.address

/-- A loaded value may be stale. Zero need not equal current RAM after
publication; an observed one retains the current signal-word knowledge. -/
def Point.Observed : Point → Option (BitVec 32)
  | .compare observed | .branch observed | .done observed => some observed
  | _ => none

def Point.Known (address : Word) (memory : Memory) (point : Point) : Prop :=
  ∀ observed, point.Observed = some observed →
    (observed = 0 ∨ observed = 1) ∧
    (observed = 1 → loadDWord memory address = .ok 1)

theorem Point.Known.frame {address : Word} {before after : Memory} {point : Point}
    (known : point.Known address before)
    (word : loadDWord before address = .ok 1 → loadDWord after address = .ok 1) :
    point.Known address after := by
  intro observed found
  obtain ⟨domain, published⟩ := known observed found
  exact ⟨domain, fun one => word (published one)⟩

/-- The resource-aware control refines the general raw loop control with
current signal knowledge. Every field describes the current state or its saved
historical request; none promises future execution or scheduler selection. -/
inductive LoopControl (address : Word) (client : Client) (worker : Nat)
    (state : Suspend.State) (actual : TSO.Worker) : Prop where
  | running (point : Point) (current : Running client point actual.context)
      (known : point.Known address state.machine.memory)
      (live : actual.returned = false) (free : state.pending worker = none)
      (empty : actual.buffer = [])
  | entered (saved : Suspend.Saved) (pending : state.pending worker = some saved)
      (owner : saved.worker = worker) (family : client.Family saved.request)
      (context : actual.context = .ofState saved.request.user)
      (live : actual.returned = false) (empty : actual.buffer = [])
  | returned (context : Threads.Context) (observed : BitVec 32)
      (checked : Running client (.done observed) context)
      (known : (Point.done observed).Known address state.machine.memory)
      (historical : actual.context = client.returned context)
      (done : actual.returned = true) (free : state.pending worker = none)
      (empty : actual.buffer = [])

theorem LoopControl.raw {address : Word} {client : Client} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker}
    (control : LoopControl address client worker state actual) :
    WorkerControl client worker state actual := by
  cases control with
  | running point current _ live free empty => exact .running point current live free empty
  | entered saved pending owner family context live empty =>
    exact .entered saved pending owner family context live empty
  | returned context observed checked _ historical done free empty =>
    exact .returned context observed checked historical done free empty

theorem LoopControl.fifo_empty {address : Word} {client : Client} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker}
    (control : LoopControl address client worker state actual) : actual.buffer = [] := by
  cases control <;> assumption

theorem LoopControl.frame {address : Word} {client : Client} {worker : Nat}
    {before after : Suspend.State} {actual : TSO.Worker}
    (control : LoopControl address client worker before actual)
    (pending : after.pending worker = before.pending worker)
    (word : loadDWord before.machine.memory address = .ok 1 →
      loadDWord after.machine.memory address = .ok 1) :
    LoopControl address client worker after actual := by
  cases control with
  | running point current known live free empty =>
    exact .running point current (known.frame word) live (pending.trans free) empty
  | entered saved savedAt owner family context live empty =>
    exact .entered saved (pending.trans savedAt) owner family context live empty
  | returned context observed checked known historical done free empty =>
    exact .returned context observed checked (known.frame word) historical done (pending.trans free) empty

def Kind.Control (cohort : Cohort) (kind : Kind) (worker : Nat)
    (state : Suspend.State) (actual : TSO.Worker) : Prop :=
  match kind with
  | .waitLoop client => LoopControl cohort.registration.address client worker state actual
  | .legacy client => Clients.WorkerControl client worker state actual

def Control (cohort : Cohort) (state : Suspend.State) : Prop :=
  ∀ (worker : Nat) (actual : TSO.Worker), state.machine.workers[worker]? = some actual →
    ∃ kind : Kind, cohort.clients[worker]? = some kind ∧ Kind.Control cohort kind worker state actual

def Protected (cohort : Cohort) (state : Futex.State) : Prop :=
  ∀ (worker : Nat) (kind : Kind), cohort.clients[worker]? = some kind →
    (Kind.binding kind).Protected cohort.seed.authority.shared.resources.space state

def FIFOAuthorized (cohort : Cohort) (state : Futex.State) : Prop :=
  ∀ worker actual, state.suspended.machine.workers[worker]? = some actual →
    ∀ store ∈ actual.buffer, ∃ grant, cohort.profile.payload worker = some grant ∧
      grant.address = store.address ∧ grant.Valid state.authority

def CallFamily (cohort : Cohort) (worker : Nat) (request : SyscallRequest) : Prop :=
  ∃ kind : Kind, cohort.clients[worker]? = some kind ∧ kind.Family request

def WordDomain (cohort : Cohort) (state : Futex.State) : Prop :=
  loadDWord state.suspended.machine.memory cohort.registration.address = .ok 0 ∨
    loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1

structure Admitted (cohort : Cohort) (state : Futex.State) : Prop where
  static : Static cohort
  runtime : Runtime.Invariant cohort.profile state
  slots : state.suspended.machine.workers.length = cohort.clients.length
  control : Control cohort state.suspended
  registration : state.registration = some cohort.registration
  fixed : ∀ identifier handle, (identifier, handle) ∈ cohort.fixedHandles →
    state.authority.handles identifier = some handle
  discipline : Clients.PinDiscipline cohort.pinFloor state
  target : targetSupported cohort.profile.service state.authority cohort.registration.address = true
  payload : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid state.authority
  fifo : FIFOAuthorized cohort state
  «protected» : Protected cohort state
  word : WordDomain cohort state

theorem Admitted.keeper {cohort : Cohort} {state : Futex.State} (admitted : Admitted cohort state) :
    Resources.Valid state.authority cohort.registration :=
  admitted.fixed _ _ admitted.static.keeperFixed

end EDSL.OS.Futex.Predicate

#audit_edsl
