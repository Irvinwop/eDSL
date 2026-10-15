/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Stubs
import EDSL.OS.Futex.RuntimeInvariant
import EDSL.OS.Futex.ClientFrames

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

inductive Role where
  | wait (expected : BitVec 32)
  | publishPayloadWake
  | payloadPeer
  deriving DecidableEq, Repr

def publishingBytes : List Byte :=
  [0xb8, 0x44, 0x33, 0x22, 0x11, 0x89, 0x06,
   0xb8, 1, 0, 0, 0, 0x87, 0x07] ++ Examples.FutexStubs.Profile.wakeOne.bytes

def peerBytes : List Byte := [0xb8, 0x88, 0x77, 0x66, 0x55, 0x89, 0x06, 0xc3]

def Role.bytes : Role → List Byte
  | .wait _ => Examples.FutexStubs.Profile.wait.bytes
  | .publishPayloadWake => publishingBytes
  | .payloadPeer => peerBytes

structure Client where
  role : Role
  entry : Threads.Context
  subject : Nat
  codeLoan : Nat
  stackLoan : Nat
  returnTarget : Word

structure Cohort where
  seed : Futex.State
  profile : Physical.Profile
  registration : Resources.Registration
  clients : List Client
  /-- The initial resource-handle frontier, not an invocation frontier. -/
  pinFloor : Nat
  fixedHandles : List (Nat × Atomics.Handle)

def Role.value : Role → BitVec 32
  | .payloadPeer => 0x55667788
  | _ => 0x11223344

def Client.store (client : Client) : StoreBuffer.Store :=
  ⟨client.entry.registers .rsi, client.role.value⟩

def Client.operation (client : Client) : Op :=
  match client.role with
  | .wait expected => .wait expected
  | _ => .wakeOne

/-- A finite control location. The exchanged old value is private proof data;
it is overwritten by the following MOV before the WAKE request. -/
inductive Stage where
  | start | payload | stored | exchange | exchanged (old : BitVec 32)
  | number | operation | count
  deriving DecidableEq, Repr

def Stage.Valid (role : Role) (stage : Stage) : Prop :=
  match role with
  | .publishPayloadWake => True
  | .wait _ => match stage with
    | .start | .number | .operation => True
    | _ => False
  | .payloadPeer => match stage with
    | .start | .payload | .stored => True
    | _ => False

def Stage.offset (role : Role) : Stage → Nat
  | .start => 0
  | .payload => 5
  | .stored => 7
  | .exchange => 12
  | .exchanged _ => 14
  | .number => match role with | .wait _ => 5 | _ => 19
  | .operation => match role with | .wait _ => 10 | _ => 24
  | .count => 29

/-- The private context at each location is stated independently of decoding
and execution. All unspecified entry registers and flags remain arbitrary. -/
def Stage.context (client : Client) (stage : Stage) : Threads.Context :=
  { registers := fun register =>
      if register = .rax ∧ stage ≠ .start then
        match stage with
        | .payload | .stored => client.role.value.setWidth 64
        | .exchange => 1
        | .exchanged old => old.setWidth 64
        | _ => 202
      else if register = .rsi ∧ (stage = .operation ∨ stage = .count) then
        match client.role with | .wait _ => 128 | _ => 129
      else if register = .rdx ∧ stage = .count then 1
      else client.entry.registers register
    rip := client.entry.rip + BitVec.ofNat 64 (stage.offset client.role)
    flags := client.entry.flags }

def Stage.instruction (role : Role) (stage : Stage) : Instruction :=
  match role with
  | .wait _ => match stage with
    | .start => .mov32 .rax 202
    | .number => .mov32 .rsi 128
    | _ => .syscall
  | .payloadPeer => match stage with
    | .start => .mov32 .rax 0x55667788
    | .payload => .storeEaxRsi
    | _ => .ret
  | .publishPayloadWake => match stage with
    | .start => .mov32 .rax 0x11223344
    | .payload => .storeEaxRsi
    | .stored => .mov32 .rax 1
    | .exchange => .exchangeEaxRdi
    | .exchanged _ => .mov32 .rax 202
    | .number => .mov32 .rsi 129
    | .operation => .mov32 .rdx 1
    | .count => .syscall

def Client.callStage (client : Client) : Stage :=
  match client.role with | .wait _ => .operation | _ => .count

def Client.callContext (client : Client) : Threads.Context :=
  client.callStage.context client

def Client.request (client : Client) (memory : Memory) : SyscallRequest :=
  ⟨MachineThreads.contextState client.callContext memory, client.callContext.rip + 2⟩

/-- Exact private request and continuation, rebased onto its own historical
capture RAM. No equality to the seed's RAM or to present RAM is required. -/
def Client.Family (client : Client) (request : SyscallRequest) : Prop :=
  client.role ≠ .payloadPeer ∧ request = client.request request.user.memory

def CallFamily (cohort : Cohort) (worker : Nat) (request : SyscallRequest) : Prop :=
  ∃ client, cohort.clients[worker]? = some client ∧ client.Family request

def Client.resumed (client : Client) (raw flags rcx r11 : Word) : Threads.Context :=
  { registers := fun register =>
      if register = .rax then raw
      else if register = .rcx then rcx
      else if register = .r11 then r11
      else client.callContext.registers register
    rip := client.callContext.rip + 2
    flags := flags }

def Client.returned (client : Client) (context : Threads.Context) : Threads.Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8
      else context.registers register
    rip := client.returnTarget }

def Client.Published (client : Client) (memory : Memory) : Prop :=
  client.role = .publishPayloadWake →
    loadDWord memory client.store.address = .ok client.store.value

def Stage.bufferCondition (role : Role) (stage : Stage) (token : StoreBuffer.Store)
    (published : Prop) (buffer : StoreBuffer.Buffer) : Prop :=
  match role with
  | .wait _ => buffer = []
  | .payloadPeer => match stage with
    | .stored => buffer = [] ∨ buffer = [token]
    | _ => buffer = []
  | .publishPayloadWake => match stage with
    | .start | .payload => buffer = []
    | .stored | .exchange => buffer = [token] ∨ (buffer = [] ∧ published)
    | _ => buffer = [] ∧ published

def Stage.FIFO (client : Client) (stage : Stage) (memory : Memory)
    (buffer : StoreBuffer.Buffer) : Prop :=
  stage.bufferCondition client.role client.store (client.Published memory) buffer

/-- Every actual record, including a returned producer with an undrained FIFO,
has one of these concrete finite controls. -/
inductive WorkerControl (client : Client) (worker : Nat) (state : Suspend.State)
    (actual : TSO.Worker) : Prop where
  | running (stage : Stage) (supported : stage.Valid client.role)
      (context : actual.context = stage.context client)
      (live : actual.returned = false) (free : state.pending worker = none)
      (fifo : stage.FIFO client state.machine.memory actual.buffer)
  | entered (saved : Suspend.Saved) (pending : state.pending worker = some saved)
      (owner : saved.worker = worker) (family : client.Family saved.request)
      (context : actual.context = client.callContext) (live : actual.returned = false)
      (empty : actual.buffer = []) (published : client.Published state.machine.memory)
  | resumed (outcome : Outcome client.operation) (flags rcx r11 : Word)
      (caller : client.role ≠ .payloadPeer)
      (context : actual.context = client.resumed outcome.raw flags rcx r11)
      (live : actual.returned = false) (free : state.pending worker = none)
      (empty : actual.buffer = []) (published : client.Published state.machine.memory)
  | returned (outcome : Outcome client.operation) (flags rcx r11 : Word)
      (caller : client.role ≠ .payloadPeer)
      (context : actual.context = client.returned (client.resumed outcome.raw flags rcx r11))
      (done : actual.returned = true) (free : state.pending worker = none)
      (empty : actual.buffer = []) (published : client.Published state.machine.memory)
  | peerReturned (peer : client.role = .payloadPeer)
      (context : actual.context = client.returned (Stage.stored.context client))
      (done : actual.returned = true) (free : state.pending worker = none)
      (fifo : actual.buffer = [] ∨ actual.buffer = [client.store])

def Control (cohort : Cohort) (state : Suspend.State) : Prop :=
  ∀ worker actual, state.machine.workers[worker]? = some actual →
    ∃ client, cohort.clients[worker]? = some client ∧ WorkerControl client worker state actual

def FIFOAuthorized (cohort : Cohort) (state : Futex.State) : Prop :=
  ∀ worker actual, state.suspended.machine.workers[worker]? = some actual →
    ∀ store ∈ actual.buffer, ∃ grant, cohort.profile.payload worker = some grant ∧
      grant.address = store.address ∧ grant.Valid state.authority

def Protected (cohort : Cohort) (state : Futex.State) : Prop :=
  ∀ (worker : Nat) (client : Client), cohort.clients[worker]? = some client →
    Threads.HasLoan state.authority.shared client.subject client.codeLoan
      ⟨client.entry.rip, client.role.bytes.length⟩ ∧
    Threads.HasLoan state.authority.shared client.subject client.stackLoan
      ⟨client.entry.registers .rsp, 8⟩ ∧
    CodeAt state.suspended.machine.memory client.entry.rip client.role.bytes ∧
    readWord state.suspended.machine.memory (client.entry.registers .rsp) = .ok client.returnTarget ∧
    canonical client.returnTarget = true ∧
    AgreesOn state.authority.shared.resources.space cohort.seed.authority.shared.resources.space
      client.entry.rip client.role.bytes.length ∧
    AgreesOn state.authority.shared.resources.space cohort.seed.authority.shared.resources.space
      (client.entry.registers .rsp) 8

def Descriptor (cohort : Cohort) (worker : Nat) (client : Client) : Prop :=
  client.entry.registers .rdi = cohort.registration.address ∧
  client.entry.registers .r10 = 0 ∧ client.entry.registers .r8 = 0 ∧ client.entry.registers .r9 = 0 ∧
  match client.role with
  | .wait expected => client.entry.registers .rdx = expected.setWidth 64 ∧
      cohort.profile.payload worker = none ∧ cohort.profile.atomic worker = none
  | .publishPayloadWake =>
      (∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = client.store.address) ∧
      ∃ access handle, cohort.profile.atomic worker = some access ∧
        (access.handle, handle) ∈ cohort.fixedHandles ∧ handle.actor = access.actor ∧
        handle.address = cohort.registration.address ∧ handle.owner = cohort.registration.owner ∧
        handle.ticket = cohort.registration.ticket
  | .payloadPeer =>
      (∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = client.store.address) ∧
      cohort.profile.atomic worker = none

structure Static (cohort : Cohort) : Prop where
  frontier : cohort.pinFloor = cohort.seed.authority.nextHandle
  fixedBelow : ∀ identifier handle, (identifier, handle) ∈ cohort.fixedHandles → identifier < cohort.pinFloor
  keeperFixed : (cohort.registration.keeper, cohort.registration.handle) ∈ cohort.fixedHandles
  descriptors : ∀ worker client, cohort.clients[worker]? = some client → Descriptor cohort worker client
  /-- Different ordinary destinations are independently granted; in particular
  no peer can overwrite a publisher's four payload bytes. -/
  payloadSeparate : ∀ left a right b, left ≠ right → cohort.profile.payload left = some a →
    cohort.profile.payload right = some b → StoreBuffer.Separate a.address b.address

/-- A memory effect retains a payload which was already current. This is a
plain read frame, to be derived from disjoint checked physical footprints. -/
def PublicationFrame (cohort : Cohort) (before after : Memory) : Prop :=
  ∀ (worker : Nat) (client : Client), cohort.clients[worker]? = some client →
    client.Published before → client.Published after

/-- Current forwarded stacks. This follows from Protected plus FIFO rights
and grant/loan separation, and does not require peer FIFOs to be empty. -/
def StackViews (cohort : Cohort) (state : Suspend.State) : Prop :=
  ∀ (worker : Nat) (actual : TSO.Worker) (client : Client), state.machine.workers[worker]? = some actual →
    cohort.clients[worker]? = some client →
    readWord (StoreBuffer.view state.machine.memory actual.buffer) (client.entry.registers .rsp) =
      .ok client.returnTarget

end EDSL.OS.Futex.Clients
