/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Sequence

namespace EDSL.OS.TSO64
open X86 AddressSpace

inductive Phase where
  | running | returned
  deriving DecidableEq, Repr

structure Context where
  registers : Register → Word
  rip : Word
  flags : Word

def Context.ofCPU (cpu : X86.State) : Context := ⟨cpu.registers, cpu.rip, cpu.flags⟩

structure Worker where
  context : Context
  resources : Resources
  phase : Phase
  pending : List Pending
  nextStore : Nat := 0

structure State where
  world : World
  workers : List Worker

inductive Action where
  | issue (tid : Nat) (af : Bool)
  | drain (tid : Nat)
  deriving DecidableEq, Repr

inductive Observation where
  | ordinary (tid : Nat)
  | returned (tid : Nat)
  | rmw (tid : Nat) (event : Atomics64.FetchAddEvent)
  | blocked (tid : Nat)
  | drained (tid : Nat) (pending : Pending)
  deriving DecidableEq, Repr

def Observation.retired : Observation → Nat
  | .ordinary _ | .returned _ | .rmw _ _ => 1
  | .blocked _ | .drained _ _ => 0

def cpu (worker : Worker) (memory : Memory) : X86.State :=
  ⟨worker.context.registers, worker.context.rip, worker.context.flags, memory⟩

def sharedCPU (state : State) (worker : Worker) : X86.State := cpu worker (published state.world)

def localCPU (state : State) (worker : Worker) : X86.State :=
  cpu worker (StoreBuffer.Mixed.view (published state.world) (payload worker.pending))

/-- Every decoder fetch is confined to the current original code loan. The
ordinary/locked executor subsequently decodes the actual current CPU memory
again; agreement with this guarded dispatch is checked, not supplied by PCs. -/
def fetchCPU (state : State) (worker : Worker) : X86.State :=
  let memory := published state.world
  cpu worker { memory with executable := (fun address => memory.executable address && decide (worker.resources.code.loan.region.Contains address)) }

inductive Decoded where
  | ordinary (instruction : Sequential.Instruction)
  | locked (instruction : LockedAdd64.Instruction)

def decode (state : X86.State) : Except Fault Decoded := do
  let first ← (fetchByte state.memory state.rip).mapError Fault.machine
  if first = 0xf0 then
    return .locked (← (LockedAdd64.decodeAt state).mapError Fault.machine)
  else return .ordinary (← (Sequential.decodeAt state).mapError Fault.machine)

/-- Explicit fail-closed ordinary profile. Branches, arithmetic, syscalls,
legacy DWORD atomics, fences and all other forms remain unsupported. -/
def supported : Sequential.Instruction → Bool
  | .movReg32 .. | .movReg64 .. | .loadMem32 .. | .loadMem64 ..
  | .storeMem32 .. | .storeMem64 .. | .nop _ | .endbr64IbtDisabled => true
  | .legacy (.mov32 ..) | .legacy .movEaxEdi | .legacy .movEaxEsi
  | .legacy .loadEaxRdi | .legacy .loadEaxRsi
  | .legacy .storeEsiRdi | .legacy .storeEaxRsi | .legacy .ret => true
  | _ => false

/-- Production intent classifiers capture both operands BEFORE execution. -/
def storeIntent (instruction : Sequential.Instruction) (initial : X86.State) : Option Store :=
  match instruction.storeIntent64 initial with
  | some (address, value) => some ⟨address, .qword value⟩
  | none => instruction.storeIntent initial |>.map fun (address, value) => ⟨address, .dword value⟩

def codeFits (worker : Worker) (length : Nat) : Prop :=
  Borrowing.Subregion ⟨worker.context.rip, length⟩ worker.resources.code.loan.region

instance (worker : Worker) (length : Nat) : Decidable (codeFits worker length) :=
  inferInstanceAs (Decidable (Borrowing.Subregion _ _))

/-- All operand admissions precede execution. Stack access requires the
original slot, even if some other address has a valid readable mapping. -/
def checkRead (state : State) (worker : Worker) (read : Sequential.Read)
    (profile : Profile := .ownedOnly) : Except Fault Unit := do
  match read.kind with
  | .stack =>
    if read.address ≠ worker.resources.callerAddress ∨ read.bytes ≠ 8 then throw .callerSlot
    let _ ← (Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier read.address).mapError (fun _ => Fault.resource)
    return ()
  | .data =>
    let value ← match read.bytes with
      | 4 => pure (StoreBuffer.Mixed.Value.dword 0)
      | 8 => pure (.qword 0)
      | _ => throw .unsupported
    match grantFor state.world worker.resources ⟨read.address, value⟩ with
    | some _ => return ()
    | none =>
      match profile, read.bytes with
      | .sharedCell, 8 =>
        let some _ := atomicFor state.world worker.resources read.address | throw .noAtomicGrant
        return ()
      | _, _ => throw .noGrant

def install (state : State) (tid : Nat) (world : World) (worker : Worker) : State :=
  ⟨world, state.workers.set tid worker⟩

def finishOrdinary (state : State) (tid : Nat) (worker : Worker)
    (pending : List Pending) (observation : Sequential.Observation)
    (nextStore : Nat := worker.nextStore) : Except Fault (State × Observation) := do
  match observation.result with
  | .next output => return (install state tid state.world
      { worker with context := .ofCPU output, pending := pending, nextStore := nextStore }, .ordinary tid)
  | .returned output => return (install state tid state.world
      { worker with context := .ofCPU output, phase := .returned, pending := pending, nextStore := nextStore }, .returned tid)
  | _ => throw .unexpected

def prepareQueue (state : State) (worker : Worker) (instruction : Sequential.Instruction)
    (profile : Profile := .ownedOnly) : Except Fault Queue.Cursor := do
  let cursor : Queue.Cursor := ⟨worker.pending, worker.nextStore⟩
  match storeIntent instruction (localCPU state worker) with
  | none => pure cursor
  | some store => cursor.enqueue state.world worker.resources store profile

def ordinary (state : State) (tid : Nat) (worker : Worker)
    (instruction : Sequential.Instruction) (af : Bool)
    (profile : Profile := .ownedOnly) : Except Fault (State × Observation) := do
  if !supported instruction then throw .unsupported
  if ¬codeFits worker instruction.length then throw .codeBounds
  let initial := localCPU state worker
  let actual ← (Sequential.decodeAt initial).mapError Fault.machine
  if actual ≠ instruction then throw .unexpected
  let _ ← (instruction.operandReads initial).mapM (fun read => checkRead state worker read profile)
  let update ← prepareQueue state worker instruction profile
  let observation ← (Sequential.execute initial instruction af).mapError Fault.machine
  finishOrdinary state tid worker update.pending observation update.nextStore

/-- Only the issuing FIFO blocks. Blocking neither drains nor executes the
primitive. Peer FIFOs are irrelevant to enabledness of this indivisible RMW8. -/
def locked (state : State) (tid : Nat) (worker : Worker)
    (instruction : LockedAdd64.Instruction) : Except Fault (State × Observation) := do
  if ¬codeFits worker instruction.length then throw .codeBounds
  if !worker.pending.isEmpty then return (state, .blocked tid)
  let initial := sharedCPU state worker
  let actual ← (LockedAdd64.decodeAt initial).mapError Fault.machine
  if actual ≠ instruction then throw .unexpected
  let some (identifier, _, _) := atomicFor state.world worker.resources
    (initial.registers instruction.base) | throw .noAtomicGrant
  let result ← (Atomics64.fetchAdd state.world worker.resources.actor identifier
    (initial.registers instruction.source)).mapError Fault.os
  let machine ← (LockedAdd64.step initial).mapError Fault.machine
  return (install state tid result.1 { worker with context := .ofCPU machine.state }, .rmw tid result.2)

def issue (state : State) (tid : Nat) (af : Bool)
    (profile : Profile := .ownedOnly) : Except Fault (State × Observation) := do
  let some worker := state.workers[tid]? | throw .missingWorker
  if worker.phase = .returned then throw .alreadyReturned
  if ¬LeaseCurrent state.world worker.resources.actor worker.resources.code ∨
      ¬LeaseCurrent state.world worker.resources.actor worker.resources.caller then throw .resource
  let instruction ← decode (fetchCPU state worker)
  match instruction with
  | .ordinary instruction => ordinary state tid worker instruction af profile
  | .locked instruction => locked state tid worker instruction

/-- Recheck the FIFO head's complete original authority at the current world,
then publish exactly that head. CPU RAM is never copied into the world. The
default profile rejects a managed head even for arbitrary initial states. -/
def drain (state : State) (tid : Nat) (profile : Profile := .ownedOnly) :
    Except Fault (State × Observation) := do
  let some worker := state.workers[tid]? | throw .missingWorker
  let head :: tail := worker.pending | throw .emptyBuffer
  let result ← Queue.publish state.world worker.resources head profile
  return (install state tid result.1 { worker with pending := tail }, .drained tid head)

def step (state : State) (action : Action) (profile : Profile := .ownedOnly) :
    Except Fault (State × Observation) :=
  match action with
  | .issue tid af => issue state tid af profile
  | .drain tid => drain state tid profile

def schedule (state : State) (actions : List Action) (profile : Profile := .ownedOnly) :
    Except Fault (State × List Observation) :=
  match actions with
  | [] => .ok (state, [])
  | action :: rest => do
    let head ← step state action profile
    let tail ← schedule head.1 rest profile
    return (tail.1, head.2 :: tail.2)

def Returned (state : State) : Prop := ∀ worker ∈ state.workers, worker.phase = .returned
def Quiescent (state : State) : Prop := ∀ worker ∈ state.workers, worker.pending = []
def Finished (state : State) : Prop := Returned state ∧ Quiescent state

end EDSL.OS.TSO64
