/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MachineThreads
import EDSL.X86.StoreBuffer

namespace EDSL.OS.TSO
open X86

structure Worker where
  context : Threads.Context
  returned : Bool
  buffer : StoreBuffer.Buffer

structure State where
  memory : X86.Memory
  workers : List Worker

inductive Action where
  | issue (identifier : Nat)
  | drain (identifier : Nat)
  deriving DecidableEq, Repr

/-- Drains and blocked locked instructions are not retired user instructions. -/
inductive Observation where
  | retired (identifier : Nat) (event : Option AtomicEvent)
  | blocked (identifier : Nat)
  | drained (identifier : Nat) (store : StoreBuffer.Store)
  deriving DecidableEq, Repr

inductive Fault where
  | machine (error : X86.Error)
  | missingThread | alreadyReturned | emptyBuffer | syscallBoundary
  | unsupportedAlignment (address : Word)
  | executableWrite (address : Word)
  | unexpectedResult
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def sharedState (state : State) (worker : Worker) : X86.State :=
  MachineThreads.contextState worker.context state.memory

def localState (state : State) (worker : Worker) : X86.State :=
  MachineThreads.contextState worker.context (StoreBuffer.view state.memory worker.buffer)

def locked : Instruction → Bool
  | .exchangeEaxRdi | .fetchAddEaxRdi => true
  | _ => false

def pendingStore (context : Threads.Context) : Instruction → Option StoreBuffer.Store
  | .storeEsiRdi => some ⟨context.registers .rdi, (context.registers .rsi).setWidth 32⟩
  | .storeEaxRsi => some ⟨context.registers .rsi, (context.registers .rax).setWidth 32⟩
  | _ => none

def loadAddress (context : Threads.Context) : Instruction → Option Word
  | .loadEaxRdi => some (context.registers .rdi)
  | .loadEaxRsi => some (context.registers .rsi)
  | _ => none

/-- This fixed-code profile rejects writes to any executable destination byte.
Permissions and mappings cannot change while this scheduler runs. -/
def dataOnly (memory : Memory) (address : Word) : Bool :=
  !(memory.executable address || memory.executable (address + 1) ||
    memory.executable (address + 2) || memory.executable (address + 3))

def install (state : State) (identifier : Nat) (memory : Memory) (context : Threads.Context)
    (returned : Bool) (buffer : StoreBuffer.Buffer) : State :=
  ⟨memory, state.workers.set identifier ⟨context, returned, buffer⟩⟩

/-- Fetch uses shared code. Ordinary stores retire into the FIFO, ordinary
loads forward from the caller's pending bytes, and locked operations execute
indivisibly on shared RAM only after that caller's FIFO is empty. No protocol
or expected-code check selects the instruction. -/
def execute (state : State) (identifier : Nat) (worker : Worker) (instruction : Instruction) :
    Except Fault (State × Observation) := do
  match pendingStore worker.context instruction with
  | some store =>
    if !atomicAddressable store.address then throw (.unsupportedAlignment store.address)
    if !dataOnly state.memory store.address then throw (.executableWrite store.address)
    match ← (executeInstruction (sharedState state worker) instruction).mapError Fault.machine with
    | .next output =>
      return (install state identifier state.memory (.ofState output) false
        (StoreBuffer.enqueue worker.buffer store), .retired identifier none)
    | _ => throw .unexpectedResult
  | none =>
    if locked instruction then
      if !worker.buffer.isEmpty then return (state, .blocked identifier)
      if !dataOnly state.memory (worker.context.registers .rdi) then
        throw (.executableWrite (worker.context.registers .rdi))
      match ← (executeInstruction (sharedState state worker) instruction).mapError Fault.machine with
      | .atomic event output =>
        return (install state identifier output.memory (.ofState output) false [], .retired identifier (some event))
      | _ => throw .unexpectedResult
    else
      if let some address := loadAddress worker.context instruction then
        if !atomicAddressable address then throw (.unsupportedAlignment address)
      match ← (executeInstruction (localState state worker) instruction).mapError Fault.machine with
      | .next output =>
        return (install state identifier state.memory (.ofState output) false worker.buffer, .retired identifier none)
      | .returned output =>
        return (install state identifier state.memory (.ofState output) true worker.buffer, .retired identifier none)
      | .syscall _ => throw .syscallBoundary
      | .atomic _ _ => throw .unexpectedResult

def issue (state : State) (identifier : Nat) : Except Fault (State × Observation) := do
  let some worker := state.workers[identifier]? | throw .missingThread
  if worker.returned then throw .alreadyReturned
  let instruction ← (decodeAt (sharedState state worker)).mapError Fault.machine
  execute state identifier worker instruction

/-- The oldest write publishes; BuffersValid or initial reachability supplies
its aligned fixed-code profile. Retired callers may still have pending writes.
This action does not execute or advance their context. -/
def drain (state : State) (identifier : Nat) : Except Fault (State × Observation) := do
  let some worker := state.workers[identifier]? | throw .missingThread
  let head :: tail := worker.buffer | throw .emptyBuffer
  let memory ← (storeDWord state.memory head.address head.value).mapError Fault.machine
  return (install state identifier memory worker.context worker.returned tail, .drained identifier head)

def step (state : State) : Action → Except Fault (State × Observation)
  | .issue identifier => issue state identifier
  | .drain identifier => drain state identifier

def schedule (state : State) : List Action → Except Fault (State × List Observation)
  | [] => .ok (state, [])
  | action :: rest => do
    let head ← step state action
    let tail ← schedule head.1 rest
    return (tail.1, head.2 :: tail.2)

def retiredCount (observations : List Observation) : Nat :=
  (observations.filter fun observation => match observation with | .retired _ _ => true | _ => false).length

def atomicEvents (observations : List Observation) : List (Nat × AtomicEvent) :=
  observations.filterMap fun observation => match observation with
    | .retired identifier (some event) => some (identifier, event)
    | _ => none

def Returned (state : State) : Prop := ∀ worker ∈ state.workers, worker.returned = true

def Quiescent (state : State) : Prop := ∀ worker ∈ state.workers, worker.buffer = []

/-- Observing RET alone does not establish publication of ordinary stores. -/
def Finished (state : State) : Prop := Returned state ∧ Quiescent state

def initial (state : MachineThreads.State) : State :=
  ⟨state.memory, state.workers.map fun worker => ⟨worker.context, worker.returned, []⟩⟩

end EDSL.OS.TSO
