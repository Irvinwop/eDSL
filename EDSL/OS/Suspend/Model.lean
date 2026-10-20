/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO
import EDSL.X86.SyscallReturn

namespace EDSL.OS.Suspend
open X86

/-- A unique invocation and the actual userspace request captured at entry.
Its memory is an entry snapshot, rather than the world to restore at return. -/
structure Saved where
  identifier : Nat
  worker : Nat
  request : SyscallRequest

structure State where
  machine : TSO.State
  nextCall : Nat
  pending : Nat → Option Saved

inductive Fault where
  | underlying (fault : TSO.Fault)
  | pendingStores | noPending | staleCall | wrongWorker
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

inductive Action where
  | issue (worker : Nat)
  | drain (worker : Nat)
  | resume (worker invocation : Nat) (raw flags rcx r11 : Word)
  | idle
  deriving DecidableEq, Repr

/-- Entry retires one SYSCALL. Parked selections, resumption, independent
storage propagation and idle are distinct observations. -/
inductive Observation where
  | machine (observation : TSO.Observation)
  | entered (worker invocation : Nat)
  | parked (worker invocation : Nat)
  | resumed (worker invocation : Nat) (raw : Word)
  | idle
  deriving DecidableEq, Repr

def initial (machine : TSO.State) : State := ⟨machine, 0, fun _ => none⟩

/-- Entry retains the exact machine state until return; the pending map then
gates further user execution. The saved continuation comes from execution. -/
def capture (state : State) (identifier : Nat) (request : SyscallRequest) : State :=
  { state with nextCall := state.nextCall + 1
               pending := fun query => if query = identifier then
                 some ⟨state.nextCall, identifier, request⟩ else state.pending query }

/-- Decode and execute remain architectural operations. This first syscall
profile explicitly rejects a nonempty own FIFO, without flushing or discarding
it. Ordinary instruction execution retains the underlying TSO definition. -/
def execute (state : State) (identifier : Nat) (worker : TSO.Worker) (instruction : Instruction) :
    Except Fault (State × Observation) := do
  if instruction = .syscall then
    if !worker.buffer.isEmpty then throw .pendingStores
    match ← (executeInstruction (TSO.sharedState state.machine worker) instruction).mapError
        (fun fault => Fault.underlying (.machine fault)) with
    | .syscall request =>
      return (capture state identifier request, .entered identifier state.nextCall)
    | _ => throw (.underlying .unexpectedResult)
  else
    let result ← (TSO.execute state.machine identifier worker instruction).mapError Fault.underlying
    return ({ state with machine := result.1 }, .machine result.2)

def issue (state : State) (identifier : Nat) : Except Fault (State × Observation) := do
  let some worker := state.machine.workers[identifier]? | throw (.underlying .missingThread)
  if worker.returned then throw (.underlying .alreadyReturned)
  if let some saved := state.pending identifier then
    return (state, .parked identifier saved.identifier)
  let instruction ← (decodeAt (TSO.sharedState state.machine worker)).mapError
    (fun fault => Fault.underlying (.machine fault))
  execute state identifier worker instruction

def drain (state : State) (identifier : Nat) : Except Fault (State × Observation) := do
  let result ← (TSO.drain state.machine identifier).mapError Fault.underlying
  return ({ state with machine := result.1 }, .machine result.2)

/-- External completion supplies only private return fields. The scheduler
itself supplies current RAM, and consumes the exact pending invocation once.
This is a service-neutral mechanism, not a Linux service completion guarantee. -/
def resume (state : State) (identifier invocation : Nat) (raw flags rcx r11 : Word) : Except Fault State := do
  let some worker := state.machine.workers[identifier]? | throw (.underlying .missingThread)
  if worker.returned then throw (.underlying .alreadyReturned)
  let some saved := state.pending identifier | throw .noPending
  if saved.identifier ≠ invocation then throw .staleCall
  if saved.worker ≠ identifier then throw .wrongWorker
  if !worker.buffer.isEmpty then throw .pendingStores
  let output := X86.resumeAt saved.request state.machine.memory raw flags rcx r11
  return { state with
    machine := TSO.install state.machine identifier state.machine.memory (.ofState output) false []
    pending := fun query => if query = identifier then none else state.pending query }

def step (state : State) : Action → Except Fault (State × Observation)
  | .issue identifier => issue state identifier
  | .drain identifier => drain state identifier
  | .resume identifier invocation raw flags rcx r11 => do
    let after ← resume state identifier invocation raw flags rcx r11
    return (after, .resumed identifier invocation raw)
  | .idle => .ok (state, .idle)

def schedule (state : State) : List Action → Except Fault (State × List Observation)
  | [] => .ok (state, [])
  | action :: rest => do
    let head ← step state action
    let tail ← schedule head.1 rest
    return (tail.1, head.2 :: tail.2)

def retiredCount (observations : List Observation) : Nat :=
  (observations.map fun observation => match observation with
    | .machine (.retired _ _) | .entered _ _ => 1
    | _ => 0).sum

def atomicEvents (observations : List Observation) : List (Nat × AtomicEvent) :=
  observations.filterMap fun observation => match observation with
    | .machine (.retired identifier (some event)) => some (identifier, event)
    | _ => none

def Returned (state : State) : Prop := TSO.Returned state.machine

def Finished (state : State) : Prop :=
  TSO.Finished state.machine ∧ ∀ identifier, state.pending identifier = none

end EDSL.OS.Suspend
