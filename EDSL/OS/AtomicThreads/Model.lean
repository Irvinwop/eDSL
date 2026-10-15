/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics
import EDSL.OS.Threads.Framing

namespace EDSL.OS.AtomicThreads
open X86 AddressSpace

abbrev Context := Threads.Context
abbrev principal := Threads.principal

def prepared (entry : Context) : Context :=
  { entry with
    registers := fun register => if register = .rax then ((entry.registers .rsi).setWidth 32).setWidth 64
      else entry.registers register
    rip := entry.rip + 2 }

def exchanged (entry : Context) (old : BitVec 32) : Context :=
  { entry with
    registers := fun register => if register = .rax then old.setWidth 64 else entry.registers register
    rip := entry.rip + 4 }

inductive Phase where
  | preparing (context : Context)
  | exchanging (context : Context)
  | returning (old : BitVec 32) (context : Context)
  | completed (old : BitVec 32) (context : Context)

structure Start where
  entry : Context
  dataTicket : Ownership.Ticket
  codeTicket : Ownership.Ticket
  stackTicket : Ownership.Ticket

structure Worker where
  parent : Nat
  entry : Context
  returnAddress : Word
  handle : Nat
  codeLoan : Nat
  stackLoan : Nat
  phase : Phase

structure State where
  shared : Atomics.State
  nextThread : Nat
  workers : Nat → Option Worker

def empty (shared : Atomics.State) : State := ⟨shared, 0, fun _ => none⟩

def codeRegion (entry : Context) : Region := ⟨entry.rip, 5⟩
abbrev stackRegion := Threads.stackRegion

def codeMatches (space : Space) (entry : Word) : Bool :=
  decide (entry.toNat + 5 ≤ 2^64) &&
    Threads.byteMatches (toMemory space) entry 0x89 &&
    Threads.byteMatches (toMemory space) (entry + 1) 0xf0 &&
    Threads.byteMatches (toMemory space) (entry + 2) 0x87 &&
    Threads.byteMatches (toMemory space) (entry + 3) 0x07 &&
    Threads.byteMatches (toMemory space) (entry + 4) 0xc3

inductive Fault where
  | atomic (fault : Atomics.Fault)
  | machine (fault : X86.Error)
  | wrongParent
  | identityCollision
  | missingThread
  | notCompleted
  | alreadyCompleted
  | unsupportedCode
  | unexpectedStep
  | creationFailed
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def replace (state : State) (identifier : Nat) (worker : Option Worker) : State :=
  { state with workers := fun query => if query = identifier then worker else state.workers query }

def install (state : State) (shared : Atomics.State) (worker : Worker) : State :=
  { shared := shared, nextThread := state.nextThread + 1
    workers := fun query => if query = state.nextThread then some worker else state.workers query }

/-- The root publishes the input context and acquires two ordinary read loans
plus a distinct actor's atomic handle. Failure exposes no partial resources.
No old data value is read or cached at spawn. -/
def spawn (state : State) (parent : Nat) (start : Start) (available : Bool := true) :
    Except Fault (State × Nat) := do
  if parent ≠ 0 then throw .wrongParent
  if !available then throw .creationFailed
  if (state.workers state.nextThread).isSome then throw .identityCollision
  if !codeMatches state.shared.shared.resources.space start.entry.rip then throw .unsupportedCode
  let target ← (readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp)).mapError Fault.machine
  if !canonical target then throw (.machine (.noncanonicalReturn target))
  let (code, codeId) ← (Atomics.readBorrow state.shared parent start.codeTicket
    (principal state.nextThread) (codeRegion start.entry)).mapError Fault.atomic
  let (stack, stackId) ← (Atomics.readBorrow code parent start.stackTicket
    (principal state.nextThread) (stackRegion start.entry)).mapError Fault.atomic
  let (data, handle) ← (Atomics.issue stack parent start.dataTicket
    (principal state.nextThread) (start.entry.registers .rdi)).mapError Fault.atomic
  return (install state data ⟨parent, start.entry, target, handle, codeId, stackId, .preparing start.entry⟩,
    state.nextThread)

/-- Each selection executes one actual instruction against current shared
cells. The exchange result is retained privately while peer exchanges remain
possible. The returned event is the actual X86.step event, with its actor
identified by this dispatch's thread ID. -/
def dispatch (state : State) (identifier : Nat) : Except Fault (State × Option AtomicEvent) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  match worker.phase with
  | .completed _ _ => throw .alreadyCompleted
  | .preparing context =>
    match ← (decodeAt (context.snapshot state.shared.shared.resources.space)).mapError Fault.machine with
    | .movEaxEsi => pure ()
    | _ => throw .unexpectedStep
    match ← (X86.step (context.snapshot state.shared.shared.resources.space)).mapError Fault.machine with
    | .next actual => return (replace state identifier
        (some { worker with phase := .exchanging (Threads.Context.ofState actual) }), none)
    | _ => throw .unexpectedStep
  | .exchanging context =>
    match ← (decodeAt (context.snapshot state.shared.shared.resources.space)).mapError Fault.machine with
    | .exchangeEaxRdi => pure ()
    | _ => throw .unexpectedStep
    let handle ← (Atomics.authorize state.shared (principal identifier) worker.handle).mapError Fault.atomic
    if context.registers .rdi ≠ handle.address then throw .unexpectedStep
    let (shared, old) ← (Atomics.exchange state.shared (principal identifier) worker.handle
      ((context.registers .rax).setWidth 32)).mapError Fault.atomic
    match ← (X86.step (context.snapshot state.shared.shared.resources.space)).mapError Fault.machine with
    | .atomic event actual =>
      return ({ replace state identifier (some { worker with phase := .returning old (Threads.Context.ofState actual) }) with
        shared := shared }, some event)
    | _ => throw .unexpectedStep
  | .returning old context =>
    match ← (decodeAt (context.snapshot state.shared.shared.resources.space)).mapError Fault.machine with
    | .ret => pure ()
    | _ => throw .unexpectedStep
    match ← (X86.step (context.snapshot state.shared.shared.resources.space)).mapError Fault.machine with
    | .returned actual => return (replace state identifier
        (some { worker with phase := .completed old (Threads.Context.ofState actual) }), none)
    | _ => throw .unexpectedStep

/-- A successful join collects the retained machine result and revokes only
this worker's handle and two loans. Internal release operations are not exposed
as separate environment actions in the worker history. -/
def join (state : State) (parent identifier : Nat) : Except Fault (State × Word) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  if worker.parent ≠ parent then throw .wrongParent
  match worker.phase with
  | .preparing _ | .exchanging _ | .returning _ _ => throw .notCompleted
  | .completed _ context =>
    let data ← (Atomics.close state.shared (principal identifier) worker.handle).mapError Fault.atomic
    let code ← (Atomics.finishLoan data (principal identifier) worker.codeLoan).mapError Fault.atomic
    let stack ← (Atomics.finishLoan code (principal identifier) worker.stackLoan).mapError Fault.atomic
    return ({ replace state identifier none with shared := stack }, context.registers .rax)

def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  let result ← (Atomics.mutate state.shared operation).mapError Fault.atomic
  return ({ state with shared := result.1 }, result.2)

abbrev HasLoan := Threads.HasLoan

def HasHandle (shared : Atomics.State) (identifier handleId : Nat) (address : Word) : Prop :=
  ∃ handle, shared.handles handleId = some handle ∧ handle.actor = principal identifier ∧ handle.address = address

def PhaseValid (entry : Context) (target : Word) : Phase → Prop
  | .preparing context => context = entry
  | .exchanging context => context = prepared entry
  | .returning old context => context = exchanged entry old
  | .completed old context => context = entry.returned old target

structure WorkerValid (shared : Atomics.State) (identifier : Nat) (worker : Worker) : Prop where
  parent : worker.parent = 0
  handle : HasHandle shared identifier worker.handle (worker.entry.registers .rdi)
  code : HasLoan shared.shared identifier worker.codeLoan (codeRegion worker.entry)
  stack : HasLoan shared.shared identifier worker.stackLoan (stackRegion worker.entry)
  distinct : worker.codeLoan ≠ worker.stackLoan
  executable : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip Examples.Compiler.Exchange.bytes
  target : readWord (toMemory shared.shared.resources.space) (worker.entry.registers .rsp) = .ok worker.returnAddress
  canonical : X86.canonical worker.returnAddress = true
  phase : PhaseValid worker.entry worker.returnAddress worker.phase

def WellFormed (state : State) : Prop :=
  Atomics.WellFormed state.shared ∧ ∀ identifier worker, state.workers identifier = some worker →
    identifier < state.nextThread ∧ WorkerValid state.shared identifier worker

/-- The worker's contribution to a swap invariant: its input before XCHG and
the privately retained old word afterwards. -/
def Worker.token (worker : Worker) : BitVec 32 :=
  match worker.phase with
  | .preparing _ | .exchanging _ => (worker.entry.registers .rsi).setWidth 32
  | .returning old _ | .completed old _ => old

def Worker.captured (worker : Worker) : Option (BitVec 32) :=
  match worker.phase with
  | .preparing _ | .exchanging _ => none
  | .returning old _ | .completed old _ => some old

end EDSL.OS.AtomicThreads
