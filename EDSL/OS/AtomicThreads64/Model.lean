/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.Routine
import EDSL.OS.Atomics64.History
import EDSL.OS.Threads.Machine

namespace EDSL.OS.AtomicThreads64
open X86 AddressSpace

abbrev Context := Threads.Context
abbrev principal := Threads.principal

/-- Full64 LOCK OR preserves every register, including RAX. -/
def applied (entry : Context) (value : Word) (af : Bool) : Context :=
  { entry with
    rip := entry.rip + 4
    flags := X86.Sequential.logicalFlags64 entry.flags value af }

/-- Near RET updates only RSP and RIP; it never writes an audit value to RAX. -/
def returned (context : Context) (target : Word) : Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8
      else context.registers register
    rip := target }

inductive Phase where
  | applying (context : Context)
  | returning (event : Atomics64.Event) (context : Context)
  | completed (event : Atomics64.Event) (context : Context)

/-- The cell has already been registered. Spawn delegates a distinct actor
handle; it does not create an overlapping registration or cache the word. -/
structure Start where
  entry : Context
  cell : Atomics64.CellId64
  codeTicket : Ownership.Ticket
  stackTicket : Ownership.Ticket

structure Worker where
  parent : Nat
  entry : Context
  cell : Atomics64.CellId64
  returnAddress : Word
  handle : Atomics64.HandleId64
  codeLoan : Nat
  stackLoan : Nat
  phase : Phase

structure State where
  shared : Atomics64.State
  nextThread : Nat
  workers : Nat → Option Worker

def empty (shared : Atomics64.State) : State := ⟨shared, 0, fun _ => none⟩
def codeRegion (entry : Context) : Region := ⟨entry.rip, 5⟩
abbrev stackRegion := Threads.stackRegion

def codeMatches (space : Space) (entry : Word) : Bool :=
  decide (entry.toNat + 5 ≤ 2^64) &&
    Threads.byteMatches (toMemory space) entry 0xf0 &&
    Threads.byteMatches (toMemory space) (entry + 1) 0x48 &&
    Threads.byteMatches (toMemory space) (entry + 2) 0x09 &&
    Threads.byteMatches (toMemory space) (entry + 3) 0x37 &&
    Threads.byteMatches (toMemory space) (entry + 4) 0xc3

inductive Fault where
  | atomic (fault : Atomics64.Fault)
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

def install (state : State) (shared : Atomics64.State) (worker : Worker) : State :=
  { shared := shared, nextThread := state.nextThread + 1
    workers := fun query => if query = state.nextThread then some worker else state.workers query }

/-- Checked functional transaction. Failure exposes no partial handle or loan.
The root publishes code and caller slot and delegates one live typed cell. -/
def spawn (state : State) (parent : Nat) (start : Start) (available : Bool := true) :
    Except Fault (State × Nat) := do
  if parent ≠ 0 then throw .wrongParent
  if !available then throw .creationFailed
  if (state.workers state.nextThread).isSome then throw .identityCollision
  if !codeMatches state.shared.legacy.shared.resources.space start.entry.rip then throw .unsupportedCode
  let cell ← (Atomics64.authorizeCell state.shared parent start.cell).mapError Fault.atomic
  if start.entry.registers .rdi ≠ cell.address then throw .unexpectedStep
  let target ← (readWord (toMemory state.shared.legacy.shared.resources.space)
    (start.entry.registers .rsp)).mapError Fault.machine
  if !canonical target then throw (.machine (.noncanonicalReturn target))
  let (code, codeId) ← (Atomics64.readBorrow state.shared parent start.codeTicket
    (principal state.nextThread) (codeRegion start.entry)).mapError Fault.atomic
  let (stack, stackId) ← (Atomics64.readBorrow code parent start.stackTicket
    (principal state.nextThread) (stackRegion start.entry)).mapError Fault.atomic
  let (data, handle) ← (Atomics64.issue stack parent start.cell
    (principal state.nextThread)).mapError Fault.atomic
  return (install state data ⟨parent, start.entry, start.cell, target, handle,
    codeId, stackId, .applying start.entry⟩, state.nextThread)

/-- Exactly one actual instruction per selection, from a fresh projection of
CURRENT shared RAM. An arbitrary supplied AF choice is used for this dispatch.
The full event is retained as audit data, not a fetched-old ABI return value. -/
def dispatch (state : State) (identifier : Nat) (af : Bool) :
    Except Fault (State × Option Atomics64.Event) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  match worker.phase with
  | .completed _ _ => throw .alreadyCompleted
  | .applying context =>
    match ← (X86.LockedLogical64.decodeAt (context.snapshot state.shared.legacy.shared.resources.space)).mapError Fault.machine with
    | .orRdiRsi => pure ()
    | _ => throw .unexpectedStep
    let selected ← (Atomics64.authorize state.shared (principal identifier) worker.handle).mapError Fault.atomic
    if context.registers .rdi ≠ selected.2.address then throw .unexpectedStep
    let (shared, event) ← (Atomics64.logicalDiscard state.shared (principal identifier)
      worker.handle (context.registers .rsi)).mapError Fault.atomic
    match ← (X86.LockedLogical64.step af (context.snapshot state.shared.legacy.shared.resources.space)).mapError Fault.machine with
    | ⟨.atomic64 label actual, _⟩ =>
      if label ≠ event.logical then throw .unexpectedStep
      return ({ replace state identifier (some { worker with
        phase := .returning event (Threads.Context.ofState actual) }) with shared := shared }, some event)
    | _ => throw .unexpectedStep
  | .returning event context =>
    match ← (X86.LockedLogical64.decodeAt (context.snapshot state.shared.legacy.shared.resources.space)).mapError Fault.machine with
    | .ret => pure ()
    | _ => throw .unexpectedStep
    match ← (X86.LockedLogical64.step af (context.snapshot state.shared.legacy.shared.resources.space)).mapError Fault.machine with
    | ⟨.returned actual, _⟩ => return (replace state identifier
        (some { worker with phase := .completed event (Threads.Context.ofState actual) }), none)
    | _ => throw .unexpectedStep

/-- JOIN revokes only this worker's handle and its two loans. The returned
context has no RAM field, so join cannot restore an earlier shared snapshot. -/
def join (state : State) (parent identifier : Nat) : Except Fault (State × Context) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  if worker.parent ≠ parent then throw .wrongParent
  match worker.phase with
  | .applying _ | .returning _ _ => throw .notCompleted
  | .completed _ context =>
    let data ← (Atomics64.close state.shared (principal identifier) worker.handle).mapError Fault.atomic
    let code ← (Atomics64.finishLoan data (principal identifier) worker.codeLoan).mapError Fault.atomic
    let stack ← (Atomics64.finishLoan code (principal identifier) worker.stackLoan).mapError Fault.atomic
    return ({ replace state identifier none with shared := stack }, context)

/-- Managed environment changes retain all worker resources. Raw close,
finishLoan and raw lower-layer histories are not managed environment actions. -/
def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  let result ← (Atomics64.mutate state.shared operation).mapError Fault.atomic
  return ({ state with shared := result.1 }, result.2)

/-- A live or completed worker's pinned handle makes retirement fail. After
all its handles are joined, explicit root retirement ends the reservation. -/
def retire (state : State) (owner : Nat) (cell : Atomics64.CellId64) : Except Fault State := do
  if owner ≠ 0 then throw .wrongParent
  let shared ← (Atomics64.retire state.shared owner cell).mapError Fault.atomic
  return { state with shared := shared }

abbrev HasLoan := Threads.HasLoan

def HasHandle (shared : Atomics64.State) (identifier : Nat) (handleId : Atomics64.HandleId64)
    (cellId : Atomics64.CellId64) (address : Word) : Prop :=
  ∃ handle cell, shared.handles handleId = some handle ∧ handle.actor = principal identifier ∧
    handle.cell = cellId ∧ shared.cells cellId = some cell ∧ cell.address = address

def PhaseValid (entry : Context) (target : Word) : Phase → Prop
  | .applying context => context = entry
  | .returning event context => ∃ af, context = applied entry event.logical.event.after af
  | .completed event context => ∃ af,
      context = returned (applied entry event.logical.event.after af) target

/-- Handle, complete cell identity and both loans stay pinned in every phase,
including completed. Only successful JOIN discharges these obligations. -/
structure WorkerValid (shared : Atomics64.State) (identifier : Nat) (worker : Worker) : Prop where
  parent : worker.parent = 0
  handle : HasHandle shared identifier worker.handle worker.cell (worker.entry.registers .rdi)
  code : HasLoan shared.legacy.shared identifier worker.codeLoan (codeRegion worker.entry)
  stack : HasLoan shared.legacy.shared identifier worker.stackLoan (stackRegion worker.entry)
  distinct : worker.codeLoan ≠ worker.stackLoan
  executable : CodeAt (toMemory shared.legacy.shared.resources.space) worker.entry.rip Atomics64.Routine.bytes
  target : readWord (toMemory shared.legacy.shared.resources.space)
    (worker.entry.registers .rsp) = .ok worker.returnAddress
  canonical : X86.canonical worker.returnAddress = true
  phase : PhaseValid worker.entry worker.returnAddress worker.phase

def WellFormed (state : State) : Prop :=
  Atomics64.WellFormed state.shared ∧ ∀ identifier worker, state.workers identifier = some worker →
    identifier < state.nextThread ∧ WorkerValid state.shared identifier worker

def Worker.captured (worker : Worker) : Option Atomics64.Event :=
  match worker.phase with
  | .applying _ => none
  | .returning event _ | .completed event _ => some event

end EDSL.OS.AtomicThreads64
