/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Borrowing

namespace EDSL.OS.Threads
open X86 AddressSpace

/-- Private user context. Shared memory is projected afresh at each dispatch. -/
structure Context where
  registers : Register → Word
  rip : Word
  flags : Word

def Context.snapshot (context : Context) (space : Space) : X86.State :=
  ⟨context.registers, context.rip, context.flags, toMemory space⟩

def Context.ofState (state : X86.State) : Context := ⟨state.registers, state.rip, state.flags⟩

def Context.loaded (context : Context) (value : BitVec 32) : Context :=
  { context with
    registers := fun register => if register = .rax then value.setWidth 64 else context.registers register
    rip := context.rip + 2 }

def Context.returned (context : Context) (value : BitVec 32) (returnAddress : Word) : Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8
      else if register = .rax then value.setWidth 64 else context.registers register
    rip := returnAddress }

inductive Phase where
  | loading (context : Context)
  | returning (context : Context)
  | completed (context : Context)

structure Start where
  entry : Context
  dataTicket : Ownership.Ticket
  codeTicket : Ownership.Ticket
  stackTicket : Ownership.Ticket

structure Worker where
  parent : Nat
  entry : Context
  value : BitVec 32
  returnAddress : Word
  dataLoan : Nat
  codeLoan : Nat
  stackLoan : Nat
  phase : Phase

structure State where
  shared : Borrowing.State
  nextThread : Nat
  workers : Nat → Option Worker

def empty (shared : Borrowing.State) : State := ⟨shared, 0, fun _ => none⟩

def principal (identifier : Nat) : Nat := identifier + 1

def dataRegion (entry : Context) : Region := ⟨entry.registers .rdi, 4⟩
def codeRegion (entry : Context) : Region := ⟨entry.rip, 3⟩
def stackRegion (entry : Context) : Region := ⟨entry.registers .rsp, 8⟩

def byteMatches (memory : Memory) (address : Word) (byte : Byte) : Bool :=
  match fetchByte memory address with
  | .error _ => false
  | .ok actual => decide (actual = byte)

def codeMatches (space : Space) (entry : Word) : Bool :=
  decide (entry.toNat + 3 ≤ 2^64) && byteMatches (toMemory space) entry 0x8b &&
    byteMatches (toMemory space) (entry + 1) 0x07 && byteMatches (toMemory space) (entry + 2) 0xc3

inductive Fault where
  | borrowing (fault : Borrowing.Fault)
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

def install (state : State) (shared : Borrowing.State) (worker : Worker) : State :=
  { shared := shared, nextThread := state.nextThread + 1
    workers := fun query => if query = state.nextThread then some worker else state.workers query }

/-- Abstract creation failure exposes no partially issued loan or thread state.
The first profile has a root manager (principal 0), no nested spawn or detach. -/
def spawn (state : State) (parent : Nat) (start : Start) (available : Bool := true) :
    Except Fault (State × Nat) := do
  if parent ≠ 0 then throw .wrongParent
  if !available then throw .creationFailed
  if (state.workers state.nextThread).isSome then throw .identityCollision
  if !codeMatches state.shared.resources.space start.entry.rip then throw .unsupportedCode
  let value ← (loadDWord (toMemory state.shared.resources.space) (start.entry.registers .rdi)).mapError Fault.machine
  let target ← (readWord (toMemory state.shared.resources.space) (start.entry.registers .rsp)).mapError Fault.machine
  if !canonical target then throw (.machine (.noncanonicalReturn target))
  let (data, dataId) ← (Borrowing.readBorrow state.shared parent start.dataTicket
    (principal state.nextThread) (dataRegion start.entry)).mapError Fault.borrowing
  let (code, codeId) ← (Borrowing.readBorrow data parent start.codeTicket
    (principal state.nextThread) (codeRegion start.entry)).mapError Fault.borrowing
  let (stack, stackId) ← (Borrowing.readBorrow code parent start.stackTicket
    (principal state.nextThread) (stackRegion start.entry)).mapError Fault.borrowing
  let worker : Worker := ⟨parent, start.entry, value, target, dataId, codeId, stackId, .loading start.entry⟩
  return (install state stack worker, state.nextThread)

/-- Executes exactly one real machine instruction against current shared cells.
The supported workload is checked load/RET; no birth-memory snapshot is stored. -/
def dispatch (state : State) (identifier : Nat) : Except Fault State := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  match worker.phase with
  | .completed _ => throw .alreadyCompleted
  | .loading context =>
    match ← (decodeAt (context.snapshot state.shared.resources.space)).mapError Fault.machine with
    | .loadEaxRdi => pure ()
    | _ => throw .unexpectedStep
    match ← (X86.step (context.snapshot state.shared.resources.space)).mapError Fault.machine with
    | .next actual => return replace state identifier (some { worker with phase := .returning (.ofState actual) })
    | _ => throw .unexpectedStep
  | .returning context =>
    match ← (decodeAt (context.snapshot state.shared.resources.space)).mapError Fault.machine with
    | .ret => pure ()
    | _ => throw .unexpectedStep
    match ← (X86.step (context.snapshot state.shared.resources.space)).mapError Fault.machine with
    | .returned actual => return replace state identifier (some { worker with phase := .completed (.ofState actual) })
    | _ => throw .unexpectedStep

/-- Join returns retained machine RAX, then revokes precisely this worker's
three internal loans. Premature join returns no changed resource state. -/
def join (state : State) (parent identifier : Nat) : Except Fault (State × Word) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  if worker.parent ≠ parent then throw .wrongParent
  match worker.phase with
  | .loading _ | .returning _ => throw .notCompleted
  | .completed context =>
    let data ← (Borrowing.finishLoan state.shared (principal identifier) worker.dataLoan).mapError Fault.borrowing
    let code ← (Borrowing.finishLoan data (principal identifier) worker.codeLoan).mapError Fault.borrowing
    let stack ← (Borrowing.finishLoan code (principal identifier) worker.stackLoan).mapError Fault.borrowing
    return ({ replace state identifier none with shared := stack }, context.registers .rax)

/-- External managed mutations keep all worker loans; arbitrary finishLoan is
not an environment transition of this thread system. -/
def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  let result ← (Borrowing.mutate state.shared operation).mapError Fault.borrowing
  return ({ state with shared := result.1 }, result.2)

/-- A worker holds exact stored loans for data, code and return stack. -/
def HasLoan (shared : Borrowing.State) (identifier loanId : Nat) (region : Region) : Prop :=
  ∃ loan, shared.loans loanId = some loan ∧ loan.borrower = principal identifier ∧ loan.region = region

def WorkerValid (shared : Borrowing.State) (identifier : Nat) (worker : Worker) : Prop :=
  worker.parent = 0 ∧
  HasLoan shared identifier worker.dataLoan (dataRegion worker.entry) ∧
  HasLoan shared identifier worker.codeLoan (codeRegion worker.entry) ∧
  HasLoan shared identifier worker.stackLoan (stackRegion worker.entry) ∧
  worker.dataLoan ≠ worker.codeLoan ∧ worker.dataLoan ≠ worker.stackLoan ∧ worker.codeLoan ≠ worker.stackLoan ∧
  CodeAt (toMemory shared.resources.space) worker.entry.rip Examples.Compiler.MemoryOps.loadBytes ∧
  loadDWord (toMemory shared.resources.space) (worker.entry.registers .rdi) = .ok worker.value ∧
  readWord (toMemory shared.resources.space) (worker.entry.registers .rsp) = .ok worker.returnAddress ∧
  canonical worker.returnAddress = true ∧
  match worker.phase with
  | .loading context => context = worker.entry
  | .returning context => context = worker.entry.loaded worker.value
  | .completed context => context = worker.entry.returned worker.value worker.returnAddress

def WellFormed (state : State) : Prop :=
  Borrowing.WellFormed state.shared ∧
  ∀ identifier worker, state.workers identifier = some worker →
    identifier < state.nextThread ∧ WorkerValid state.shared identifier worker

end EDSL.OS.Threads
