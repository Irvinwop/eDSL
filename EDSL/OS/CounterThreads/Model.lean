/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads.Framing
import EDSL.X86.CodeCheck

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

abbrev Context := Threads.Context
abbrev principal := Threads.principal

/-- JRCXZ done; MOV EAX,1; LOCK XADD [RDI],EAX; LOOP body;
MOV EAX,0; RET. RCX supplies the 64-bit iteration count. -/
def bytes : List Byte :=
  [0xe3, 0x0b, 0xb8, 1, 0, 0, 0, 0xf0, 0x0f, 0xc1, 0x07, 0xe2, 0xf5, 0xb8, 0, 0, 0, 0, 0xc3]

inductive Phase where
  | entry | preparing | adding | backedge | finishing | returning | completed
  deriving DecidableEq, Repr

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
  context : Context

structure State where
  shared : Atomics.State
  nextThread : Nat
  workers : Nat → Option Worker

def empty (shared : Atomics.State) : State := ⟨shared, 0, fun _ => none⟩
def codeRegion (entry : Context) : Region := ⟨entry.rip, bytes.length⟩
abbrev stackRegion := Threads.stackRegion

def PrivateValid (worker : Worker) : Prop :=
  worker.context.registers .rdi = worker.entry.registers .rdi ∧
  (worker.context.registers .rcx).toNat ≤ (worker.entry.registers .rcx).toNat ∧
  (match worker.phase with
    | .completed => worker.context.registers .rsp = worker.entry.registers .rsp + 8
    | _ => worker.context.registers .rsp = worker.entry.registers .rsp) ∧
  match worker.phase with
  | .entry => worker.context.rip = worker.entry.rip ∧ worker.context.registers .rcx = worker.entry.registers .rcx
  | .preparing => worker.context.rip = worker.entry.rip + 2 ∧ worker.context.registers .rcx ≠ 0
  | .adding => worker.context.rip = worker.entry.rip + 7 ∧ worker.context.registers .rcx ≠ 0 ∧ worker.context.registers .rax = 1
  | .backedge => worker.context.rip = worker.entry.rip + 11 ∧ worker.context.registers .rcx ≠ 0
  | .finishing => worker.context.rip = worker.entry.rip + 13 ∧ worker.context.registers .rcx = 0
  | .returning => worker.context.rip = worker.entry.rip + 18 ∧ worker.context.registers .rcx = 0 ∧ worker.context.registers .rax = 0
  | .completed => worker.context.rip = worker.returnAddress ∧ worker.context.registers .rcx = 0 ∧ worker.context.registers .rax = 0

instance (worker : Worker) : Decidable (PrivateValid worker) := by
  unfold PrivateValid
  cases worker.phase <;> infer_instance

abbrev HasLoan := Threads.HasLoan
abbrev HasHandle := AtomicThreads.HasHandle

structure WorkerValid (shared : Atomics.State) (identifier : Nat) (worker : Worker) : Prop where
  parent : worker.parent = 0
  handle : HasHandle shared identifier worker.handle (worker.entry.registers .rdi)
  code : HasLoan shared.shared identifier worker.codeLoan (codeRegion worker.entry)
  stack : HasLoan shared.shared identifier worker.stackLoan (stackRegion worker.entry)
  distinct : worker.codeLoan ≠ worker.stackLoan
  executable : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip bytes
  target : readWord (toMemory shared.shared.resources.space) (worker.entry.registers .rsp) = .ok worker.returnAddress
  canonical : X86.canonical worker.returnAddress = true
  privateContext : PrivateValid worker

def WellFormed (state : State) : Prop :=
  Atomics.WellFormed state.shared ∧ ∀ identifier worker, state.workers identifier = some worker →
    identifier < state.nextThread ∧ WorkerValid state.shared identifier worker

inductive Fault where
  | atomic (fault : Atomics.Fault)
  | machine (fault : X86.Error)
  | wrongParent | creationFailed | identityCollision | missingThread
  | unsupportedCode | unexpectedStep | invalidContext | alreadyCompleted | notCompleted
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def replace (state : State) (identifier : Nat) (worker : Option Worker) : State :=
  { state with workers := fun query => if query = identifier then worker else state.workers query }

def install (state : State) (shared : Atomics.State) (worker : Worker) : State :=
  { shared := shared, nextThread := state.nextThread + 1
    workers := fun query => if query = state.nextThread then some worker else state.workers query }

def spawn (state : State) (parent : Nat) (start : Start) (available : Bool := true) : Except Fault (State × Nat) := do
  if parent ≠ 0 then throw .wrongParent
  if !available then throw .creationFailed
  if (state.workers state.nextThread).isSome then throw .identityCollision
  if !checkCode (toMemory state.shared.shared.resources.space) start.entry.rip bytes then throw .unsupportedCode
  let target ← (readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp)).mapError Fault.machine
  if !canonical target then throw (.machine (.noncanonicalReturn target))
  let (code, codeId) ← (Atomics.readBorrow state.shared parent start.codeTicket (principal state.nextThread) (codeRegion start.entry)).mapError Fault.atomic
  let (stack, stackId) ← (Atomics.readBorrow code parent start.stackTicket (principal state.nextThread) (stackRegion start.entry)).mapError Fault.atomic
  let (data, handle) ← (Atomics.issue stack parent start.dataTicket (principal state.nextThread) (start.entry.registers .rdi)).mapError Fault.atomic
  return (install state data ⟨parent, start.entry, target, handle, codeId, stackId, .entry, start.entry⟩, state.nextThread)

def expected : Phase → Option Instruction
  | .entry => some (.jrcxz 0x0b)
  | .preparing => some (.mov32 .rax 1)
  | .adding => some .fetchAddEaxRdi
  | .backedge => some (.loopRcx 0xf5)
  | .finishing => some (.mov32 .rax 0)
  | .returning => some .ret
  | .completed => none

def nextPhase (phase : Phase) (context : Context) : Phase :=
  match phase with
  | .entry | .backedge => if context.registers .rcx = 0 then .finishing else .preparing
  | .preparing => .adding
  | .adding => .backedge
  | .finishing => .returning
  | .returning | .completed => .completed

structure Advance where
  shared : Atomics.State
  worker : Worker
  event : Option AtomicEvent

def checkedAdvance (shared : Atomics.State) (worker : Worker) (context : Context) (event : Option AtomicEvent) : Except Fault Advance := do
  let after := { worker with phase := nextPhase worker.phase context, context := context }
  if !decide (PrivateValid after) then throw .invalidContext
  return ⟨shared, after, event⟩

/-- One actual decoded instruction on current shared cells. Private checks
reject malformed contexts; atomic updates retain checked handle authority. -/
def advance (state : State) (identifier : Nat) (worker : Worker) : Except Fault Advance := do
  let some instruction := expected worker.phase | throw .alreadyCompleted
  let actual ← (decodeAt (worker.context.snapshot state.shared.shared.resources.space)).mapError Fault.machine
  if actual ≠ instruction then throw .unexpectedStep
  let outcome ← (X86.step (worker.context.snapshot state.shared.shared.resources.space)).mapError Fault.machine
  match worker.phase, outcome with
  | .adding, .atomic event context =>
    let handle ← (Atomics.authorize state.shared (principal identifier) worker.handle).mapError Fault.atomic
    if worker.context.registers .rdi ≠ handle.address then throw .unexpectedStep
    if (worker.context.registers .rax).setWidth 32 ≠ 1 then throw .unexpectedStep
    let (shared, _) ← (Atomics.fetchAdd state.shared (principal identifier) worker.handle 1).mapError Fault.atomic
    checkedAdvance shared worker (Threads.Context.ofState context) (some event)
  | .returning, .returned context => checkedAdvance state.shared worker (Threads.Context.ofState context) none
  | .entry, .next context | .preparing, .next context | .backedge, .next context | .finishing, .next context =>
    checkedAdvance state.shared worker (Threads.Context.ofState context) none
  | _, _ => throw .unexpectedStep

def dispatch (state : State) (identifier : Nat) : Except Fault (State × Option AtomicEvent) := do
  let some worker := state.workers identifier | throw .missingThread
  let result ← advance state identifier worker
  return ({ replace state identifier (some result.worker) with shared := result.shared }, result.event)

def join (state : State) (parent identifier : Nat) : Except Fault (State × Word) := do
  let some worker := state.workers identifier | throw .missingThread
  if worker.parent ≠ parent then throw .wrongParent
  if worker.phase ≠ .completed then throw .notCompleted
  let data ← (Atomics.close state.shared (principal identifier) worker.handle).mapError Fault.atomic
  let code ← (Atomics.finishLoan data (principal identifier) worker.codeLoan).mapError Fault.atomic
  let stack ← (Atomics.finishLoan code (principal identifier) worker.stackLoan).mapError Fault.atomic
  return ({ replace state identifier none with shared := stack }, worker.context.registers .rax)

def mutate (state : State) (operation : Ownership.Mutation) : Except Fault (State × Option Ownership.Ticket) := do
  let result ← (Atomics.mutate state.shared operation).mapError Fault.atomic
  return ({ state with shared := result.1 }, result.2)

/-- Remaining actual user instructions; no fairness or elapsed-time assumption
is encoded in this variant. -/
def Worker.remaining (worker : Worker) : Nat :=
  let count := (worker.context.registers .rcx).toNat
  match worker.phase with
  | .entry => 3 * count + 3
  | .preparing => 3 * count + 2
  | .adding => 3 * count + 1
  | .backedge => 3 * (count - 1) + 3
  | .finishing => 2
  | .returning => 1
  | .completed => 0

def Worker.performed (worker : Worker) : Nat :=
  (worker.entry.registers .rcx).toNat - ((worker.context.registers .rcx).toNat -
    if worker.phase = .backedge then 1 else 0)

end EDSL.OS.CounterThreads
