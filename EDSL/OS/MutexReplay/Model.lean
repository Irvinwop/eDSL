/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Step
import EDSL.OS.Threads.Model
import EDSL.X86.CodeCheck

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

abbrev Context := Threads.Context
abbrev principal := Threads.principal

/-- Owned System V worker. Two ordinary stores open and restore the protected
invariant. The spin loop uses the actual ZF produced by CMP EAX,0. -/
def bytes : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x87, 0x07, 0x83, 0xf8, 0, 0x75, 0xf4,
   0x8b, 0x06, 0x8d, 0x40, 1, 0x89, 0x06, 0x8d, 0x40, 1, 0x89, 0x06,
   0xb8, 0, 0, 0, 0, 0x87, 0x07, 0xb8, 0, 0, 0, 0, 0xc3]

inductive Phase where
  | entry | acquiring | comparing | branching | loading
  | incrementingFirst | storingFirst | incrementingSecond | storingSecond
  | preparingRelease | releasing | finishing | returning | completed
  deriving DecidableEq, Repr

def Phase.offset : Phase → Nat
  | .entry => 0 | .acquiring => 5 | .comparing => 7 | .branching => 10
  | .loading => 12 | .incrementingFirst => 14 | .storingFirst => 17
  | .incrementingSecond => 19 | .storingSecond => 22 | .preparingRelease => 24
  | .releasing => 29 | .finishing => 31 | .returning => 36 | .completed => 37

structure Start where
  entry : Context
  codeTicket : Ownership.Ticket
  stackTicket : Ownership.Ticket

structure Worker where
  entry : Context
  returnAddress : Word
  codeLoan : Nat
  stackLoan : Nat
  context : Context
  phase : Phase
  guard : Option Mutex.Lease

/-- A fixed cohort is created before replay. Indices are immutable worker
identities; collection removes the whole cohort rather than recycling IDs. -/
structure State where
  shared : Mutex.State
  workers : List Worker

def empty (shared : Mutex.State) : State := ⟨shared, []⟩
def codeRegion (entry : Context) : Region := ⟨entry.rip, bytes.length⟩

inductive Fault where
  | protocol (fault : Mutex.Fault)
  | machine (fault : X86.Error)
  | missingThread | alreadyCompleted | notCompleted | unexpectedStep
  | invalidContext | unsupportedCode | wrongOwner | busy | started | postcondition
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def started (state : State) : Bool :=
  state.workers.any fun worker => decide (worker.phase ≠ .entry)

/-- Code/return-stack authority is issued through the same mutex resource
history. No raw resource replacement or public guard injection is accepted. -/
def spawn (state : State) (start : Start) : Except Fault State := do
  if started state then throw .started
  let record ← (Mutex.registered state.shared).mapError Fault.protocol
  if record.config.owner ≠ 0 then throw .wrongOwner
  if record.holder.isSome then throw .busy
  if start.entry.registers .rdi ≠ record.config.lockAddress ∨
      start.entry.registers .rsi ≠ record.config.dataAddress then throw .invalidContext
  if !checkCode (toMemory state.shared.shared.resources.space) start.entry.rip bytes then throw .unsupportedCode
  let target ← (readWord (toMemory state.shared.shared.resources.space) (start.entry.registers .rsp)).mapError Fault.machine
  if !canonical target then throw (.machine (.noncanonicalReturn target))
  let (code, codeId) ← (Mutex.readBorrow state.shared 0 start.codeTicket
    (principal state.workers.length) (codeRegion start.entry)).mapError Fault.protocol
  let (stack, stackId) ← (Mutex.readBorrow code 0 start.stackTicket
    (principal state.workers.length) (Threads.stackRegion start.entry)).mapError Fault.protocol
  return ⟨stack, state.workers ++ [⟨start.entry, target, codeId, stackId,
    start.entry, .entry, none⟩]⟩

/-- Only these ordinary instructions can enter the non-memory path. -/
inductive Plain where
  | immediate (value : BitVec 32)
  | increment
  | compare
  | branch
  deriving DecidableEq, Repr

def Plain.instruction : Plain → Instruction
  | .immediate value => .mov32 .rax value
  | .increment => .leaEaxRaxDisp8 1
  | .compare => .cmpEaxZero
  | .branch => .jnz 0xf4

inductive Action where
  | plain (instruction : Plain)
  | acquire
  | load (guard : Mutex.Lease)
  | store (guard : Mutex.Lease)
  | release (guard : Mutex.Lease)
  | ret

def action (worker : Worker) : Except Fault Action :=
  match worker.phase with
  | .entry => .ok (.plain (.immediate 1))
  | .acquiring => if worker.guard.isSome then .error .invalidContext else .ok .acquire
  | .comparing => .ok (.plain .compare)
  | .branching => .ok (.plain .branch)
  | .incrementingFirst | .incrementingSecond => .ok (.plain .increment)
  | .preparingRelease | .finishing => .ok (.plain (.immediate 0))
  | .returning => .ok .ret
  | .completed => .error .alreadyCompleted
  | .loading | .storingFirst | .storingSecond | .releasing =>
    match worker.guard with
    | none => .error .invalidContext
    | some guard => .ok (match worker.phase with
      | .loading => .load guard
      | .releasing => .release guard
      | _ => .store guard)

def decode (shared : Mutex.State) (context : Context) (expected : Instruction) : Except Fault Unit := do
  let actual ← (decodeAt (context.snapshot shared.shared.resources.space)).mapError Fault.machine
  if actual ≠ expected then throw .unexpectedStep

def runNext (shared : Mutex.State) (context : Context) (expected : Instruction) : Except Fault Context := do
  decode shared context expected
  match ← (X86.step (context.snapshot shared.shared.resources.space)).mapError Fault.machine with
  | .next actual => return .ofState actual
  | _ => throw .unexpectedStep

def runAtomic (shared : Mutex.State) (context : Context) (event : AtomicEvent) : Except Fault Context := do
  decode shared context .exchangeEaxRdi
  match ← (X86.step (context.snapshot shared.shared.resources.space)).mapError Fault.machine with
  | .atomic actual output =>
    if actual ≠ event then throw .unexpectedStep
    return .ofState output
  | _ => throw .unexpectedStep

def runReturn (shared : Mutex.State) (context : Context) : Except Fault Context := do
  decode shared context .ret
  match ← (X86.step (context.snapshot shared.shared.resources.space)).mapError Fault.machine with
  | .returned actual => return .ofState actual
  | _ => throw .unexpectedStep

structure Result where
  shared : Mutex.State
  context : Context
  guard : Option Mutex.Lease
  event : Option AtomicEvent
  returned : Bool

/-- Protocol authorization and the actual machine step both run. The bridge
theorems establish equality of their entire resulting memory projections. -/
def perform (shared : Mutex.State) (identifier : Nat) (worker : Worker) : Action → Except Fault Result
  | .plain instruction => do
    let context ← runNext shared worker.context instruction.instruction
    return ⟨shared, context, worker.guard, none, false⟩
  | .acquire => do
    let record ← (Mutex.registered shared).mapError Fault.protocol
    if worker.context.registers .rdi ≠ record.config.lockAddress ∨
        (worker.context.registers .rax).setWidth 32 ≠ 1 then throw .invalidContext
    let result ← (Mutex.tryAcquire shared (principal identifier)).mapError Fault.protocol
    let context ← runAtomic shared worker.context result.event
    return ⟨result.state, context, result.acquired, some result.event, false⟩
  | .load guard => do
    let record ← (Mutex.authorize shared (principal identifier) guard).mapError Fault.protocol
    if worker.context.registers .rsi ≠ record.config.dataAddress then throw .invalidContext
    let _ ← (Mutex.guardLoad shared (principal identifier) guard).mapError Fault.protocol
    let context ← runNext shared worker.context .loadEaxRsi
    return ⟨shared, context, worker.guard, none, false⟩
  | .store guard => do
    let record ← (Mutex.authorize shared (principal identifier) guard).mapError Fault.protocol
    if worker.context.registers .rsi ≠ record.config.dataAddress then throw .invalidContext
    let after ← (Mutex.guardStore shared (principal identifier) guard
      ((worker.context.registers .rax).setWidth 32)).mapError Fault.protocol
    let context ← runNext shared worker.context .storeEaxRsi
    return ⟨after, context, worker.guard, none, false⟩
  | .release guard => do
    let record ← (Mutex.authorize shared (principal identifier) guard).mapError Fault.protocol
    if worker.context.registers .rdi ≠ record.config.lockAddress ∨
        (worker.context.registers .rax).setWidth 32 ≠ 0 then throw .invalidContext
    let result ← (Mutex.release shared (principal identifier) guard).mapError Fault.protocol
    let context ← runAtomic shared worker.context result.2
    return ⟨result.1, context, none, some result.2, false⟩
  | .ret => do
    let context ← runReturn shared worker.context
    return ⟨shared, context, worker.guard, none, true⟩

def nextPhase (worker : Worker) (result : Result) : Phase :=
  match worker.phase with
  | .entry => .acquiring | .acquiring => .comparing | .comparing => .branching
  | .branching => if result.context.rip = worker.entry.rip then .entry else .loading
  | .loading => .incrementingFirst | .incrementingFirst => .storingFirst
  | .storingFirst => .incrementingSecond | .incrementingSecond => .storingSecond
  | .storingSecond => .preparingRelease | .preparingRelease => .releasing
  | .releasing => .finishing | .finishing => .returning
  | .returning | .completed => .completed

def contextValid (worker : Worker) : Bool :=
  decide (worker.context.registers .rdi = worker.entry.registers .rdi ∧
    worker.context.registers .rsi = worker.entry.registers .rsi ∧
    worker.context.registers .rsp = worker.entry.registers .rsp +
      (if worker.phase = .completed then 8 else 0) ∧
    worker.context.rip = (if worker.phase = .completed then worker.returnAddress
      else worker.entry.rip + BitVec.ofNat 64 worker.phase.offset))

def advance (state : State) (identifier : Nat) (worker : Worker) : Except Fault Result := do
  if !contextValid worker then throw .invalidContext
  if !checkCode (toMemory state.shared.shared.resources.space) worker.entry.rip bytes then throw .unsupportedCode
  let operation ← action worker
  let result ← perform state.shared identifier worker operation
  let after := { worker with context := result.context, phase := nextPhase worker result, guard := result.guard }
  if !contextValid after then throw .invalidContext
  if result.returned then
    if after.phase ≠ .completed then throw .unexpectedStep
  else
    if after.phase = .completed then throw .unexpectedStep
  return result

def dispatch (state : State) (identifier : Nat) : Except Fault (State × Option AtomicEvent) := do
  let some worker := state.workers[identifier]? | throw .missingThread
  let result ← advance state identifier worker
  let after := { worker with context := result.context, phase := nextPhase worker result, guard := result.guard }
  return (⟨result.shared, state.workers.set identifier after⟩, result.event)

def recordEvent (identifier : Nat) (event : Option AtomicEvent) (tail : List (Nat × AtomicEvent)) : List (Nat × AtomicEvent) :=
  match event with | none => tail | some actual => (identifier, actual) :: tail

def schedule (state : State) : List Nat → Except Fault (State × List (Nat × AtomicEvent))
  | [] => .ok (state, [])
  | identifier :: rest => do
    let first ← dispatch state identifier
    let tail ← schedule first.1 rest
    return (tail.1, recordEvent identifier first.2 tail.2)

def completed (state : State) : Bool :=
  state.workers.all fun worker => decide (worker.phase = .completed ∧
    worker.context.registers .rax = 0 ∧ worker.guard = none)

/-- Independent endpoint contract. Acceptance observes actual lock/payload
cells and the retained machine return values; it does not infer completion
from fuel exhaustion or an attempted schedule. -/
def Post (before after : State) (initial : BitVec 32) : Prop :=
  after.workers.length = before.workers.length ∧ completed after = true ∧
  ∃ original record, before.shared.mutex = some original ∧
    after.shared.mutex = some record ∧ record.holder = none ∧
    loadDWord (toMemory after.shared.shared.resources.space) original.config.lockAddress = .ok 0 ∧
    loadDWord (toMemory after.shared.shared.resources.space) original.config.dataAddress =
      .ok (initial + BitVec.ofNat 32 (2 * before.workers.length)) ∧
    original.config.invariant (initial + BitVec.ofNat 32 (2 * before.workers.length)) = true

def checkPost (before after : State) (initial : BitVec 32) : Bool :=
  match before.shared.mutex, after.shared.mutex with
  | some original, some record => decide (after.workers.length = before.workers.length ∧ completed after = true ∧
      record.holder = none ∧
      (loadDWord (toMemory after.shared.shared.resources.space) original.config.lockAddress).toOption = some 0 ∧
      (loadDWord (toMemory after.shared.shared.resources.space) original.config.dataAddress).toOption =
        some (initial + BitVec.ofNat 32 (2 * before.workers.length)) ∧
      original.config.invariant (initial + BitVec.ofNat 32 (2 * before.workers.length)) = true)
  | _, _ => false

def verify (state : State) (selections : List Nat) : Except Fault (State × List (Nat × AtomicEvent)) := do
  if started state then throw .started
  let record ← (Mutex.registered state.shared).mapError Fault.protocol
  if record.holder.isSome then throw .busy
  let initial ← (loadDWord (toMemory state.shared.shared.resources.space) record.config.dataAddress).mapError Fault.machine
  let result ← schedule state selections
  if !checkPost state result.1 initial then throw .postcondition
  return result

/-- Cohort collection uses the loan identifiers retained by checked spawn.
Arbitrary finishLoans calls are not transitions admitted during replay. -/
def finishLoans (shared : Mutex.State) (identifier : Nat) : List Worker → Except Fault Mutex.State
  | [] => .ok shared
  | worker :: rest => do
    let code ← (Mutex.finishLoan shared (principal identifier) worker.codeLoan).mapError Fault.protocol
    let stack ← (Mutex.finishLoan code (principal identifier) worker.stackLoan).mapError Fault.protocol
    finishLoans stack (identifier + 1) rest

def collect (state : State) : Except Fault (Mutex.State × List Word) := do
  if !completed state then throw .notCompleted
  let shared ← finishLoans state.shared 0 state.workers
  return (shared, state.workers.map fun worker => worker.context.registers .rax)

end EDSL.OS.MutexReplay
