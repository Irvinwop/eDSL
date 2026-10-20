/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Layout

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

abbrev Context := Threads.Context
abbrev principal := Threads.principal
abbrev Fault := AtomicThreads64.Fault
abbrev HasLoan := Threads.HasLoan
abbrev HasHandle := AtomicThreads64.HasHandle
abbrev stackRegion := Threads.stackRegion

def applied (context : Context) (value : Word) (af : Bool) : Context :=
  { context with
    rip := context.rip + 4
    flags := Sequential.logicalFlags64 context.flags value af }

def returned (context : Context) (target : Word) : Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8
      else context.registers register
    rip := target }

inductive Phase where
  | running
  | completed
  deriving DecidableEq, Repr

structure Start where
  entry : Context
  bytes : List Byte
  cell : Atomics64.CellId64
  codeTicket : Ownership.Ticket
  stackTicket : Ownership.Ticket

/-- Immutable invocation authority and current private CPU cursor. Captured
events are audit data; their after-values are never restored into shared RAM.
Actual event origins require checked execution evidence. -/
structure Worker where
  parent : Nat
  entry : Context
  bytes : List Byte
  operations : List Sequential.LogicalOp
  cell : Atomics64.CellId64
  returnAddress : Word
  handle : Atomics64.HandleId64
  codeLoan : Nat
  stackLoan : Nat
  context : Context
  cursor : Nat
  events : List Atomics64.Event
  phase : Phase

structure State where
  shared : Atomics64.State
  nextThread : Nat
  workers : Nat → Option Worker

def empty (shared : Atomics64.State) : State := ⟨shared, 0, fun _ => none⟩
def codeRegion (entry : Context) (bytes : List Byte) : Region := ⟨entry.rip, bytes.length⟩

def replace (state : State) (identifier : Nat) (worker : Option Worker) : State :=
  { state with workers := fun query => if query = identifier then worker else state.workers query }

def install (state : State) (shared : Atomics64.State) (worker : Worker) : State :=
  { shared := shared, nextThread := state.nextThread + 1
    workers := fun query => if query = state.nextThread then some worker else state.workers query }

/-- Checked functional transaction: failure exposes no partial loans/handle. -/
def spawn (state : State) (parent : Nat) (start : Start) (available : Bool := true) :
    Except Fault (State × Nat) := do
  if parent ≠ 0 then throw .wrongParent
  if !available then throw .creationFailed
  if (state.workers state.nextThread).isSome then throw .identityCollision
  let operations ← match checkLayout start.bytes with
    | none => .error .unsupportedCode
    | some operations => .ok operations
  if !codeMatches state.shared.legacy.shared.resources.space start.entry.rip start.bytes then throw .unsupportedCode
  let cell ← (Atomics64.authorizeCell state.shared parent start.cell).mapError AtomicThreads64.Fault.atomic
  if start.entry.registers .rdi ≠ cell.address then throw .unexpectedStep
  let target ← (readWord (toMemory state.shared.legacy.shared.resources.space)
    (start.entry.registers .rsp)).mapError AtomicThreads64.Fault.machine
  if !canonical target then throw (.machine (.noncanonicalReturn target))
  if !(decide ((start.entry.registers .rsp).toNat + 8 < 2^64)) then throw .unexpectedStep
  if !canonical (start.entry.registers .rsp + 8) then throw .unexpectedStep
  let (code, codeId) ← (Atomics64.readBorrow state.shared parent start.codeTicket
    (principal state.nextThread) (codeRegion start.entry start.bytes)).mapError AtomicThreads64.Fault.atomic
  let (stack, stackId) ← (Atomics64.readBorrow code parent start.stackTicket
    (principal state.nextThread) (stackRegion start.entry)).mapError AtomicThreads64.Fault.atomic
  let (data, handle) ← (Atomics64.issue stack parent start.cell
    (principal state.nextThread)).mapError AtomicThreads64.Fault.atomic
  return (install state data
    ⟨parent, start.entry, start.bytes, operations, start.cell, target, handle,
      codeId, stackId, start.entry, 0, [], .running⟩, state.nextThread)

/-- One actual selected instruction, fetched against CURRENT shared RAM.
The decoded opcode selects the checked operation; no requested task chooses it. -/
def dispatch (state : State) (identifier : Nat) (af : Bool) :
    Except Fault (State × Option Atomics64.Event) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  match worker.phase with
  | .completed => throw .alreadyCompleted
  | .running =>
    match ← (LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space)).mapError AtomicThreads64.Fault.machine with
    | .logicalRdiRsi op =>
      let selected ← (Atomics64.authorize state.shared (principal identifier) worker.handle).mapError AtomicThreads64.Fault.atomic
      if worker.context.registers .rdi ≠ selected.2.address then throw .unexpectedStep
      let (shared, event) ← (Atomics64.logicalUpdate op state.shared (principal identifier)
        worker.handle (worker.context.registers .rsi)).mapError AtomicThreads64.Fault.atomic
      match ← (LockedSet64.step af (worker.context.snapshot state.shared.legacy.shared.resources.space)).mapError AtomicThreads64.Fault.machine with
      | ⟨.atomic64 label actual, _⟩ =>
        if label ≠ event.logical then throw .unexpectedStep
        return ({ replace state identifier (some { worker with
          context := Threads.Context.ofState actual, cursor := worker.cursor + 1,
          events := worker.events ++ [event] }) with shared := shared }, some event)
      | _ => throw .unexpectedStep
    | .ret =>
      match ← (LockedSet64.step af (worker.context.snapshot state.shared.legacy.shared.resources.space)).mapError AtomicThreads64.Fault.machine with
      | ⟨.returned actual, _⟩ => return (replace state identifier
          (some { worker with context := Threads.Context.ofState actual, phase := .completed }), none)
      | _ => throw .unexpectedStep

/-- Collection returns only a private context and revokes precisely its stored
handle/two loans. Completed workers retain authority until checked collection. -/
def join (state : State) (parent identifier : Nat) : Except Fault (State × Context) := do
  let worker ← match state.workers identifier with
    | none => .error .missingThread
    | some worker => .ok worker
  if worker.parent ≠ parent then throw .wrongParent
  match worker.phase with
  | .running => throw .notCompleted
  | .completed =>
    let data ← (Atomics64.close state.shared (principal identifier) worker.handle).mapError AtomicThreads64.Fault.atomic
    let code ← (Atomics64.finishLoan data (principal identifier) worker.codeLoan).mapError AtomicThreads64.Fault.atomic
    let stack ← (Atomics64.finishLoan code (principal identifier) worker.stackLoan).mapError AtomicThreads64.Fault.atomic
    return ({ replace state identifier none with shared := stack }, worker.context)

def mutate (state : State) (operation : Ownership.Mutation) :
    Except Fault (State × Option Ownership.Ticket) := do
  let result ← (Atomics64.mutate state.shared operation).mapError AtomicThreads64.Fault.atomic
  return ({ state with shared := result.1 }, result.2)

def retire (state : State) (owner : Nat) (cell : Atomics64.CellId64) : Except Fault State := do
  if owner ≠ 0 then throw .wrongParent
  let shared ← (Atomics64.retire state.shared owner cell).mapError AtomicThreads64.Fault.atomic
  return { state with shared := shared }

/-- This relates private contexts only: one captured event and one arbitrary
AF choice per logical instruction, with no shared-memory snapshots. It does
not authenticate a preexisting event prefix without execution evidence. -/
inductive ContextPrefix (entry : Context) : List Atomics64.Event → Context → Prop
  | nil : ContextPrefix entry [] entry
  | snoc {events : List Atomics64.Event} {context : Context}
      (chain : ContextPrefix entry events context) (event : Atomics64.Event) (af : Bool) :
      ContextPrefix entry (events ++ [event]) (applied context event.logical.event.after af)

def Captured (identifier : Nat) (worker : Worker) : Prop :=
  ∀ (offset : Nat) (event : Atomics64.Event), worker.events[offset]? = some event →
    worker.operations[offset]? = some event.logical.op ∧ event.actor = principal identifier ∧
    event.handle = worker.handle ∧ event.cell = worker.cell ∧
    event.logical.event.address = worker.entry.registers .rdi ∧
    event.logical.mask = worker.entry.registers .rsi

structure PhaseValid (entry : Context) (target : Word) (operations : List Sequential.LogicalOp)
    (cursor : Nat) (events : List Atomics64.Event) (context : Context) (phase : Phase) : Prop where
  counted : cursor = events.length
  bound : cursor ≤ operations.length
  shape : match phase with
    | .running => ContextPrefix entry events context
    | .completed => cursor = operations.length ∧ ∃ before,
        ContextPrefix entry events before ∧ context = returned before target

/-- Current exact identities and both immutable loans remain pinned in both
phases. A captured event's after-word need not still be current after a peer. -/
structure WorkerValid (shared : Atomics64.State) (identifier : Nat) (worker : Worker) : Prop where
  parent : worker.parent = 0
  handle : HasHandle shared identifier worker.handle worker.cell (worker.entry.registers .rdi)
  code : HasLoan shared.legacy.shared identifier worker.codeLoan (codeRegion worker.entry worker.bytes)
  stack : HasLoan shared.legacy.shared identifier worker.stackLoan (stackRegion worker.entry)
  distinct : worker.codeLoan ≠ worker.stackLoan
  layout : worker.bytes = bodyBytes worker.operations
  executable : CodeAt (toMemory shared.legacy.shared.resources.space) worker.entry.rip worker.bytes
  target : readWord (toMemory shared.legacy.shared.resources.space)
    (worker.entry.registers .rsp) = .ok worker.returnAddress
  canonical : X86.canonical worker.returnAddress = true
  stackBound : (worker.entry.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : X86.canonical (worker.entry.registers .rsp + 8) = true
  captured : Captured identifier worker
  phase : PhaseValid worker.entry worker.returnAddress worker.operations worker.cursor worker.events worker.context worker.phase

def WellFormed (state : State) : Prop :=
  Atomics64.WellFormed state.shared ∧ ∀ identifier worker, state.workers identifier = some worker →
    identifier < state.nextThread ∧ WorkerValid state.shared identifier worker

/-- Remaining selected user instructions, including the actual RET. -/
def Worker.rank (worker : Worker) : Nat :=
  match worker.phase with
  | .running => worker.operations.length - worker.cursor + 1
  | .completed => 0

/-- Present borrowing facts. No successful future checked wrapper is assumed. -/
def BorrowReady (shared : Atomics64.State) (ticket : Ownership.Ticket) (region : Region) : Prop :=
  ∃ allocation,
    Ownership.authorize shared.legacy.shared.resources 0 ticket = .ok allocation ∧
    region.valid = true ∧ Borrowing.Subregion region allocation.region ∧
    Borrowing.allReadable shared.legacy.shared.resources.space region = true ∧
    Atomics64.reserved shared ticket.identifier = false ∧
    Atomics.reserved shared.legacy ticket.identifier = false

/-- Resource-only constructive spawn admission. Syntax describes supported
finite bodies; no future run, opcode/task agreement or final value is admitted. -/
def SpawnReady (state : State) (start : Start) : Prop :=
  ∃ _layout : Layout start.bytes,
    CodeAt (toMemory state.shared.legacy.shared.resources.space) start.entry.rip start.bytes ∧
    ∃ cell, Atomics64.authorizeCell state.shared 0 start.cell = .ok cell ∧
      start.entry.registers .rdi = cell.address ∧
      BorrowReady state.shared start.codeTicket (codeRegion start.entry start.bytes) ∧
      BorrowReady state.shared start.stackTicket (stackRegion start.entry) ∧
      ∃ returnAddress,
        readWord (toMemory state.shared.legacy.shared.resources.space)
          (start.entry.registers .rsp) = .ok returnAddress ∧
        X86.canonical returnAddress = true ∧
        (start.entry.registers .rsp).toNat + 8 < 2^64 ∧
        X86.canonical (start.entry.registers .rsp + 8) = true

theorem empty_wellFormed {shared : Atomics64.State} (valid : Atomics64.WellFormed shared) :
    WellFormed (empty shared) := ⟨valid, by simp [empty]⟩

end EDSL.OS.AtomicSetThreads64

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

theorem ContextPrefix.registers {entry context : Context} {events : List Atomics64.Event}
    (chain : ContextPrefix entry events context) : context.registers = entry.registers := by
  induction chain with
  | nil => rfl
  | snoc chain event af ih => exact ih

theorem ContextPrefix.rip {entry context : Context} {events : List Atomics64.Event}
    (chain : ContextPrefix entry events context) :
    context.rip = entry.rip + BitVec.ofNat 64 (4 * events.length) := by
  induction chain with
  | nil => simp
  | snoc chain event af ih =>
    simp only [applied, List.length_append, List.length_singleton]
    rw [ih, Nat.mul_add, BitVec.ofNat_add]
    simp only [Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

theorem ContextPrefix.flags {entry context : Context} {events : List Atomics64.Event}
    (chain : ContextPrefix entry events context) :
    context.flags &&& ~~~arithmeticFlagMask = entry.flags &&& ~~~arithmeticFlagMask := by
  induction chain with
  | nil => rfl
  | snoc chain event af ih =>
    exact (Sequential.logicalFlags64_preserves ..).trans ih

theorem ContextPrefix.nil_context {entry context : Context}
    (chain : ContextPrefix entry [] context) : context = entry := by
  generalize empty : ([] : List Atomics64.Event) = events at chain
  induction chain with
  | nil => rfl
  | snoc chain event af ih =>
    have lengths := congrArg List.length empty
    simp only [List.length_nil, List.length_append, List.length_singleton] at lengths
    omega

theorem WorkerValid.authorized {shared : Atomics64.State} {identifier : Nat} {worker : Worker}
    (valid : WorkerValid shared identifier worker) (sharedValid : Atomics64.WellFormed shared) :
    ∃ handle cell, Atomics64.authorize shared (principal identifier) worker.handle = .ok (handle, cell) ∧
      cell.address = worker.entry.registers .rdi ∧ handle.cell = worker.cell := by
  obtain ⟨handle, cell, live, actor, link, registered, address⟩ := valid.handle
  exact ⟨handle, cell, Atomics64.authorize_success _ _ _ _ _ sharedValid live actor
    (by rw [link]; exact registered), address, link⟩

theorem WorkerValid.running_registers {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running) :
    worker.context.registers = worker.entry.registers := by
  have shape := valid.phase.shape
  rw [running] at shape
  exact shape.registers

theorem WorkerValid.running_rip {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running) :
    worker.context.rip = worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor) := by
  have shape := valid.phase.shape
  rw [running] at shape
  rw [valid.phase.counted]
  exact shape.rip

theorem WorkerValid.completed_result {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (completed : worker.phase = .completed) :
    worker.context.registers .rax = worker.entry.registers .rax ∧
      worker.context.registers .rsp = worker.entry.registers .rsp + 8 ∧
      worker.context.rip = worker.returnAddress ∧
      (∀ register, register ≠ .rsp → worker.context.registers register = worker.entry.registers register) ∧
      worker.context.flags &&& ~~~arithmeticFlagMask = worker.entry.flags &&& ~~~arithmeticFlagMask := by
  have shape := valid.phase.shape
  rw [completed] at shape
  obtain ⟨_, before, chain, context⟩ := shape
  rw [context]
  have registers := chain.registers
  refine ⟨?_, ?_, rfl, ?_, chain.flags⟩
  · simpa [returned] using congrFun registers .rax
  · change before.registers .rsp + 8 = worker.entry.registers .rsp + 8
    rw [registers]
  · intro register other
    simp only [returned, other, ↓reduceIte, registers]

end EDSL.OS.AtomicSetThreads64

namespace EDSL.OS.AtomicSetThreads64

/-- The last own logical instruction determines the current arithmetic flags;
interleaved peers never enter this private-context relation. -/
theorem ContextPrefix.last_step {entry context : Context} {events : List Atomics64.Event}
    (chain : ContextPrefix entry events context) {event : Atomics64.Event}
    (last : events.getLast? = some event) :
    ∃ earlier before af, events = earlier ++ [event] ∧
      ContextPrefix entry earlier before ∧ context = applied before event.logical.event.after af := by
  cases chain with
  | nil => simp at last
  | @snoc earlier before chain actual af =>
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at last
    cases last
    exact ⟨earlier, before, af, rfl, chain, rfl⟩

end EDSL.OS.AtomicSetThreads64

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

theorem WorkerValid.running_logical_decode {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running)
    {op : Sequential.LogicalOp} (selected : worker.operations[worker.cursor]? = some op) :
    LockedSet64.decodeAt (worker.context.snapshot shared.legacy.shared.resources.space) =
      .ok (.logicalRdiRsi op) := by
  apply LockedSet64.decodeAt_of_code
  have code : CodeAt (toMemory shared.legacy.shared.resources.space) worker.entry.rip
      (bodyBytes worker.operations) := by simpa only [valid.layout] using valid.executable
  simpa only [Threads.Context.snapshot, valid.running_rip running] using
    bodyBytes_logical_code code selected

theorem WorkerValid.running_ret_decode {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running)
    (terminal : worker.cursor = worker.operations.length) :
    LockedSet64.decodeAt (worker.context.snapshot shared.legacy.shared.resources.space) = .ok .ret := by
  apply LockedSet64.decodeAt_of_code
  have code : CodeAt (toMemory shared.legacy.shared.resources.space) worker.entry.rip
      (bodyBytes worker.operations) := by simpa only [valid.layout] using valid.executable
  simpa only [Threads.Context.snapshot, valid.running_rip running, terminal] using
    bodyBytes_ret_code code

/-- Coverage is about the entire decoded instruction inside the immutable
original fetch loan; executable neighbors never extend that authority. -/
theorem WorkerValid.running_fetch {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running) :
    ∃ instruction,
      LockedSet64.decodeAt (worker.context.snapshot shared.legacy.shared.resources.space) = .ok instruction ∧
      worker.context.rip = worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor) ∧
      4 * worker.cursor + instruction.length ≤ worker.bytes.length := by
  by_cases continuing : worker.cursor < worker.operations.length
  · have selected : worker.operations[worker.cursor]? = some worker.operations[worker.cursor] :=
      List.getElem?_eq_getElem continuing
    refine ⟨.logicalRdiRsi _, valid.running_logical_decode running selected,
      valid.running_rip running, ?_⟩
    rw [valid.layout, bodyBytes_length]
    change 4 * worker.cursor + 4 ≤ 4 * worker.operations.length + 1
    omega
  · have terminal : worker.cursor = worker.operations.length := by have := valid.phase.bound; omega
    refine ⟨.ret, valid.running_ret_decode running terminal, valid.running_rip running, ?_⟩
    rw [valid.layout, bodyBytes_length, terminal]
    exact Nat.le_refl _

@[simp] theorem Worker.rank_completed (worker : Worker) (completed : worker.phase = .completed) :
    worker.rank = 0 := by simp [Worker.rank, completed]

theorem Worker.rank_running_positive (worker : Worker) (running : worker.phase = .running) :
    0 < worker.rank := by simp [Worker.rank, running]

end EDSL.OS.AtomicSetThreads64
