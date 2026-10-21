/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ScalarCall64
import EDSL.Concurrency.AtomicCalls
import EDSL.Audit

/-!
Independent present-state admission for managed full64 acquire loads and
release stores. A trusted catalog registers an operation and an entire callable
image; each actual initial worker slot selects one of those sites. Registers,
current resources, original protected callers and executable bytes are bound
without an instruction shape, verification result or future execution premise.

The annotations select the declared atomic interface. They do not establish
source/compiler ordering preservation or physical x86/Linux correspondence.
The represented scalar RAM, stable translations/no hidden aliases, managed
authority, long-mode/CET-off and fixed worker population remain the execution
model's environmental boundaries. This module defines no completed-call,
history, full-file certificate or inhabited-corpus claim.
-/

set_option autoImplicit false

namespace EDSL.Grading.ConcurrentTask.Plain64
open X86 OS Concurrency

abbrev Image := OS.ScalarCall64.Image
abbrev ScalarEntry := OS.ScalarCall64.Entry

inductive Kind where
  | loadAcquire | storeRelease
  deriving DecidableEq, Repr

structure Site where
  kind : Kind
  image : Image
  deriving DecidableEq, Repr

abbrev Catalog := List Site

/-- Logical occurrence labels are independent of machine store allocation.
A load has no supplied reply and leaves its unused RSI unconstrained. -/
inductive Input where
  | loadAcquire (image : Image) (target : Atomics64.CellId64)
      (cell : Atomics64.Cell) (occurrence : Nat)
  | storeRelease (image : Image) (target : Atomics64.CellId64)
      (cell : Atomics64.Cell) (value : Word) (occurrence : Nat)

def Input.site : Input → Site
  | .loadAcquire image .. => ⟨.loadAcquire, image⟩
  | .storeRelease image .. => ⟨.storeRelease, image⟩

def Input.target : Input → Atomics64.CellId64
  | .loadAcquire _ target .. | .storeRelease _ target .. => target

def Input.cell : Input → Atomics64.Cell
  | .loadAcquire _ _ cell _ | .storeRelease _ _ cell .. => cell

def Input.occurrence : Input → Nat
  | .loadAcquire _ _ _ occurrence | .storeRelease _ _ _ _ occurrence => occurrence

def Input.request : Input → AtomicCalls.Request Atomics64.CellId64 Word
  | .loadAcquire _ target .. => .loadAcquire target
  | .storeRelease _ target _ value _ => .storeRelease target value

abbrev Input.Reply (input : Input) := input.request.Reply

def Input.argument (input : Input) (index : Fin 6) : Option PureCall.Argument :=
  if index.val = 0 then some (.word64 input.cell.address)
  else if index.val = 1 then
    match input with
    | .loadAcquire .. => none
    | .storeRelease _ _ _ value _ => some (.word64 value)
  else none

def Arguments (input : Input) (worker : TSO64.Worker) : Prop :=
  ∀ index argument, input.argument index = some argument →
    argument.Holds (worker.context.registers (PureCall.argumentRegister index))

theorem Arguments.rdi {input : Input} {worker : TSO64.Worker}
    (arguments : Arguments input worker) :
    worker.context.registers .rdi = input.cell.address :=
  arguments 0 (.word64 input.cell.address) rfl

theorem Arguments.store_rsi {image : Image} {target : Atomics64.CellId64}
    {cell : Atomics64.Cell} {value : Word} {occurrence : Nat} {worker : TSO64.Worker}
    (arguments : Arguments (.storeRelease image target cell value occurrence) worker) :
    worker.context.registers .rsi = value :=
  arguments 1 (.word64 value) rfl

/-- Every field concerns this actual entry state. Current original code/caller
leases and validity of every incoming FIFO entry follow from `Pre.valid`.
The full descriptor and the selector bind current whole-qword authority; no
address-only handle or later authorization is assumed. -/
structure Entry (input : Input) (before : TSO64.State)
    (worker : TSO64.Worker) : Prop where
  running : worker.phase = .running
  pc : worker.context.rip = input.site.image.base
  arguments : Arguments input worker
  nonempty : 0 < input.site.image.bytes.length
  baseCanonical : canonical input.site.image.base = true
  code : CodeAt (TSO64.published before.world)
    input.site.image.base input.site.image.bytes
  fits : Borrowing.Subregion ⟨input.site.image.base, input.site.image.bytes.length⟩
    worker.resources.code.loan.region
  originalRsp : worker.context.registers .rsp = worker.resources.callerAddress
  scalar : ScalarEntry worker
  liveTarget : before.world.cells input.target = some input.cell
  validCell : Atomics64.ValidCell before.world.legacy.shared input.cell
  selected : ∃ identifier handle,
    TSO64.atomicFor before.world worker.resources input.cell.address =
      some (identifier, handle, input.cell) ∧ handle.cell = input.target
  caller : ∃ continuation,
    Borrowing.loadWord64 before.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok continuation ∧
    canonical continuation = true

/-- One selected input for every actual initial slot, including all peers.
Incoming valid queues and arbitrary nextStore counters are admitted. Original
caller slots are private, and each complete code image is separated from every
original caller slot. Shape checking belongs to a separate proof-side bridge. -/
structure Pre (catalog : Catalog) (before : TSO64.State)
    (inputs : Fin before.workers.length → Input) : Prop where
  valid : TSO64.WellFormed before .sharedCell
  selected : ∀ tid, (inputs tid).site ∈ catalog
  entry : ∀ tid, ∃ worker, before.workers[tid.val]? = some worker ∧
    Entry (inputs tid) before worker
  privateCallers : ∀ (i j : Fin before.workers.length) first second,
    i ≠ j → before.workers[i.val]? = some first → before.workers[j.val]? = some second →
    Ownership.Disjoint first.resources.caller.loan.region second.resources.caller.loan.region
  codeCallerSeparation : ∀ (i j : Fin before.workers.length) caller,
    before.workers[j.val]? = some caller →
    Ownership.Disjoint
      ⟨(inputs i).site.image.base, (inputs i).site.image.bytes.length⟩
      caller.resources.caller.loan.region

/-- Whole-graph admission separately adds empty initial queues. It places no
zero-counter or invented past-issue requirement on this boundary. -/
def ClosedPre (catalog : Catalog) (before : TSO64.State)
    (inputs : Fin before.workers.length → Input) : Prop :=
  Pre catalog before inputs ∧ TSO64.Quiescent before

theorem Pre.workerValid {catalog : Catalog} {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} (pre : Pre catalog before inputs)
    {tid : Nat} {worker : TSO64.Worker} (live : before.workers[tid]? = some worker) :
    TSO64.WorkerValid before.world worker .sharedCell :=
  pre.valid.2 worker (List.mem_of_getElem? live)

/-- This includes current ORIGINAL loan descriptors, a readable caller qword
equal to the original caller region, and the worker's actual authority lists. -/
theorem Pre.resources {catalog : Catalog} {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} (pre : Pre catalog before inputs)
    {tid : Nat} {worker : TSO64.Worker} (live : before.workers[tid]? = some worker) :
    TSO64.ResourcesValid before.world worker.resources :=
  (pre.workerValid live).1

theorem Pre.pendingValid {catalog : Catalog} {before : TSO64.State}
    {inputs : Fin before.workers.length → Input} (pre : Pre catalog before inputs)
    {tid : Nat} {worker : TSO64.Worker} (live : before.workers[tid]? = some worker) :
    ∀ pending ∈ worker.pending,
      TSO64.PendingValid before.world worker.resources pending .sharedCell :=
  (pre.workerValid live).2

end EDSL.Grading.ConcurrentTask.Plain64

#audit_edsl
