/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ManagedReturn
import EDSL.Concurrency.AtomicCalls

/-!
Checked padding/MOV64/RET shapes and proof-side callable cutpoints for the
frozen c_atomic_load_acquire64/c_atomic_store_release64 interface. Execution,
admission and return origins remain those of the production TSO64 scheduler.
This model does not prove progress, scheduler closure or an AtomicCalls.History
adapter. Physical correspondence retains the existing long-mode, CET-off,
scalar RAM, translation/alias and managed-resource environmental assumptions.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

abbrev Padding := AtomicMethods.Padding

/-- Both the effective address and a store's source are read in the access
prestate. RAX/address/source aliases and a store source of RSP are allowed. -/
inductive Operation where
  | load (address : Sequential.Address)
  | store (address : Sequential.Address) (source : Register)
  deriving DecidableEq, Repr

def Operation.address : Operation → Sequential.Address
  | .load address | .store address _ => address

def Operation.instruction : Operation → Sequential.Instruction
  | .load address => .loadMem64 .rax address
  | .store address source => .storeMem64 address source

def Operation.length (operation : Operation) : Nat := operation.instruction.length

def Operation.Reply : Operation → Type
  | .load _ => Word
  | .store .. => PUnit

/-- A register assertion using the existing full-register write, not an
instruction evaluator. Stores preserve all GPRs; loads replace exactly RAX. -/
def Operation.registers (operation : Operation) (entry : Register → Word) :
    operation.Reply → Register → Word :=
  match operation with
  | .load _ => fun value => written entry .rax value
  | .store .. => fun _ => entry

theorem Operation.registers_rsp (operation : Operation) (entry : Register → Word)
    (reply : operation.Reply) : operation.registers entry reply .rsp = entry .rsp := by
  cases operation with
  | load _ => exact written_other entry .rax reply .rsp (by decide)
  | store _ _ => rfl

/-- The source request is independent of observed memory and of verification
success. Its location is a persistent cell identity, not a machine address. -/
def Operation.request (operation : Operation) (object : Atomics64.CellId64)
    (entry : Register → Word) : Concurrency.AtomicCalls.Request Atomics64.CellId64 Word :=
  match operation with
  | .load _ => .loadAcquire object
  | .store _ source => .storeRelease object (entry source)

def Operation.requestReply (operation : Operation) (object : Atomics64.CellId64)
    (entry : Register → Word) : operation.Reply → (operation.request object entry).Reply :=
  match operation with
  | .load _ => fun reply => reply
  | .store .. => fun reply => reply

/-- Actual decoding at every node and exact extent; no trailing bytes are
ignored. Access length includes the selected addressing form's encoded suffix. -/
inductive Shape (bytes : List Byte) (operation : Operation) : Nat → List Padding → Prop where
  | body {offset}
      (access : Node bytes offset (.ordinary operation.instruction))
      (ret : Node bytes (offset + operation.length) (.ordinary (.legacy .ret)))
      (extent : offset + operation.length + 1 = bytes.length) :
      Shape bytes operation offset []
  | pad {offset padding rest}
      (node : Node bytes offset (.ordinary padding.instruction))
      (tail : Shape bytes operation (offset + padding.instruction.length) rest) :
      Shape bytes operation offset (padding :: rest)

def checkFrom (bytes : List Byte) (operation : Operation) : Nat → List Padding → Bool
  | offset, [] => decide (Node bytes offset (.ordinary operation.instruction)) &&
      decide (Node bytes (offset + operation.length) (.ordinary (.legacy .ret))) &&
      decide (offset + operation.length + 1 = bytes.length)
  | offset, padding :: rest => decide (Node bytes offset (.ordinary padding.instruction)) &&
      checkFrom bytes operation (offset + padding.instruction.length) rest

def check (bytes : List Byte) (operation : Operation) (padding : List Padding) : Bool :=
  decide (bytes.length ≤ 64) && checkFrom bytes operation 0 padding

theorem checkFrom_sound {bytes : List Byte} {operation : Operation} {offset : Nat}
    {padding : List Padding} (accepted : checkFrom bytes operation offset padding = true) :
    Shape bytes operation offset padding := by
  induction padding generalizing offset with
  | nil =>
      have parts := accepted
      simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at parts
      exact .body parts.1.1 parts.1.2 parts.2
  | cons padding rest ih =>
      have parts := accepted
      simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at parts
      exact .pad parts.1 (ih parts.2)

theorem check_sound {bytes : List Byte} {operation : Operation} {padding : List Padding}
    (accepted : check bytes operation padding = true) :
    bytes.length ≤ 64 ∧ Shape bytes operation 0 padding := by
  have parts := Bool.and_eq_true_iff.mp accepted
  exact ⟨of_decide_eq_true parts.1, checkFrom_sound parts.2⟩

/-- A FIFO frame allows any number of head drains, retaining the exact counter
and remaining entries. It requires neither an empty queue nor invented history
for entries already present at the invocation boundary. -/
structure QueueFrame (expected actual : Queue.Cursor) : Prop where
  counter : actual.nextStore = expected.nextStore
  suffix : ∃ drained, expected.pending = drained ++ actual.pending

theorem QueueFrame.refl (cursor : Queue.Cursor) : QueueFrame cursor cursor :=
  ⟨rfl, [], rfl⟩

theorem QueueFrame.trans {first middle last : Queue.Cursor}
    (prior : QueueFrame first middle) (following : QueueFrame middle last) :
    QueueFrame first last := by
  refine ⟨following.counter.trans prior.counter, ?_⟩
  obtain ⟨firstDrained, firstFIFO⟩ := prior.suffix
  obtain ⟨nextDrained, nextFIFO⟩ := following.suffix
  exact ⟨firstDrained ++ nextDrained, by rw [firstFIFO, nextFIFO, List.append_assoc]⟩

theorem QueueFrame.dropHead {expected actual : Queue.Cursor}
    (frame : QueueFrame expected actual) : QueueFrame expected actual.dropHead := by
  refine ⟨frame.counter, ?_⟩
  obtain ⟨drained, fifo⟩ := frame.suffix
  cases pending : actual.pending with
  | nil =>
      exact ⟨drained, by simpa only [Queue.Cursor.dropHead, pending, List.tail_nil] using fifo⟩
  | cons head tail =>
      refine ⟨drained ++ [head], ?_⟩
      simpa only [Queue.Cursor.dropHead, pending, List.tail_cons, List.append_assoc,
        List.singleton_append] using fifo

/-- Appending the same managed access commutes with prior head drains. Its
occurrence comes from the unchanged counter, not the current FIFO length. -/
theorem QueueFrame.enqueueManaged {expected actual : Queue.Cursor}
    (frame : QueueFrame expected actual) (reference : Queue.ManagedRef) (value : Word) :
    QueueFrame (expected.enqueueManaged reference value) (actual.enqueueManaged reference value) := by
  refine ⟨congrArg (fun counter => counter + 1) frame.counter, ?_⟩
  obtain ⟨drained, fifo⟩ := frame.suffix
  refine ⟨drained, ?_⟩
  change expected.pending ++ [.managed reference value expected.nextStore] =
    drained ++ (actual.pending ++ [.managed reference value actual.nextStore])
  rw [fifo, frame.counter, List.append_assoc]

/-- Fixed invocation data, including an arbitrary initial FIFO/counter boundary.
No shared-memory value, successful future action, or desired history is retained.
Current supplies the actual code and authority; initial At supplies the shape. -/
structure Method where
  bytes : List Byte
  operation : Operation
  base : Word
  entry : Register → Word
  entryFlags : Word
  resources : Resources
  reference : Queue.ManagedRef
  returnAddress : Word
  initialQueue : Queue.Cursor
  size : bytes.length ≤ 64
  codeNoWrap : base.toNat + bytes.length ≤ 2^64
  originalRsp : entry .rsp = resources.callerAddress
  returnCanonical : canonical returnAddress = true
  stackNoWrap : (entry .rsp).toNat + 8 < 2^64

/-- A carrier for the original RF, not an invocation memory snapshot. The
production Address.eval reads only registers; no alternate evaluator is used. -/
def Method.entryCPU (method : Method) : X86.State :=
  ⟨method.entry, method.base, method.entryFlags, Sequential.codeMemory []⟩

def Method.address (method : Method) : Word :=
  method.operation.address.eval method.entryCPU

def Method.responded (method : Method) (reply : method.operation.Reply) : Register → Word :=
  method.operation.registers method.entry reply

def Method.request (method : Method) : Concurrency.AtomicCalls.Request Atomics64.CellId64 Word :=
  method.operation.request method.reference.handle.cell method.entry

def Method.requestReply (method : Method) (reply : method.operation.Reply) : method.request.Reply :=
  method.operation.requestReply method.reference.handle.cell method.entry reply

/-- Exact access queue postcondition, using production cursor bookkeeping.
A load retains the entire current FIFO/counter. A store appends one exact
managed entry with the original source value and consumes one nextStore. -/
def Method.queueAfter (method : Method) (before : Queue.Cursor) : Queue.Cursor :=
  match method.operation with
  | .load _ => before
  | .store _ source => before.enqueueManaged method.reference (method.entry source)

/-- Admission depends on the present world and original entry registers, never
on a target-memory snapshot or an address reevaluated after the RAX load. -/
structure Current (method : Method) (state : OS.TSO64.State) : Prop where
  valid : WellFormed state .sharedCell
  code : CodeAt (published state.world) method.base method.bytes
  fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩ method.resources.code.loan.region
  caller : Borrowing.loadWord64 state.world.legacy.shared method.resources.actor
    method.resources.caller.identifier method.resources.callerAddress = .ok method.returnAddress
  selected : atomicFor state.world method.resources method.address =
    some (method.reference.identifier, method.reference.handle, method.reference.cell)

theorem Current.step {method : Method} {before : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} (current : Current method before)
    (success : OS.TSO64.step before action .sharedCell = .ok result) : Current method result.1 := by
  exact ⟨step_wellFormed current.valid success, step_code success current.code, current.fits,
    ManagedReturn.loan_read_preserved current.valid success current.caller,
    (atomicFor_stable (step_stable success) _ _).trans current.selected⟩

/-- Current checked bytes determine both production decodings and code bounds,
even with a nonempty own FIFO. This is a fetch fact, not a successful issue. -/
theorem Current.decode_node {method : Method} {state : OS.TSO64.State} {worker : Worker}
    {tid offset : Nat} {instruction : Sequential.Instruction} (current : Current method state)
    (live : state.workers[tid]? = some worker) (resources : worker.resources = method.resources)
    (node : Node method.bytes offset (.ordinary instruction))
    (pc : worker.context.rip = method.base + BitVec.ofNat 64 offset) :
    OS.TSO64.decode (fetchCPU state worker) = .ok (.ordinary instruction) ∧
      Sequential.decodeAt (localCPU state worker) = .ok instruction ∧
      codeFits worker instruction.length := by
  have fits : Borrowing.Subregion ⟨method.base, method.bytes.length⟩
      worker.resources.code.loan.region := by
    rw [resources]
    exact current.fits
  have workerValid := current.valid.2 worker (List.mem_of_getElem? live)
  exact ⟨node.decoded method.size (guarded_code current.code fits) (fetchCPU state worker) rfl pc,
    decode_ordinary (node.decoded method.size
      (ManagedRules.local_code current.valid workerValid current.code fits)
      (localCPU state worker) rfl pc), node.codeFits current.code fits pc⟩

/-- Proof-side stages only. A reply is a load word or a store unit; it is not
admission evidence and carries no reads-from/publication claim. -/
inductive Point (operation : Operation) where
  | preamble (offset : Nat) (padding : List Padding)
  | ret (offset : Nat) (reply : operation.Reply)
  | done (reply : operation.Reply)

def Point.remaining {operation : Operation} : Point operation → Nat
  | .preamble _ padding => padding.length + 2
  | .ret .. => 1
  | .done _ => 0

def Method.queueAt (method : Method) : Point method.operation → Queue.Cursor
  | .preamble .. => method.initialQueue
  | .ret .. | .done _ => method.queueAfter method.initialQueue

/-- Exact phase, PC, RF, flags, original resources, counter and remaining FIFO.
The suffix frame permits drains between all stages, including after RET.
For a store the expected FIFO ends in the exact allocated managed occurrence;
that occurrence may already have drained. No publication is inferred here. -/
structure At (method : Method) (point : Point method.operation) (worker : Worker) : Prop where
  resources : worker.resources = method.resources
  flags : worker.context.flags = method.entryFlags
  queue : QueueFrame (method.queueAt point) ⟨worker.pending, worker.nextStore⟩
  location : match point with
    | .preamble offset padding => worker.phase = .running ∧
        worker.context.rip = method.base + BitVec.ofNat 64 offset ∧
        worker.context.registers = method.entry ∧ Shape method.bytes method.operation offset padding
    | .ret offset reply => worker.phase = .running ∧
        worker.context.rip = method.base + BitVec.ofNat 64 offset ∧
        worker.context.registers = method.responded reply ∧
        Node method.bytes offset (.ordinary (.legacy .ret)) ∧ offset + 1 = method.bytes.length
    | .done reply => worker.phase = .returned ∧ worker.context.rip = method.returnAddress ∧
        worker.context.registers = written (method.responded reply) .rsp (method.entry .rsp + 8)

theorem address_eval_registers (address : Sequential.Address) {first second : X86.State}
    (registers : first.registers = second.registers) : address.eval first = address.eval second := by
  cases address <;> simp only [Sequential.Address.eval, registers]

/-- The actual access prestate has the original effective address, even when
RAX is part of that address. No assertion reevaluates it after the load. -/
theorem At.preamble_address {method : Method} {state : OS.TSO64.State} {worker : Worker}
    {offset : Nat} {padding : List Padding} (located : At method (.preamble offset padding) worker) :
    method.operation.address.eval (localCPU state worker) = method.address := by
  exact address_eval_registers _ located.location.2.2.1

theorem At.preamble_register {method : Method} {state : OS.TSO64.State} {worker : Worker}
    {offset : Nat} {padding : List Padding} (located : At method (.preamble offset padding) worker)
    (register : Register) : (localCPU state worker).registers register = method.entry register :=
  congrFun located.location.2.2.1 register

theorem Current.preamble_selected {method : Method} {state : OS.TSO64.State} {worker : Worker}
    {offset : Nat} {padding : List Padding} (current : Current method state)
    (located : At method (.preamble offset padding) worker) :
    atomicFor state.world worker.resources (method.operation.address.eval (localCPU state worker)) =
      some (method.reference.identifier, method.reference.handle, method.reference.cell) := by
  rw [located.resources, located.preamble_address]
  exact current.selected

theorem At.ret_rsp {method : Method} {worker : Worker} {offset : Nat}
    {reply : method.operation.Reply} (located : At method (.ret offset reply) worker) :
    worker.context.registers .rsp = method.resources.callerAddress := by
  rw [located.location.2.2.1]
  exact (method.operation.registers_rsp method.entry reply).trans method.originalRsp

/-- Conditional projection of an already established done cutpoint through the
existing return API. Reaching this cutpoint remains a progress-proof obligation. -/
theorem At.done_returnValue {method : Method} {state : OS.TSO64.State} {worker : Worker}
    {tid : Nat} {reply : method.operation.Reply} (live : state.workers[tid]? = some worker)
    (located : At method (.done reply) worker) :
    OS.TSO64.Return.returnValue (state, .returned tid) =
      some (tid, method.responded reply .rax) := by
  have rax : worker.context.registers .rax = method.responded reply .rax := by
    rw [located.location.2.2]
    exact written_other _ .rsp _ .rax (by decide)
  simp only [OS.TSO64.Return.returnValue, live, Option.map_some, rax]

/-- A successful response additionally has the production RET origin. This
links no invocation/access interval and constructs no AtomicCalls.History. -/
theorem At.return_origin {method : Method} {before after : OS.TSO64.State}
    {action : Action} {worker : Worker} {tid : Nat} {reply : method.operation.Reply}
    (valid : WellFormed before .sharedCell)
    (success : OS.TSO64.step before action .sharedCell = .ok (after, .returned tid))
    (live : after.workers[tid]? = some worker) (located : At method (.done reply) worker) :
    OS.TSO64.Return.ReturnOrigin before action (after, .returned tid) tid
      (method.responded reply .rax) .sharedCell :=
  OS.TSO64.Return.returnValue_sound valid success (At.done_returnValue live located)

end EDSL.X86.VCGen.PlainMethods
