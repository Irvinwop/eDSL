import EDSL.OS.Futex.Model
import EDSL.OS.Suspend

namespace EDSL.OS.Futex.Predicate
open X86

def bytes : List Byte :=
  [0x8b, 0x07, 0x83, 0xf8, 0x00, 0x75, 0x16,
   0xb8, 0xca, 0x00, 0x00, 0x00, 0xbe, 0x80, 0x00, 0x00, 0x00,
   0x0f, 0x05, 0xb8, 0x01, 0x00, 0x00, 0x00,
   0x83, 0xf8, 0x00, 0x75, 0xe3, 0xc3]

structure Client where
  entry : Threads.Context
  subject : Nat
  codeLoan : Nat
  stackLoan : Nat
  returnTarget : Word

def Client.ABI (client : Client) : Prop :=
  client.entry.registers .rdx = 0 ∧ client.entry.registers .r10 = 0 ∧
  client.entry.registers .r8 = 0 ∧ client.entry.registers .r9 = 0

inductive Point where
  | load
  | compare (observed : BitVec 32)
  | branch (observed : BitVec 32)
  | number
  | operation
  | syscall
  | resumed (raw : Word)
  | retryCompare
  | retryBranch
  | done (observed : BitVec 32)
  deriving DecidableEq, Repr

def Point.offset : Point → Nat
  | .load => 0
  | .compare _ => 2
  | .branch _ => 5
  | .number => 7
  | .operation => 12
  | .syscall => 17
  | .resumed _ => 19
  | .retryCompare => 24
  | .retryBranch => 27
  | .done _ => 29

def Point.instruction : Point → Instruction
  | .load => .loadEaxRdi
  | .compare _ | .retryCompare => .cmpEaxZero
  | .branch _ => .jnz 0x16
  | .number => .mov32 .rax 202
  | .operation => .mov32 .rsi 128
  | .syscall => .syscall
  | .resumed _ => .mov32 .rax 1
  | .retryBranch => .jnz 0xe3
  | .done _ => .ret

def Stable (client : Client) (context : Threads.Context) : Prop :=
  (∀ register, register ≠ .rax → register ≠ .rsi → register ≠ .rcx → register ≠ .r11 →
    context.registers register = client.entry.registers register) ∧
  (context.registers .rsi = client.entry.registers .rsi ∨ context.registers .rsi = 128)

def Point.Fields (point : Point) (context : Threads.Context) : Prop :=
  match point with
  | .load => True
  | .compare observed => context.registers .rax = observed.setWidth 64
  | .branch observed => context.registers .rax = observed.setWidth 64 ∧
      context.flags.getLsbD 6 = (observed == 0)
  | .number => context.registers .rax = 0
  | .operation => context.registers .rax = 202
  | .syscall => context.registers .rax = 202 ∧ context.registers .rsi = 128
  | .resumed raw => context.registers .rax = raw ∧ context.registers .rsi = 128
  | .retryCompare => context.registers .rax = 1 ∧ context.registers .rsi = 128
  | .retryBranch => context.registers .rax = 1 ∧ context.registers .rsi = 128 ∧
      context.flags.getLsbD 6 = false
  | .done observed => context.registers .rax = observed.setWidth 64 ∧ observed ≠ 0 ∧
      context.flags.getLsbD 6 = false

structure Running (client : Client) (point : Point) (context : Threads.Context) : Prop where
  stable : Stable client context
  rip : context.rip = client.entry.rip + BitVec.ofNat 64 point.offset
  fields : point.Fields context

def Ready (client : Client) (point : Point) (memory : Memory) : Prop :=
  match point with
  | .load => atomicAddressable (client.entry.registers .rdi) = true ∧
      ∃ observed, loadDWord memory (client.entry.registers .rdi) = .ok observed
  | .branch observed => observed ≠ 0 → canonical (client.entry.rip + 29) = true
  | .retryBranch => canonical client.entry.rip = true
  | .done _ => readWord memory (client.entry.registers .rsp) = .ok client.returnTarget ∧
      canonical client.returnTarget = true
  | _ => True

def Client.Family (client : Client) (request : SyscallRequest) : Prop :=
  Running client .syscall (.ofState request.user) ∧ request.continuation = request.user.rip + 2

def Client.returned (client : Client) (context : Threads.Context) : Threads.Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8
      else context.registers register
    rip := client.returnTarget }

inductive WorkerControl (client : Client) (worker : Nat) (state : Suspend.State)
    (actual : TSO.Worker) : Prop where
  | running (point : Point) (current : Running client point actual.context)
      (live : actual.returned = false) (free : state.pending worker = none)
      (empty : actual.buffer = [])
  | entered (saved : Suspend.Saved) (pending : state.pending worker = some saved)
      (owner : saved.worker = worker) (family : client.Family saved.request)
      (context : actual.context = .ofState saved.request.user)
      (live : actual.returned = false) (empty : actual.buffer = [])
  | returned (context : Threads.Context) (observed : BitVec 32)
      (checked : Running client (.done observed) context)
      (historical : actual.context = client.returned context)
      (done : actual.returned = true) (free : state.pending worker = none)
      (empty : actual.buffer = [])

def retire (state : Suspend.State) (worker : Nat) (context : Threads.Context)
    (returned : Bool := false) : Suspend.State :=
  { state with machine := TSO.install state.machine worker state.machine.memory context returned [] }

theorem Running.initial (client : Client) : Running client .load client.entry := by
  exact ⟨⟨by intros; rfl, Or.inl rfl⟩, by simp [Point.offset], trivial⟩

theorem WorkerControl.initial (client : Client) (worker : Nat) (state : Suspend.State)
    (free : state.pending worker = none) :
    WorkerControl client worker state ⟨client.entry, false, []⟩ :=
  .running .load (Running.initial client) rfl free rfl

theorem Stable.register {client : Client} {context : Threads.Context}
    (stable : Stable client context) (register : Register)
    (rax : register ≠ .rax) (rsi : register ≠ .rsi)
    (rcx : register ≠ .rcx) (r11 : register ≠ .r11) :
    context.registers register = client.entry.registers register :=
  stable.1 register rax rsi rcx r11

theorem Running.rdi {client : Client} {point : Point} {context : Threads.Context}
    (current : Running client point context) :
    context.registers .rdi = client.entry.registers .rdi := by
  exact current.stable.register .rdi (by decide) (by decide) (by decide) (by decide)

theorem Running.rsp {client : Client} {point : Point} {context : Threads.Context}
    (current : Running client point context) :
    context.registers .rsp = client.entry.registers .rsp := by
  exact current.stable.register .rsp (by decide) (by decide) (by decide) (by decide)

theorem WorkerControl.frame {client : Client} {worker : Nat} {before after : Suspend.State}
    {actual : TSO.Worker} (control : WorkerControl client worker before actual)
    (pending : after.pending worker = before.pending worker) :
    WorkerControl client worker after actual := by
  cases control with
  | running point current live free empty =>
    exact .running point current live (pending.trans free) empty
  | entered saved savedAt owner family context live empty =>
    exact .entered saved (pending.trans savedAt) owner family context live empty
  | returned context observed checked historical done free empty =>
    exact .returned context observed checked historical done (pending.trans free) empty

theorem Family.classifies {client : Client} {request : SyscallRequest}
    (abi : client.ABI) (family : client.Family request) : classify request = .ok (.wait 0) := by
  obtain ⟨current, _⟩ := family
  obtain ⟨rdx, r10, r8, r9⟩ := abi
  have dx := current.stable.register .rdx (by decide) (by decide) (by decide) (by decide)
  have fourth := current.stable.register .r10 (by decide) (by decide) (by decide) (by decide)
  have fifth := current.stable.register .r8 (by decide) (by decide) (by decide) (by decide)
  have sixth := current.stable.register .r9 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨number, operation⟩ := current.fields
  simp only [Threads.Context.ofState] at dx fourth fifth sixth number operation
  simp [classify, number, operation, dx, fourth, fifth, sixth, rdx, r10, r8, r9]

theorem Family.continuation {client : Client} {request : SyscallRequest}
    (family : client.Family request) : request.continuation = client.entry.rip + 19 := by
  have rip : request.user.rip = client.entry.rip + 17 := family.1.rip
  rw [family.2, rip]
  simp [BitVec.add_assoc]

theorem retire_memory (state : Suspend.State) (worker : Nat) (context : Threads.Context)
    (returned : Bool) : (retire state worker context returned).machine.memory = state.machine.memory := rfl

theorem retire_peer {state : Suspend.State} {worker peer : Nat} {context : Threads.Context}
    {returned : Bool} (different : peer ≠ worker) :
    (retire state worker context returned).machine.workers[peer]? = state.machine.workers[peer]? := by
  exact List.getElem?_set_ne different.symm

theorem retire_selected {state : Suspend.State} {worker : Nat} {before : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some before) (context : Threads.Context)
    (returned : Bool := false) :
    (retire state worker context returned).machine.workers[worker]? = some ⟨context, returned, []⟩ :=
  List.getElem?_set_self (List.getElem_of_getElem? atWorker).1

end EDSL.OS.Futex.Predicate
