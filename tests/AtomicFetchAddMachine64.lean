/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAddMachine64
import EDSL.Audit

namespace EDSL.Tests.AtomicFetchAddMachine64
open X86 OS.AddressSpace OS.Atomics64

abbrev Managed := OS.Atomics64.State
abbrev Fault := OS.Atomics64.Fault

/-- The executable fixtures carry an invariant proved by the real resource
operations. This also lets enabledness run on a concrete current OS world. -/
structure Checked where
  state : Managed
  valid : WellFormed state

def seed : Checked :=
  ⟨empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty))),
    empty_wellFormed _ (OS.Atomics.empty_wellFormed _
      (OS.Borrowing.empty_wellFormed _ (OS.Ownership.empty_wellFormed _)))⟩

def change (before : Checked) (operation : OS.Ownership.Mutation) :
    Except Fault (Checked × Option OS.Ownership.Ticket) :=
  match success : mutate before.state operation with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, mutate_wellFormed _ _ _ before.valid success⟩, result.2)

def registerCell (before : Checked) (ticket : OS.Ownership.Ticket) :
    Except Fault (Checked × CellId64) :=
  match success : enroll before.state 7 ticket 65536 with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, (enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def issueHandle (before : Checked) (cell : CellId64) : Except Fault (Checked × HandleId64) :=
  match success : issue before.state 7 cell 11 with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, (issue_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def borrow (before : Checked) (owner : Nat) (ticket : OS.Ownership.Ticket) (region : Region) :
    Except Fault (Checked × Nat) :=
  match success : readBorrow before.state owner ticket 22 region with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, readBorrow_wellFormed _ _ _ _ _ _ before.valid success⟩, result.2)

def ticketFrom (output : Option OS.Ownership.Ticket) : Except Fault OS.Ownership.Ticket :=
  match output with
  | some ticket => .ok ticket
  | none => .error .missingCell

structure Ready where
  checked : Checked
  ticket : OS.Ownership.Ticket
  cell : CellId64
  handle : HandleId64
  callerLoan : Nat
  codeLoan : Nat

/-- The code qword contains LOCK XADD, RET, and two NOP bytes. The caller and
code each have a real live read loan. A separate readable replacement slot is
outside the caller loan, so raw CPU permission cannot stand in for OS authority. -/
def setup (old codeWord : Word) : Except Fault Ready := do
  let (allocated, output) ← change seed (.allocate 7 ⟨65536, 16⟩ readWrite)
  let ticket ← ticketFrom output
  let (neighbor, _) ← change allocated (.store64 7 ticket 65544 0x8877665544332211)
  let (written, _) ← change neighbor (.store64 7 ticket 65536 old)
  let (registered, cell) ← registerCell written ticket
  let (live, handle) ← issueHandle registered cell
  let (replacement, output) ← change live (.allocate 8 ⟨131072, 8⟩ readWrite)
  let replacementTicket ← ticketFrom output
  let (replacementWritten, _) ← change replacement
    (.store64 8 replacementTicket 131072 0xaabbccddeeff0011)
  let (replacementProtected, _) ← change replacementWritten (.protect 8 replacementTicket readOnly)
  let (caller, output) ← change replacementProtected (.allocate 9 ⟨196608, 8⟩ readWrite)
  let callerTicket ← ticketFrom output
  let (callerWritten, _) ← change caller (.store64 9 callerTicket 196608 0x0102030405060708)
  let (callerProtected, _) ← change callerWritten (.protect 9 callerTicket readOnly)
  let (callerLoaned, callerLoan) ← borrow callerProtected 9 callerTicket ⟨196608, 8⟩
  let (code, output) ← change callerLoaned (.allocate 10 ⟨262144, 8⟩ readWrite)
  let codeTicket ← ticketFrom output
  let (codeWritten, _) ← change code (.store64 10 codeTicket 262144 codeWord)
  let (executable, _) ← change codeWritten (.protect 10 codeTicket readExecute)
  let (guarded, codeLoan) ← borrow executable 10 codeTicket ⟨262144, 8⟩
  return ⟨guarded, ticket, cell, handle, callerLoan, codeLoan⟩

def cpu (state : Managed) (registers : List (Register × Word)) : X86.State where
  registers register := (registers.lookup register).getD 0xdeadbeef12345678
  rip := 262144
  flags := 0x200202
  memory := toMemory state.legacy.shared.resources.space

structure Execution where
  initial : X86.State
  instruction : X86.LockedAdd64.Instruction
  os : Managed × FetchAddEvent
  machine : X86.LockedAdd64.Observation

/-- Two independent operations on the same current world. Actual decoding
selects the OS input; the CPU independently fetches and decodes again in step. -/
def executeOn (state : Managed) (actor : Nat) (handle : HandleId64)
    (registers : List (Register × Word)) : Except Fault Execution := do
  let initial := cpu state registers
  let instruction ← (X86.LockedAdd64.decodeAt initial).mapError Fault.machine
  let os ← fetchAdd state actor handle (initial.registers instruction.source)
  let machine ← (X86.LockedAdd64.step initial).mapError Fault.machine
  return ⟨initial, instruction, os, machine⟩

def scenario (old codeWord : Word) (registers : List (Register × Word)) : Except Fault Execution := do
  let ready ← setup old codeWord
  executeOn ready.checked.state 11 ready.handle registers

structure ArithmeticView where
  os : FetchAddEvent
  machine : FetchAddEvent64
  registers : List Word
  flags : Word
  rip : Word
  osRead : Except Error Word
  cpuRead : Except Error Word
  accesses : List X86.LockedAdd64.Access

def view (execution : Execution) (registers : List Register) : ArithmeticView :=
  ⟨execution.os.2, execution.machine.event, registers.map execution.machine.state.registers,
    execution.machine.state.flags, execution.machine.state.rip,
    loadQWord (toMemory execution.os.1.legacy.shared.resources.space) 65536,
    loadQWord execution.machine.state.memory 65536, execution.machine.accesses⟩

def arithmetic (old codeWord : Word) (registers : List (Register × Word)) (selected : List Register) :=
  (scenario old codeWord registers).map (fun execution => view execution selected)

-- Frozen RAX returns the FULL old word; carry from bit31 changes the high half.
example : arithmetic 0x12345678ffffffff 0x9090c307c10f48f0
    [(.rdi,65536),(.rax,1),(.rsp,196608)] [.rax,.rdi,.rsp,.rbx] = .ok
    ⟨⟨11,⟨0⟩,⟨0⟩,⟨1,⟨65536,0x12345678ffffffff,0x1234567900000000⟩⟩⟩,
      ⟨1,⟨65536,0x12345678ffffffff,0x1234567900000000⟩⟩,
      [0x12345678ffffffff,65536,196608,0xdeadbeef12345678],0x200216,262149,
      .ok 0x1234567900000000,.ok 0x1234567900000000,[.rmw8 65536]⟩ := by rfl

-- Exact full64 wrap, including all six ADD flags and the full old response.
example : arithmetic 0xffffffffffffffff 0x9090c307c10f48f0
    [(.rdi,65536),(.rax,1)] [.rax] = .ok
    ⟨⟨11,⟨0⟩,⟨0⟩,⟨1,⟨65536,0xffffffffffffffff,0⟩⟩⟩,
      ⟨1,⟨65536,0xffffffffffffffff,0⟩⟩,[0xffffffffffffffff],0x200257,262149,
      .ok 0,.ok 0,[.rmw8 65536]⟩ := by rfl

-- Both high banks with ignored REX.X=1; low-bank RDI is deliberately unaligned.
example : arithmetic 0xffffffff 0x9090c307c10f4ff0
    [(.r15,65536),(.rdi,65537),(.r8,0x100000001),(.rax,99)] [.r8,.rax,.r15,.rdi] = .ok
    ⟨⟨11,⟨0⟩,⟨0⟩,⟨0x100000001,⟨65536,0xffffffff,0x200000000⟩⟩⟩,
      ⟨0x100000001,⟨65536,0xffffffff,0x200000000⟩⟩,[0xffffffff,99,65536,65537],
      0x200216,262149,.ok 0x200000000,.ok 0x200000000,[.rmw8 65536]⟩ := by rfl

-- An alias MUST use RDI's prestate value for both address and delta.
example : arithmetic 0x11223344ffff0000 0x9090c33fc10f48f0
    [(.rdi,65536),(.rax,77)] [.rdi,.rax] = .ok
    ⟨⟨11,⟨0⟩,⟨0⟩,⟨65536,⟨65536,0x11223344ffff0000,0x1122334500000000⟩⟩⟩,
      ⟨65536,⟨65536,0x11223344ffff0000,0x1122334500000000⟩⟩,
      [0x11223344ffff0000,77],0x200206,262149,
      .ok 0x1122334500000000,.ok 0x1122334500000000,[.rmw8 65536]⟩ := by rfl

-- High-bank source/base alias and a high old word exercise the generic bridge.
example : arithmetic 0x8000000000000000 0x9090c33fc10f4df0
    [(.r15,65536)] [.r15] = .ok
    ⟨⟨11,⟨0⟩,⟨0⟩,⟨65536,⟨65536,0x8000000000000000,0x8000000000010000⟩⟩⟩,
      ⟨65536,⟨65536,0x8000000000000000,0x8000000000010000⟩⟩,
      [0x8000000000000000],0x200286,262149,
      .ok 0x8000000000010000,.ok 0x8000000000010000,[.rmw8 65536]⟩ := by rfl

-- Signed overflow is distinct from unsigned carry, including AF and sign.
example : arithmetic 0x7fffffffffffffff 0x9090c307c10f48f0
    [(.rdi,65536),(.rax,1)] [.rax] = .ok
    ⟨⟨11,⟨0⟩,⟨0⟩,⟨1,⟨65536,0x7fffffffffffffff,0x8000000000000000⟩⟩⟩,
      ⟨1,⟨65536,0x7fffffffffffffff,0x8000000000000000⟩⟩,
      [0x7fffffffffffffff],0x200a96,262149,
      .ok 0x8000000000000000,.ok 0x8000000000000000,[.rmw8 65536]⟩ := by rfl

def resourceFrame := do
  let ready ← setup 0x12345678ffffffff 0x9090c307c10f48f0
  let execution ← executeOn ready.checked.state 11 ready.handle [(.rdi,65536),(.rax,1),(.rsp,196608)]
  let state := execution.os.1
  let memory := execution.machine.state.memory
  pure (loadQWord memory 65544, readWord memory 196608,
    OS.Borrowing.loadWord64 state.legacy.shared 22 ready.callerLoan 196608,
    OS.Borrowing.loadWord64 state.legacy.shared 22 ready.codeLoan 262144,
    [262144,262145,262146,262147,262148,262149,262150,262151].map memory.read,
    [65536,65543,65544,131072,196608,262144,262151].map memory.writable,
    [65536,65543,196608,262144,262151].map memory.executable,
    (state.nextCell,state.nextHandle,state.legacy.nextHandle,state.legacy.shared.nextLoan,
      state.legacy.shared.resources.frontier),
    [0,1,2,3].map state.legacy.shared.resources.allocations,
    state.cells ⟨0⟩,state.handles ⟨0⟩,
    [0,1].map state.legacy.shared.loans)

-- Post-mutation bytes, full permissions, actual loan reads, current allocation
-- owner/epoch/regions and all registry/loan frontiers have literal expectations.
example : resourceFrame = .ok
    (.ok 0x8877665544332211,.ok 0x0102030405060708,.ok 0x0102030405060708,
      .ok 0x9090c307c10f48f0,
      [some 0xf0,some 0x48,some 0x0f,some 0xc1,some 0x07,some 0xc3,some 0x90,some 0x90],
      [true,true,true,false,false,false,false],[false,false,false,true,true],
      (1,1,0,2,4),
      [some ⟨7,0,⟨65536,16⟩⟩,some ⟨8,0,⟨131072,8⟩⟩,some ⟨9,0,⟨196608,8⟩⟩,
        some ⟨10,0,⟨262144,8⟩⟩],
      some ⟨7,⟨0,0⟩,65536⟩,some ⟨11,⟨0⟩⟩,
      [some ⟨⟨2,0⟩,9,22,⟨196608,8⟩⟩,some ⟨⟨3,0⟩,10,22,⟨262144,8⟩⟩]) := by rfl

def sourceRSP := do
  let ready ← setup 131072 0x9090c327c10f48f0
  let execution ← executeOn ready.checked.state 11 ready.handle [(.rdi,65536),(.rsp,196608)]
  let shared := execution.os.1.legacy.shared
  let memory := execution.machine.state.memory
  pure (view execution [.rsp,.rdi],
    OS.Borrowing.loadWord64 shared 22 ready.callerLoan 196608,readWord memory 196608,
    OS.Borrowing.loadWord64 shared 22 ready.callerLoan (execution.machine.state.registers .rsp),
    readWord memory (execution.machine.state.registers .rsp),
    [131072,196608].map memory.writable,shared.loans ready.callerLoan)

-- RSP changes to the old value. The ORIGINAL slot/loan survive; a readable
-- replacement slot does NOT gain loan authority or write permission.
example : sourceRSP = .ok
    (⟨⟨11,⟨0⟩,⟨0⟩,⟨196608,⟨65536,131072,327680⟩⟩⟩,
      ⟨196608,⟨65536,131072,327680⟩⟩,[131072,65536],0x200206,262149,
      .ok 327680,.ok 327680,[.rmw8 65536]⟩,
      .ok 0x0102030405060708,.ok 0x0102030405060708,.error .outsideLoan,
      .ok 0xaabbccddeeff0011,[false,false],some ⟨⟨2,0⟩,9,22,⟨196608,8⟩⟩) := by rfl

def peerChange := do
  let ready ← setup 0xfffffffffffffffe 0x9090c307c10f48f0
  let (both, peer) ← issue ready.checked.state 7 ready.cell 12
  let (current, response) ← fetchAdd both 12 peer 3
  let execution ← executeOn current 11 ready.handle [(.rdi,65536),(.rax,0x100000000)]
  pure (response,view execution [.rax],loadQWord execution.machine.state.memory 65544)

-- The original handle predates the peer change. Both CPU and OS must read
-- current 1, not the old issuance-time word or a stale CPU memory snapshot.
example : peerChange = .ok
    (⟨12,⟨1⟩,⟨0⟩,⟨3,⟨65536,0xfffffffffffffffe,1⟩⟩⟩,
      ⟨⟨11,⟨0⟩,⟨0⟩,⟨0x100000000,⟨65536,1,0x100000001⟩⟩⟩,
        ⟨0x100000000,⟨65536,1,0x100000001⟩⟩,[1],0x200202,262149,
        .ok 0x100000001,.ok 0x100000001,[.rmw8 65536]⟩,.ok 0x8877665544332211) := by rfl

def withSpace (state : Managed) (space : Space) : Managed :=
  { state with legacy := { state.legacy with shared := { state.legacy.shared with
    resources := { state.legacy.shared.resources with space := space } } } }

def osEvent (operation : Except Fault (Managed × FetchAddEvent)) : Except Fault FetchAddEvent64 :=
  operation.map (fun result => result.2.arithmetic)

def cpuEvent (operation : Except Error X86.LockedAdd64.Observation) : Except Error FetchAddEvent64 :=
  operation.map (fun result => result.event)

/-- Deliberate external code interference after the original code/loan exists.
The CURRENT CPU and OS projection agree, and actual mutated ModRM selects RCX. -/
def mutatedDecode := do
  let ready ← setup 0x100000000 0x9090c307c10f48f0
  let current := withSpace ready.checked.state
    (writeQWordCells ready.checked.state.legacy.shared.resources.space 262144 0x9090c30fc10f48f0)
  let execution ← executeOn current 11 ready.handle [(.rdi,65536),(.rax,99),(.rcx,7)]
  pure ((execution.instruction.base,execution.instruction.source,execution.instruction.bytes),
    view execution [.rcx,.rax])

example : mutatedDecode = .ok
    ((.rdi,.rcx,[0xf0,0x48,0x0f,0xc1,0x0f]),
      ⟨⟨11,⟨0⟩,⟨0⟩,⟨7,⟨65536,0x100000000,0x100000007⟩⟩⟩,
        ⟨7,⟨65536,0x100000000,0x100000007⟩⟩,[0x100000000,99],0x200202,262149,
        .ok 0x100000007,.ok 0x100000007,[.rmw8 65536]⟩) := by rfl

def authorityFailures := do
  let ready ← setup 0x8000000000000001 0x9090c307c10f48f0
  let state := ready.checked.state
  let closed ← close state 11 ready.handle
  let (legacy, _) ← (OS.Atomics.mutate state.legacy (.transfer 7 ready.ticket 7)).mapError Fault.legacy
  let stale := { state with legacy := legacy }
  let raw := cpuEvent (X86.LockedAdd64.step (cpu state [(.rdi,65536),(.rax,0)]))
  pure (raw,
    [osEvent (fetchAdd state 12 ready.handle 0),osEvent (fetchAdd closed 11 ready.handle 0),
      osEvent (fetchAdd stale 11 ready.handle 0)],
    cpuEvent (X86.LockedAdd64.step (cpu closed [(.rdi,65536),(.rax,0)])),
    cpuEvent (X86.LockedAdd64.step (cpu stale [(.rdi,65536),(.rax,0)])))

-- Raw CPU permission remains sufficient for raw CPU execution after revocation
-- or epoch change. It does not authorize any corresponding OS transition.
example : authorityFailures = .ok
    (.ok ⟨0,⟨65536,0x8000000000000001,0x8000000000000001⟩⟩,
      [.error .wrongActor,.error .missingHandle,.error (.ownership .staleEpoch)],
      .ok ⟨0,⟨65536,0x8000000000000001,0x8000000000000001⟩⟩,
      .ok ⟨0,⟨65536,0x8000000000000001,0x8000000000000001⟩⟩) := by rfl

/-- Hostile registry edits preserve the raw bytes/permissions but change
current authority. Neither the old handle nor a readable neighbor repairs it. -/
def registryFailures := do
  let ready ← setup 9 0x9090c307c10f48f0
  let state := ready.checked.state
  let resources := state.legacy.shared.resources
  let wrongOwner := { state with legacy := { state.legacy with shared := { state.legacy.shared with
    resources := OS.Ownership.replace resources 0 (some ⟨8,0,⟨65536,16⟩⟩) } } }
  let short := { state with legacy := { state.legacy with shared := { state.legacy.shared with
    resources := OS.Ownership.replace resources 0 (some ⟨7,0,⟨65536,4⟩⟩) } } }
  pure (osEvent (fetchAdd wrongOwner 11 ready.handle 0),osEvent (fetchAdd short 11 ready.handle 0),
    cpuEvent (X86.LockedAdd64.step (cpu wrongOwner [(.rdi,65536),(.rax,0)])),
    cpuEvent (X86.LockedAdd64.step (cpu short [(.rdi,65536),(.rax,0)])))

example : registryFailures = .ok
    (.error (.ownership .wrongOwner),.error (.ownership .outsideAllocation),
      .ok ⟨0,⟨65536,9,9⟩⟩,.ok ⟨0,⟨65536,9,9⟩⟩) := by rfl

def deniedUpper (permissions : Permissions) := do
  let ready ← setup 0x8000000000000001 0x9090c307c10f48f0
  let current := withSpace ready.checked.state
    (protectUnchecked ready.checked.state.legacy.shared.resources.space ⟨65543,1⟩ permissions)
  pure (osEvent (fetchAdd current 11 ready.handle 0),
    cpuEvent (X86.LockedAdd64.step (cpu current [(.rdi,65536),(.rax,0)])))

example : deniedUpper readOnly = .ok
    (.error (.machine (.writeDenied 65536)),.error (.writeDenied 65536)) := by rfl
example : deniedUpper inaccessible = .ok
    (.error (.machine (.writeDenied 65536)),.error (.writeDenied 65536)) := by rfl
example : deniedUpper ⟨true,true,true⟩ = .ok
    (.error .executable,.error (.writeDenied 65536)) := by rfl

def missingUpper := do
  let ready ← setup 0x8000000000000001 0x9090c307c10f48f0
  let current := withSpace ready.checked.state
    (unmapUnchecked ready.checked.state.legacy.shared.resources.space ⟨65543,1⟩)
  pure (osEvent (fetchAdd current 11 ready.handle 0),
    cpuEvent (X86.LockedAdd64.step (cpu current [(.rdi,65536),(.rax,0)])))

example : missingUpper = .ok
    (.error (.machine (.writeDenied 65536)),.error (.writeDenied 65536)) := by rfl

def codeGate (opcode : Bool) := do
  let ready ← setup 0x100000000 0x9090c307c10f48f0
  let space := ready.checked.state.legacy.shared.resources.space
  let changed := if opcode then writeQWordCells space 262144 0x9090c307c00f48f0
    else protectUnchecked space ⟨262148,1⟩ readOnly
  let current := withSpace ready.checked.state changed
  pure (osEvent (fetchAdd current 11 ready.handle 1),
    cpuEvent (X86.LockedAdd64.step (cpu current [(.rdi,65536),(.rax,1)])))

-- Data authority alone cannot supply executable bytes or repair a changed
-- opcode. An expected frozen body would incorrectly execute these states.
example : codeGate false = .ok
    (.ok ⟨1,⟨65536,0x100000000,0x100000001⟩⟩,
      .error (.inaccessibleInstruction 262148)) := by rfl
example : codeGate true = .ok
    (.ok ⟨1,⟨65536,0x100000000,0x100000001⟩⟩,.error .unsupportedEncoding) := by rfl

/-- A real well-formed fixture with current code and original caller/code loans. -/
def frozenReady : Ready := (setup 0x12345678ffffffff 0x9090c307c10f48f0).toOption.get (by decide)
def frozenCPU := cpu frozenReady.checked.state [(.rdi,65536),(.rax,1),(.rsp,196608)]

-- Invoke enabledness using only current WF, current authorization, current
-- code and prestate operands. No successful fetchAdd or CPU mutation premise.
theorem current_enabled : ∃ result observation,
    FetchAddMachineEffect frozenReady.checked.state 11 frozenReady.handle frozenCPU
      X86.LockedAdd64.frozen result observation := by
  have authorized : authorize frozenReady.checked.state 11 frozenReady.handle =
      .ok (⟨11,frozenReady.cell⟩,⟨7,frozenReady.ticket,65536⟩) := by rfl
  have decoded : X86.LockedAdd64.decodeAt frozenCPU = .ok X86.LockedAdd64.frozen := by rfl
  obtain ⟨result, changed, _⟩ := fetchAdd_step_enabled_of_code _ _ _ _ _ _ _
    frozenReady.checked.valid authorized rfl (by rfl) (X86.LockedAdd64.decodeAt_code decoded)
  exact ⟨result, _, fetchAdd_step_effect _ _ _ _ _ _ _ _ changed authorized rfl (by rfl) decoded⟩

-- The converse starts with the actual CPU observation. Decoding, source input,
-- typed event equality, whole RAM coupling and the OS effect are recovered.
theorem current_converse (observation : X86.LockedAdd64.Observation)
    (stepped : X86.LockedAdd64.step frozenCPU = .ok observation) :
    ∃ instruction result, FetchAddMachineEffect frozenReady.checked.state 11 frozenReady.handle
      frozenCPU instruction result observation := by
  apply step_fetchAdd _ _ _ ⟨11,frozenReady.cell⟩ ⟨7,frozenReady.ticket,65536⟩ _ _
    frozenReady.checked.valid (by rfl) rfl _ stepped
  intro instruction decoded
  have actual : X86.LockedAdd64.decodeAt frozenCPU = .ok X86.LockedAdd64.frozen := by rfl
  have same := Except.ok.inj (decoded.symm.trans actual)
  subst instruction
  rfl

def rspReady : Ready := (setup 131072 0x9090c327c10f48f0).toOption.get (by decide)
def rspCPU := cpu rspReady.checked.state [(.rdi,65536),(.rsp,196608)]
def rspInstruction : X86.LockedAdd64.Instruction := ⟨0x48,0x27,by decide,by decide⟩

/-- A concrete client derives source-RSP execution and original caller safety
from CURRENT invariants and fetched code, then uses the joint effect's loan and
permission theorems. No future successful mutation is a premise. -/
theorem rsp_enabled_original_loan : ∃ result observation,
    FetchAddMachineEffect rspReady.checked.state 11 rspReady.handle rspCPU rspInstruction result observation ∧
    observation.state.registers .rsp = 131072 ∧
    OS.Borrowing.loadWord64 result.1.legacy.shared 22 rspReady.callerLoan 196608 =
      .ok 0x0102030405060708 ∧
    readWord observation.state.memory 196608 = .ok 0x0102030405060708 ∧
    OS.Borrowing.loadWord64 result.1.legacy.shared 22 rspReady.callerLoan
      (observation.state.registers .rsp) = .error .outsideLoan ∧
    observation.state.memory.writable (observation.state.registers .rsp) = false := by
  have authorized : authorize rspReady.checked.state 11 rspReady.handle =
      .ok (⟨11,rspReady.cell⟩,⟨7,rspReady.ticket,65536⟩) := by rfl
  have decoded : X86.LockedAdd64.decodeAt rspCPU = .ok rspInstruction := by rfl
  obtain ⟨result, changed, _⟩ := fetchAdd_step_enabled_of_code _ _ _ _ _ _ _
    rspReady.checked.valid authorized rfl (by rfl) (X86.LockedAdd64.decodeAt_code decoded)
  let observation : X86.LockedAdd64.Observation := ⟨result.2.arithmetic,
    X86.LockedAdd64.afterAdd rspCPU rspInstruction (toMemory result.1.legacy.shared.resources.space)
      result.2.arithmetic,[.rmw8 65536]⟩
  have effect : FetchAddMachineEffect rspReady.checked.state 11 rspReady.handle rspCPU
      rspInstruction result observation :=
    fetchAdd_step_effect _ _ _ _ _ _ _ _ changed authorized rfl (by rfl) decoded
  have address : result.2.arithmetic.event.address = 65536 := effect.cpu.address
  have old := effect.cpu.old
  rw [address] at old
  have present : loadQWord rspCPU.memory 65536 = .ok 131072 := by rfl
  have oldValue : result.2.arithmetic.event.before = 131072 :=
    Except.ok.inj (old.symm.trans present)
  have newRsp : observation.state.registers .rsp = 131072 := effect.source_old.trans oldValue
  have caller := effect.original_caller_loan rspReady.checked.valid 22 rspReady.callerLoan
    0x0102030405060708 (by rfl)
  have denied := effect.outside_original_loan 22 rspReady.callerLoan
    ⟨⟨2,0⟩,9,22,⟨196608,8⟩⟩ (observation.state.registers .rsp) (by rfl)
    (by rw [newRsp]; decide)
  refine ⟨result, observation, effect, newRsp, caller.1, caller.2.2, denied, ?_⟩
  rw [effect.permissions.2, newRsp]
  rfl

end EDSL.Tests.AtomicFetchAddMachine64

#audit_edsl
#print axioms EDSL.OS.Atomics64.fetchAdd_step
#print axioms EDSL.OS.Atomics64.fetchAdd_step_enabled
#print axioms EDSL.OS.Atomics64.fetchAdd_step_enabled_of_code
#print axioms EDSL.OS.Atomics64.step_fetchAdd
#print axioms EDSL.OS.Atomics64.FetchAddMachineEffect.original_caller_loan
#print axioms EDSL.OS.Atomics64.FetchAddMachineEffect.outside_original_loan
#print axioms EDSL.Tests.AtomicFetchAddMachine64.current_enabled
#print axioms EDSL.Tests.AtomicFetchAddMachine64.current_converse
#print axioms EDSL.Tests.AtomicFetchAddMachine64.rsp_enabled_original_loan
