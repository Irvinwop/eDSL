/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Setup

namespace EDSL.Tests.TSO64
open X86 OS.AddressSpace OS.TSO64

abbrev Managed := OS.Atomics64.State
abbrev OSFault := OS.Atomics64.Fault
abbrev Scheduler := OS.TSO64.State
abbrev SchedulerFault := OS.TSO64.Fault

structure Checked where
  world : Managed
  valid : OS.Atomics64.WellFormed world

def seed : Checked :=
  ⟨OS.Atomics64.empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty))),
    OS.Atomics64.empty_wellFormed _ (OS.Atomics.empty_wellFormed _
      (OS.Borrowing.empty_wellFormed _ (OS.Ownership.empty_wellFormed _)))⟩

def change (before : Checked) (operation : OS.Ownership.Mutation) :
    Except OSFault (Checked × Option OS.Ownership.Ticket) :=
  match success : OS.Atomics64.mutate before.world operation with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, OS.Atomics64.mutate_wellFormed _ _ _ before.valid success⟩, result.2)

def enroll (before : Checked) (ticket : OS.Ownership.Ticket) :
    Except OSFault (Checked × OS.Atomics64.CellId64) :=
  match success : OS.Atomics64.enroll before.world 7 ticket 65536 with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, (OS.Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def handle (before : Checked) (cell : OS.Atomics64.CellId64) (actor : Nat) :
    Except OSFault (Checked × OS.Atomics64.HandleId64) :=
  match success : OS.Atomics64.issue before.world 7 cell actor with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, (OS.Atomics64.issue_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def borrow (before : Checked) (lender : Nat) (ticket : OS.Ownership.Ticket)
    (actor : Nat) (region : Region) : Except OSFault (Checked × Nat) :=
  match success : OS.Atomics64.readBorrow before.world lender ticket actor region with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, OS.Atomics64.readBorrow_wellFormed _ _ _ _ _ _ before.valid success⟩, result.2)

def ticket (value : Option OS.Ownership.Ticket) : Except OSFault OS.Ownership.Ticket :=
  match value with
  | none => .error .missingCell
  | some value => .ok value

structure Ready where
  checked : Checked
  codeA : Nat
  codeB : Nat
  callerA : Nat
  callerB : Nat
  dataA : OS.Ownership.Ticket
  dataB : OS.Ownership.Ticket
  atomicA : OS.Atomics64.HandleId64
  atomicB : OS.Atomics64.HandleId64

/-- Project-owned synthetic programs and mappings, installed with the actual
checked resource operations. The program words are parameters to the fixture,
never dispatch inputs to the scheduler. -/
def fixture (first second old : Word) : Except OSFault Ready := do
  let (atomic, out) ← change seed (.allocate 7 ⟨65536, 16⟩ readWrite)
  let atomicTicket ← ticket out
  let (initialized, _) ← change atomic (.store64 7 atomicTicket 65536 old)
  let (neighbor, _) ← change initialized (.store64 7 atomicTicket 65544 0xabcdef0123456789)
  let (registered, cell) ← enroll neighbor atomicTicket
  let (one, atomicA) ← handle registered cell 11
  let (two, atomicB) ← handle one cell 12
  let (dataOne, out) ← change two (.allocate 11 ⟨131072, 16⟩ readWrite)
  let dataA ← ticket out
  let (dataTwo, out) ← change dataOne (.allocate 12 ⟨196608, 16⟩ readWrite)
  let dataB ← ticket out
  let (stackOne, out) ← change dataTwo (.allocate 21 ⟨262144, 8⟩ readWrite)
  let stackA ← ticket out
  let (writtenA, _) ← change stackOne (.store64 21 stackA 262144 0x7000)
  let (protectedA, _) ← change writtenA (.protect 21 stackA readOnly)
  let (loanA, callerA) ← borrow protectedA 21 stackA 11 ⟨262144, 8⟩
  let (stackTwo, out) ← change loanA (.allocate 22 ⟨327680, 8⟩ readWrite)
  let stackB ← ticket out
  let (writtenB, _) ← change stackTwo (.store64 22 stackB 327680 0x8000)
  let (protectedB, _) ← change writtenB (.protect 22 stackB readOnly)
  let (loanB, callerB) ← borrow protectedB 22 stackB 12 ⟨327680, 8⟩
  let (code, out) ← change loanB (.allocate 23 ⟨393216, 16⟩ readWrite)
  let codeTicket ← ticket out
  let (low, _) ← change code (.store64 23 codeTicket 393216 first)
  let (high, _) ← change low (.store64 23 codeTicket 393224 second)
  let (executable, _) ← change high (.protect 23 codeTicket readExecute)
  let (codeOne, codeA) ← borrow executable 23 codeTicket 11 ⟨393216, 16⟩
  let (codeTwo, codeB) ← borrow codeOne 23 codeTicket 12 ⟨393216, 16⟩
  return ⟨codeTwo, codeA, codeB, callerA, callerB, dataA, dataB, atomicA, atomicB⟩

def context (stack data delta initial : Word) : Context where
  registers register := match register with
    | .rsp => stack
    | .rdi => 65536
    | .rdx => data
    | .rcx => data + 4
    | .rsi => delta
    | .rax => initial
    | _ => 0x8877665544332211
  rip := 393216
  flags := 0x200202

def start (ready : Ready) (deltaA deltaB initial : Word) : Except SchedulerFault Scheduler := do
  let first ← attach ⟨ready.checked.world, []⟩ 11 (context 262144 131072 deltaA initial)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  attach first 12 (context 327680 196608 deltaB initial)
    ready.codeB ready.callerB [ready.dataB] [ready.atomicB]

def run (first second old deltaA deltaB initial : Word) (actions : List Action) :
    Except SchedulerFault (Scheduler × List Observation) := do
  let ready ← (fixture first second old).mapError OS.TSO64.Fault.os
  let state ← start ready deltaA deltaB initial
  schedule state actions

def events (observations : List Observation) : List (Nat × Word × Word × Word) :=
  observations.filterMap fun observation => match observation with
    | .rmw tid event => some (tid, event.arithmetic.delta, event.arithmetic.event.before, event.arithmetic.event.after)
    | _ => none

def workerView (state : Scheduler) (tid : Nat) : Option (List Word × Word × Word × Phase × Nat) :=
  state.workers[tid]?.map fun worker =>
    ([.rax, .rbx, .rdi, .rsi, .rsp].map worker.context.registers,
      worker.context.rip, worker.context.flags, worker.phase, worker.pending.length)

end EDSL.Tests.TSO64
