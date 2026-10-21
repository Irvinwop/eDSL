/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures

/-!
Checked two-allocation shared-cell setup for finite scalar-RAM, long-mode,
CET-off scheduler clients. The original fixture retains its code/caller loans
and private grants. Cell B receives a separate checked allocation, registration
and one current handle per actor; neither actor receives an ordinary B grant.
-/

set_option autoImplicit false

namespace EDSL.Tests.TSO64CrossCellFixtures
open X86 OS.AddressSpace OS.TSO64

abbrev Fault := OS.TSO64.Fault

/-- 89 31; 48 89 37; 48 89 32; f0 48 0f c1 32; c3.
MOV dword [RCX],ESI; MOV qword [RDI],RSI; MOV qword [RDX],RSI;
LOCK XADD qword [RDX],RSI; RET. The dword form is required by the existing
natural-alignment gate at privateData+4.
Instruction offsets are 0, 2, 5, 8, 13; the remaining two bytes are zero. -/
def codeFirst : Word := 0x3289483789483189
def codeSecond : Word := 0x0000c332c10f48f0
def peerOffset : Nat := 5

def enrollSecond (before : TSO64.Checked) (ticket : OS.Ownership.Ticket) :
    Except TSO64.OSFault (TSO64.Checked × OS.Atomics64.CellId64) :=
  match success : OS.Atomics64.enroll before.world 7 ticket 458752 with
  | .error fault => .error fault
  | .ok result =>
    .ok (⟨result.1,
      (OS.Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

structure Ready where
  original : TSO64.Ready
  checked : TSO64.Checked
  secondA : OS.Atomics64.HandleId64
  secondB : OS.Atomics64.HandleId64

def fixture (first second oldA oldB : Word) : Except TSO64.OSFault Ready := do
  let original ← TSO64.fixture first second oldA
  let (allocated, out) ← TSO64.change original.checked (.allocate 7 ⟨458752, 8⟩ readWrite)
  let ticket ← TSO64.ticket out
  let (initialized, _) ← TSO64.change allocated (.store64 7 ticket 458752 oldB)
  let (registered, cell) ← enrollSecond initialized ticket
  let (one, secondA) ← TSO64.handle registered cell 11
  let (two, secondB) ← TSO64.handle one cell 12
  return ⟨original, two, secondA, secondB⟩

/-- RDX selects the separate cell B; RCX keeps the original privateData+4.
The original RDI, RSI, RAX, stack, flags and other registers are retained. -/
def context (stack privateData delta : Word) (offset : Nat) : Context :=
  { TSO64.context stack privateData delta 5 with
    registers := fun register =>
      if register = .rdx then 458752
      else (TSO64.context stack privateData delta 5).registers register
    rip := 393216 + BitVec.ofNat 64 offset }

/-- Fixed public fixture entry point. Both attachments check the complete
current resources in the final two-cell world. -/
def start (first second oldA oldB deltaA deltaB : Word) (offsetA offsetB : Nat) :
    Except Fault OS.TSO64.State := do
  let ready ← (fixture first second oldA oldB).mapError Fault.os
  let one ← attach ⟨ready.checked.world, []⟩ 11 (context 262144 131072 deltaA offsetA)
    ready.original.codeA ready.original.callerA [ready.original.dataA]
    [ready.original.atomicA, ready.secondA]
  attach one 12 (context 327680 196608 deltaB offsetB)
    ready.original.codeB ready.original.callerB [ready.original.dataB]
    [ready.original.atomicB, ready.secondB]

private theorem empty_valid (world : World) (valid : OS.Atomics64.WellFormed world) :
    WellFormed ⟨world, []⟩ .sharedCell := by
  refine ⟨valid, ?_⟩
  intro worker absent
  cases absent

/-- Full global validity comes from checked mutations, enrollment, handle
issuance and both actual attachments, for every successful parameterization. -/
theorem start_valid {first second oldA oldB deltaA deltaB : Word} {offsetA offsetB : Nat}
    {state : OS.TSO64.State}
    (success : start first second oldA oldB deltaA deltaB offsetA offsetB = .ok state) :
    WellFormed state .sharedCell := by
  cases setup : fixture first second oldA oldB with
  | error fault => simp [start, setup, Except.mapError] at success
  | ok ready =>
    have attached : (do
        let one ← attach ⟨ready.checked.world, []⟩ 11 (context 262144 131072 deltaA offsetA)
          ready.original.codeA ready.original.callerA [ready.original.dataA]
          [ready.original.atomicA, ready.secondA]
        attach one 12 (context 327680 196608 deltaB offsetB)
          ready.original.codeB ready.original.callerB [ready.original.dataB]
          [ready.original.atomicB, ready.secondB]) = .ok state := by
      simpa only [start, setup, Except.mapError, ok_bind] using success
    cases one : attach ⟨ready.checked.world, []⟩ 11 (context 262144 131072 deltaA offsetA)
        ready.original.codeA ready.original.callerA [ready.original.dataA]
        [ready.original.atomicA, ready.secondA] with
    | error fault =>
      rw [one] at attached
      cases attached
    | ok firstState =>
      have final : attach firstState 12 (context 327680 196608 deltaB offsetB)
          ready.original.codeB ready.original.callerB [ready.original.dataB]
          [ready.original.atomicB, ready.secondB] = .ok state := by
        simpa only [one, ok_bind] using attached
      exact attach_valid_for .sharedCell
        (attach_valid_for .sharedCell (empty_valid _ ready.checked.valid) one) final

end EDSL.Tests.TSO64CrossCellFixtures
