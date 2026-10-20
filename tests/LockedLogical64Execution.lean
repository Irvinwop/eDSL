/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedLogical64.Execution
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.LockedLogical64Execution
open X86
open X86.LockedLogical64

/-- Independent bit membership specification for any indexed event emitted by
an entire actual execution. The old word is read at that instruction's current
memory, rather than captured from the entry state or inferred from the mask. -/
theorem event_current_union {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {position : Nat} {label : LogicalEvent64}
    (present : result.events[position]? = some label) (bit : Fin 64) :
    ∃ before middle priorEvents priorAccesses accesses,
      Block choices initial before position priorEvents priorAccesses ∧
      step (choices position) before = .ok ⟨.atomic64 label middle, accesses⟩ ∧
      loadQWord before.memory label.event.address = .ok label.event.before ∧
      (label.event.after.toNat.testBit bit = true ↔
        label.event.before.toNat.testBit bit = true ∨
          (before.registers .rsi).toNat.testBit bit = true) := by
  obtain ⟨before, middle, priorEvents, priorAccesses, accesses, preceding, actual, _, effect⟩ :=
    execution.event_origin present
  refine ⟨before, middle, priorEvents, priorAccesses, accesses, preceding, actual,
    effect.transition.2.2.1, ?_⟩
  rw [effect.value]
  simp [BitVec.testBit_toNat]

/-- Exact RET accounting prevents losing no-change RMW events or inventing a
terminal RMW. This applies to arbitrary actual successful executions. -/
theorem no_lost_event {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) :
    result.events.length + 1 = result.accesses.length := by
  rw [execution.access_count]
  exact execution.event_count

/-- Two sequential ORs deliberately make the second RMW a no-change event.
The literal bytes encode OR/OR/RET; the caller slot is a separate eight-byte
object and the initial word has nonzero high bits. -/
def entry : State where
  registers register := match register with
    | .rdi => 65536
    | .rsi => 0x8000000200000002
    | .rsp => 32768
    | .rax => 0xcafef00d98765432
    | _ => 0x123456789abcdef0
  rip := 4096
  flags := 0xed7
  memory := {
    read := fun address => match address.toNat with
      | 4096 | 4100 => some 0xf0
      | 4097 | 4101 => some 0x48
      | 4098 | 4102 => some 0x09
      | 4099 | 4103 => some 0x37
      | 4104 => some 0xc3
      | 32768 => some 0x34
      | 32769 => some 0x12
      | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0
      | 65535 => some 0x5a
      | 65536 | 65543 => some 1
      | 65537 | 65538 | 65539 | 65540 | 65541 | 65542 => some 0
      | 65544 => some 0xa5
      | _ => none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4105)
    writable := fun address => decide (65536 ≤ address.toNat ∧ address.toNat < 65544) }

structure View where
  events : List LogicalEvent64
  accesses : List Access
  instructions : Nat
  rip : Word
  rsp : Word
  rax : Word
  flagsExceptAF : Word
  af : Bool
  bytes : List (Option Byte)
  deriving DecidableEq, Repr

def observe (first second last : Bool) (fuel : Nat) (initial : State := entry) : Except Error View := do
  let result ← run (fun index => if index = 0 then first else if index = 1 then second else last) fuel initial
  return ⟨result.events, result.accesses, result.instructions, result.state.rip,
    result.state.registers .rsp, result.state.registers .rax,
    result.state.flags &&& ~~~(0x10 : Word), result.state.flags.getLsbD 4,
    [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map result.state.memory.read⟩

/-- Ordered old/new labels catch event erasure, reordering and entry-memory
reuse. Final AF is the second instruction's choice, even when RET's differs;
current RAM, caller-slot use, preserved RAX and neighboring bytes are observed. -/
theorem sequential_trace (first second last : Bool) : observe first second last 3 = .ok {
    events := [
      ⟨.bor,0x8000000200000002,⟨65536,0x0100000000000001,0x8100000200000003⟩⟩,
      ⟨.bor,0x8000000200000002,⟨65536,0x8100000200000003,0x8100000200000003⟩⟩]
    accesses := [.rmw8 65536,.rmw8 65536,.stack8 32768]
    instructions := 3
    rip := 0x1234
    rsp := 32776
    rax := 0xcafef00d98765432
    flagsExceptAF := 0x686
    af := second
    bytes := [some 0x5a,some 3,some 0,some 0,some 0,some 2,some 0,some 0,some 0x81,some 0xa5] } := by
  cases first <;> cases second <;> cases last <;> rfl

/-- The finite observation regressions cover every possible AF stream, not
just a chosen default. Stream suffixes beyond the three retired instructions
cannot influence this returning execution. -/
theorem entry_all_choices : AllExecutions entry (fun result =>
    result.events.length = 2 ∧ result.instructions = 3) := by
  intro choices
  let chosen : Choices := fun index =>
    if index = 0 then choices 0 else if index = 1 then choices 1 else choices 2
  have agree : choices.Agree chosen 3 := by
    intro index bound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> simp [chosen]
  have trace := sequential_trace (choices 0) (choices 1) (choices 2)
  have same := run_choices_congr (initial := entry) agree
  change (do
    let result ← run chosen 3 entry
    pure (⟨result.events, result.accesses, result.instructions, result.state.rip,
      result.state.registers .rsp, result.state.registers .rax,
      result.state.flags &&& ~~~(0x10 : Word), result.state.flags.getLsbD 4,
      [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map result.state.memory.read⟩ : View)) = _ at trace
  rw [←same] at trace
  cases actual : run choices 3 entry with
  | error fault => simp [actual] at trace
  | ok result =>
    simp only [actual, ok_bind, pure_ok, Except.ok.injEq, View.mk.injEq] at trace
    refine ⟨result, run_sound actual, ?_⟩
    have events : result.events.length = 2 := by rw [trace.1]; rfl
    have count : result.instructions = 3 := trace.2.2.1
    exact ⟨events, count⟩

-- A completed run ignores extra fuel; the smallest sufficient fuel is three.
example (first second last : Bool) : observe first second last 12 = observe first second last 3 := by
  cases first <;> cases second <;> cases last <;> rfl
example (first second last : Bool) : observe first second last 2 = .error .exhaustedFuel := by
  cases first <;> cases second <;> cases last <;> rfl

/-- A high-byte denial still fails a no-change RMW. The exact first fault wins
over unused future choices, future stack errors and unused recursive fuel. -/
def denied : State := { entry with
  memory := { entry.memory with
    writable := fun address => address != 65543 && entry.memory.writable address }
  registers := fun register => if register = .rsi then 0 else entry.registers register }

example (first second last : Bool) : observe first second last 3 denied =
    .error (.writeDenied 65536) := by
  cases first <;> cases second <;> cases last <;> rfl

/-- A failing RET reports its actual current caller-slot fault, after both
RMWs, rather than converting the failed step into a retired instruction. -/
def missingStack : State := { entry with memory := { entry.memory with
  read := fun address => if address = 32775 then none else entry.memory.read address } }

example (first second last : Bool) : observe first second last 3 missingStack =
    .error (.inaccessibleStack 32775) := by
  cases first <;> cases second <;> cases last <;> rfl

end EDSL.Tests.LockedLogical64Execution

#audit_edsl
