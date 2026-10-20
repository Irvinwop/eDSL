/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedSet64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.LockedSet64
open X86
open X86.LockedSet64

/-- Independent natural-number bit membership, including exclusive membership
for XOR. No expected result calls `LogicalOp.eval`. -/
def NaturalBit (op : Sequential.LogicalOp) (left right index : Nat) : Prop :=
  match op with
  | .band => left.testBit index = true ∧ right.testBit index = true
  | .bor => left.testBit index = true ∨ right.testBit index = true
  | .bxor => left.testBit index ≠ right.testBit index

/-- Every indexed event is tied to its decoded opcode and its actual current
read. This checks all 64 natural-number bits for all three instructions. -/
theorem event_natural_bits {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {index : Nat} {label : LogicalEvent64}
    (present : result.events[index]? = some label) (bit : Fin 64) :
    ∃ before middle priorEvents priorAccesses accesses op,
      Block choices initial before index priorEvents priorAccesses ∧
      LockedSet64.decodeAt before = .ok (.logicalRdiRsi op) ∧
      step (choices index) before = .ok ⟨.atomic64 label middle, accesses⟩ ∧
      loadQWord before.memory label.event.address = .ok label.event.before ∧
      label.op = op ∧ label.mask = before.registers .rsi ∧
      (label.event.after.toNat.testBit bit = true ↔
        NaturalBit op label.event.before.toNat (before.registers .rsi).toNat bit) := by
  obtain ⟨before, middle, priorEvents, priorAccesses, accesses, block, actual, _,
    op, decoded, effect⟩ := execution.event_origin present
  refine ⟨before, middle, priorEvents, priorAccesses, accesses, op, block, decoded, actual,
    effect.transition.2.2.1, effect.op, effect.mask, ?_⟩
  rw [effect.value]
  cases op <;> simp [NaturalBit, Sequential.LogicalOp.eval, BitVec.testBit_toNat]

private def registers (mask : Word) : Register → Word
  | .rdi => 65536
  | .rsi => mask
  | .rsp => 32768
  | .rax => 0xcafef00d98765432
  | _ => 0x123456789abcdef0

/-- The fixture encodes data by natural division, independently of the
backend's extraction/store helper. RX code, RW data and caller slots are disjoint. -/
def entry (code : List Byte) (old mask : Word) : State where
  registers := registers mask
  rip := 4096
  flags := 0xed7
  memory := {
    read := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then
        code[address.toNat - 4096]?
      else if 65536 ≤ address.toNat ∧ address.toNat < 65544 then
        some (BitVec.ofNat 8 (old.toNat / 256 ^ (address.toNat - 65536)))
      else match address.toNat with
        | 32768 => some 0x34
        | 32769 => some 0x12
        | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0
        | 65535 => some 0x5a
        | 65544 => some 0xa5
        | _ => none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
    writable := fun address => decide (65536 ≤ address.toNat ∧ address.toNat < 65544) }

private def snapshot (state : State) : List Word :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15].map state.registers

structure RmwView where
  event : LogicalEvent64
  word : Except Error Word
  flagsExceptAF : Word
  af : Bool
  rip : Word
  accesses : List Access
  gprsUnchanged : Bool
  permissionsUnchanged : Bool
  neighbors : List (Option Byte)

def observeRmw (af : Bool) (initial : State) : Except Error RmwView := do
  let observation ← step af initial
  match observation.result with
  | .returned _ => throw .unexpectedReturn
  | .atomic64 label final =>
    return ⟨label, loadQWord final.memory 65536, final.flags &&& ~~~(0x10 : Word),
      final.flags.getLsbD 4, final.rip, observation.accesses,
      snapshot final == snapshot initial,
      [4096,4097,4098,4099,32768,32775,65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].all
        (fun address => (final.memory.writable address == initial.memory.writable address) &&
          (final.memory.executable address == initial.memory.executable address)),
      [65535,65544].map final.memory.read⟩

private def expected (op : Sequential.LogicalOp) (before mask after flags : Word)
    (af : Bool) : Except Error RmwView := .ok
  ⟨⟨op, mask, ⟨65536, before, after⟩⟩, .ok after, flags, af, 4100,
    [.rmw8 65536], true, true, [some 0x5a, some 0xa5]⟩

/-- Literal oracles distinguish opcodes, all high/low halves, bit 63, width,
SF/ZF/PF/CF/OF, all GPRs, permissions, RIP and the full-width memory result. -/
theorem full_width_vectors (af : Bool) :
    ([0x21,0x09,0x31] : List Byte).map (fun opcode =>
      observeRmw af (entry [0xf0,0x48,opcode,0x37]
        0x80000001000000f0 0x800000020000003c)) =
    [expected .band 0x80000001000000f0 0x800000020000003c 0x8000000000000030 0x686 af,
     expected .bor  0x80000001000000f0 0x800000020000003c 0x80000003000000fc 0x686 af,
     expected .bxor 0x80000001000000f0 0x800000020000003c 0x00000003000000cc 0x606 af] := by
  cases af <;> rfl

theorem zero_and_unchanged_events (af : Bool) :
    ([(0x21,0x80000001000000f0,0),
      (0x09,0x80000001000000f0,0), (0x31,0x80000001000000f0,0),
      (0x21,0x80000001000000f0,0xffffffffffffffff),
      (0x09,0x80000001000000f0,0x80000001000000f0),
      (0x31,0x80000001000000f0,0x80000001000000f0),
      (0x21,0x100000000,0x100000000), (0x09,0,0x8000000000000001)] :
      List (Byte × Word × Word)).map (fun (opcode,old,mask) =>
        observeRmw af (entry [0xf0,0x48,opcode,0x37] old mask)) =
    [expected .band 0x80000001000000f0 0 0 0x646 af,
     expected .bor 0x80000001000000f0 0 0x80000001000000f0 0x686 af,
     expected .bxor 0x80000001000000f0 0 0x80000001000000f0 0x686 af,
     expected .band 0x80000001000000f0 0xffffffffffffffff 0x80000001000000f0 0x686 af,
     expected .bor 0x80000001000000f0 0x80000001000000f0 0x80000001000000f0 0x686 af,
     expected .bxor 0x80000001000000f0 0x80000001000000f0 0 0x646 af,
     expected .band 0x100000000 0x100000000 0x100000000 0x606 af,
     expected .bor 0 0x8000000000000001 0x8000000000000001 0x682 af] := by
  cases af <;> rfl

/-- General preservation includes flag bits outside the arithmetic mask,
not just the sampled flags and registers of the executable regressions. -/
theorem complete_preservation {initial final : State} {op : Sequential.LogicalOp}
    {af : Bool} {label : LogicalEvent64} {accesses : List Access}
    (success : execute initial (.logicalRdiRsi op) af = .ok ⟨.atomic64 label final, accesses⟩) :
    final.registers = initial.registers ∧
    final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask ∧
    (∀ offset, offset < 8 →
      initial.memory.writable (label.event.address + BitVec.ofNat 64 offset) = true ∧
      (initial.memory.read (label.event.address + BitVec.ofNat 64 offset)).isSome = true ∧
      initial.memory.executable (label.event.address + BitVec.ofNat 64 offset) = false) := by
  have effect := execute_logical_sound success
  exact ⟨effect.registers, effect.nonarithmetic_flags, effect.full_permissions⟩

inductive Denial where
  | missing | readonly | executable

def denyByte (mode : Denial) (offset : Nat) (initial : State) : State :=
  let target : Word := 65536 + BitVec.ofNat 64 offset
  match mode with
  | .missing => { initial with memory := { initial.memory with
      read := fun address => if address = target then none else initial.memory.read address } }
  | .readonly => { initial with memory := { initial.memory with
      writable := fun address => if address = target then false else initial.memory.writable address } }
  | .executable => { initial with memory := { initial.memory with
      executable := fun address => if address = target then true else initial.memory.executable address } }

private def isWriteDenied : Except Error α → Bool
  | .error (.writeDenied address) => address == 65536
  | _ => false

/-- Tests all eight positions for each opcode, with zero old/mask so all
three operations would be unchanged. None may bypass the RMW preflight. -/
def deniedBytes (mode : Denial) (af : Bool) : List (List Bool) :=
  ([0x21,0x09,0x31] : List Byte).map fun opcode =>
    (List.range 8).map fun offset =>
      isWriteDenied (step af (denyByte mode offset (entry [0xf0,0x48,opcode,0x37] 0 0)))

theorem missing_every_byte (af : Bool) :
    deniedBytes .missing af = List.replicate 3 (List.replicate 8 true) := by
  cases af <;> rfl

theorem nonwritable_every_byte (af : Bool) :
    deniedBytes .readonly af = List.replicate 3 (List.replicate 8 true) := by
  cases af <;> rfl

theorem executable_every_byte (af : Bool) :
    deniedBytes .executable af = List.replicate 3 (List.replicate 8 true) := by
  cases af <;> rfl

private def unsupported : Except Error α → Bool
  | .error .unsupportedEncoding => true
  | _ => false

/-- Literal malformed encodings exercise wrong widths, register direction,
ModRM/bank, immediate forms, duplicate/reordered prefixes and LOCK RET. -/
def malformed (opcode : Byte) : List (List Byte) :=
  [[0x48,opcode,0x37], [0xf0,opcode,0x37], [0xf0,0x40,opcode,0x37],
   [0xf0,0x49,opcode,0x37], [0xf0,0x4c,opcode,0x37], [0xf0,0x48,opcode,0xf7],
   [0xf0,0x48,opcode,0x36], [0xf0,0x48,opcode,0x3f], [0xf0,0x48,opcode,0x77,0],
   [0xf0,0xf0,0x48,opcode,0x37], [0x48,0xf0,opcode,0x37],
   [0x66,0xf0,0x48,opcode,0x37], [0x67,0xf0,0x48,opcode,0x37],
   [0xf0,0x48,0x81,0x27,0,0,0,0], [0xf0,0xc3],
   [0xf0,0x48,0x23,0x37], [0xf0,0x48,0x0b,0x37], [0xf0,0x48,0x33,0x37]]

theorem malformed_rejected :
    ([0x21,0x09,0x31] : List Byte).map (fun opcode =>
      (malformed opcode).map (fun bytes => unsupported (LockedSet64.decodeAt (entry bytes 0 0)))) =
    List.replicate 3 (List.replicate 18 true) := by rfl

theorem truncated_exact_faults :
    ([[],[0xf0],[0xf0,0x48],[0xf0,0x48,0x21],[0xf0,0x48,0x09],[0xf0,0x48,0x31]] :
      List (List Byte)).map (fun bytes => LockedSet64.decodeAt (entry bytes 0 0)) =
    [.error (.inaccessibleInstruction 4096), .error (.inaccessibleInstruction 4097),
     .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099),
     .error (.inaccessibleInstruction 4099), .error (.inaccessibleInstruction 4099)] := by rfl

/-- No padding is fetched after RET; only the real current stack slot matters. -/
theorem ret_only (af : Bool) :
    step af (entry [0xc3] 0 0) = .ok ⟨.returned
      { (entry [0xc3] 0 0).writeRegister .rsp 32776 with rip := 0x1234 },
      [.stack8 32768]⟩ := by rfl

def routine : State := entry
  [0xf0,0x48,0x21,0x37, 0xf0,0x48,0x09,0x37,
   0xf0,0x48,0x09,0x37, 0xf0,0x48,0x31,0x37, 0xc3]
  0x0100000000000001 0x8000000200000002

structure RoutineView where
  events : List LogicalEvent64
  accesses : List Access
  instructions : Nat
  rip : Word
  rsp : Word
  registersCorrect : Bool
  flagsExceptAF : Word
  af : Bool
  bytes : List (Option Byte)
  codeUnchanged : Bool

def routineView (initial : State) (result : Result) : RoutineView :=
  ⟨result.events, result.accesses, result.instructions, result.state.rip,
    result.state.registers .rsp,
    snapshot result.state == snapshot (initial.writeRegister .rsp 32776),
    result.state.flags &&& ~~~(0x10 : Word), result.state.flags.getLsbD 4,
    [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map result.state.memory.read,
    (List.range 17).all (fun offset =>
      result.state.memory.read (4096 + BitVec.ofNat 64 offset) ==
        initial.memory.read (4096 + BitVec.ofNat 64 offset))⟩

def stream (first second third fourth last : Bool) : Choices := fun index =>
  if index = 0 then first else if index = 1 then second else if index = 2 then third
  else if index = 3 then fourth else last

def routineExpected (af : Bool) : RoutineView := {
  events := [
    ⟨.band,0x8000000200000002,⟨65536,0x0100000000000001,0⟩⟩,
    ⟨.bor,0x8000000200000002,⟨65536,0,0x8000000200000002⟩⟩,
    ⟨.bor,0x8000000200000002,⟨65536,0x8000000200000002,0x8000000200000002⟩⟩,
    ⟨.bxor,0x8000000200000002,⟨65536,0x8000000200000002,0⟩⟩]
  accesses := [.rmw8 65536,.rmw8 65536,.rmw8 65536,.rmw8 65536,.stack8 32768]
  instructions := 5
  rip := 0x1234
  rsp := 32776
  registersCorrect := true
  flagsExceptAF := 0x646
  af := af
  bytes := [some 0x5a,some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0xa5]
  codeUnchanged := true }

/-- Literal AND/OR/OR/XOR/RET establishes the current-before chain, keeps an
unchanged OR event, and returns through the actual caller slot. All 32 AF
prefixes are checked, with the final flags coming from XOR rather than RET. -/
theorem routine_trace (first second third fourth last : Bool) :
    (run (stream first second third fourth last) 5 routine).map (routineView routine) =
      .ok (routineExpected fourth) := by
  cases first <;> cases second <;> cases third <;> cases fourth <;> cases last <;> rfl

/-- This is total correctness for every infinite AF stream. The semantic
claim has no instruction budget or favorable future-run hypothesis. -/
theorem routine_all_choices : AllExecutions routine (fun result =>
    result.events.length = 4 ∧ result.instructions = 5) := by
  intro choices
  let chosen := stream (choices 0) (choices 1) (choices 2) (choices 3) (choices 4)
  have agree : choices.Agree chosen 5 := by
    intro index bound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> simp [chosen, stream]
  have trace := routine_trace (choices 0) (choices 1) (choices 2) (choices 3) (choices 4)
  change (run chosen 5 routine).map (routineView routine) = _ at trace
  rw [←run_choices_congr (initial := routine) agree] at trace
  cases actual : run choices 5 routine with
  | error fault => simp [actual, Except.map] at trace
  | ok result =>
    have viewEq : routineView routine result = routineExpected (choices 3) := by
      simpa only [actual, Except.map, Except.ok.injEq] using trace
    exact ⟨result, run_sound actual,
      congrArg (fun view : RoutineView => view.events.length) viewEq,
      congrArg (fun view : RoutineView => view.instructions) viewEq⟩

/-- A first-step permission fault wins over unused choices, later stack
faults and extra runner fuel; no failed instruction retires. -/
theorem fault_before_stream_advance (choices : Choices) (fuel : Nat) :
    run choices (fuel + 1) (denyByte .readonly 7 routine) = .error (.writeDenied 65536) := by
  apply run_fault
  cases head : choices 0 <;> rfl

def missingStack : State := { routine with memory := { routine.memory with
  read := fun address => if address = 32775 then none else routine.memory.read address } }

theorem current_ret_fault (first second third fourth last : Bool) :
    run (stream first second third fourth last) 5 missingStack =
      .error (.inaccessibleStack 32775) := by
  cases first <;> cases second <;> cases third <;> cases fourth <;> cases last <;> rfl

def stackTargetRoutine (opcode : Byte) (mask : Word) : State :=
  let initial := entry [0xf0,0x48,opcode,0x37,0xc3] 0 mask
  { initial with
    registers := fun register => if register = .rdi then 32768 else initial.registers register
    memory := { initial.memory with
      writable := fun address => decide (32768 ≤ address.toNat ∧ address.toNat < 32776) } }

/-- Here the destination actually overlaps the return slot. Each RET must
read the changed current slot, rather than using the entry return address. -/
theorem actual_current_stack (first second : Bool) :
    ([(0x21,0xff),(0x09,1),(0x31,0x1000)] : List (Byte × Word)).map (fun (opcode,mask) =>
      (run (stream first second false false false) 2 (stackTargetRoutine opcode mask)).map (fun (result : Result) =>
        (result.state.rip, result.state.registers .rsp, result.events, result.accesses))) =
    [.ok (0x34,32776,[⟨.band,0xff,⟨32768,0x1234,0x34⟩⟩],[.rmw8 32768,.stack8 32768]),
     .ok (0x1235,32776,[⟨.bor,1,⟨32768,0x1234,0x1235⟩⟩],[.rmw8 32768,.stack8 32768]),
     .ok (0x234,32776,[⟨.bxor,0x1000,⟨32768,0x1234,0x234⟩⟩],[.rmw8 32768,.stack8 32768])] := by
  cases first <;> cases second <;> rfl

private def atAddress (address : Word) : State :=
  let initial := entry [0xf0,0x48,0x21,0x37] 0 0
  { initial with registers := fun register => if register = .rdi then address else initial.registers register }

theorem unsupported_addresses (af : Bool) :
    ([65537,0x0000800000000000,0xffffffffffffffff] : List Word).map
      (fun address => step af (atAddress address)) =
    [.error (.unsupportedAtomicAddress 65537),
     .error (.unsupportedAtomicAddress 0x0000800000000000),
     .error (.unsupportedAtomicAddress 0xffffffffffffffff)] := by
  cases af <;> rfl

end EDSL.Tests.LockedSet64

#audit_edsl
