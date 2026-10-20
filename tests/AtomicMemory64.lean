/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedLogical64.Machine
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicMemory64
open X86

/-- Independent finite-set membership contract, for every bit including 63.
It is applied to actual guarded operations, without an `eval` expected value. -/
theorem primitive_or_union {memory : Memory} {address mask : Word}
    {result : Memory × LogicalEvent64}
    (success : logicalRmwQWord .bor memory address mask = .ok result) (index : Fin 64) :
    result.2.event.after.toNat.testBit index = true ↔
      result.2.event.before.toNat.testBit index = true ∨ mask.toNat.testBit index = true := by
  have value := (logicalRmwQWord_sound _ _ _ _ _ success).2.2.2.2
  rw [value]
  simp [Sequential.LogicalOp.eval, BitVec.testBit_toNat]

theorem primitive_and_intersection {memory : Memory} {address mask : Word}
    {result : Memory × LogicalEvent64}
    (success : logicalRmwQWord .band memory address mask = .ok result) (index : Fin 64) :
    result.2.event.after.toNat.testBit index = true ↔
      result.2.event.before.toNat.testBit index = true ∧ mask.toNat.testBit index = true := by
  have value := (logicalRmwQWord_sound _ _ _ _ _ success).2.2.2.2
  rw [value]
  simp [Sequential.LogicalOp.eval, BitVec.testBit_toNat]

theorem primitive_xor_symmetric_difference {memory : Memory} {address mask : Word}
    {result : Memory × LogicalEvent64}
    (success : logicalRmwQWord .bxor memory address mask = .ok result) (index : Fin 64) :
    result.2.event.after.toNat.testBit index = true ↔
      (result.2.event.before.toNat.testBit index = true ∧ mask.toNat.testBit index = false) ∨
      (mask.toNat.testBit index = true ∧ result.2.event.before.toNat.testBit index = false) := by
  have value := (logicalRmwQWord_sound _ _ _ _ _ success).2.2.2.2
  rw [value]
  simp [Sequential.LogicalOp.eval, BitVec.testBit_toNat]
  cases result.2.event.before[index.val] <;> cases mask[index.val] <;> decide

theorem actual_step_union {initial final : State} {af : Bool} {label : LogicalEvent64}
    {accesses : List LockedLogical64.Access}
    (success : LockedLogical64.step af initial = .ok ⟨.atomic64 label final, accesses⟩) (index : Fin 64) :
    label.event.after.toNat.testBit index = true ↔
      label.event.before.toNat.testBit index = true ∨
        (initial.registers .rsi).toNat.testBit index = true := by
  rw [(LockedLogical64.step_atomic64_sound success).2.1.value]
  simp [BitVec.testBit_toNat]

/-- Literal old bytes and guards, independent of qword extraction/join code. -/
def data : Memory where
  read address := match address.toNat with
    | 32768 => some 0x00 | 32769 => some 0x20
    | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0
    | 65535 => some 0x5a
    | 65536 => some 0x01 | 65537 => some 0x23 | 65538 => some 0x45 | 65539 => some 0x67
    | 65540 => some 0x89 | 65541 => some 0xab | 65542 => some 0xcd | 65543 => some 0x01
    | 65544 => some 0xa5
    | _ => none
  executable := fun _ => false
  writable := fun address => decide (65536 ≤ address.toNat ∧ address.toNat < 65544)

def exactBytes : List Byte := [0xf0, 0x48, 0x09, 0x37, 0xc3]

def entry (mask : Word := 0x8020044080201010) (code : List Byte := exactBytes) : State where
  registers register := match register with
    | .rdi => 65536 | .rsi => mask | .rsp => 32768
    | .rax => 0xdeadbeef76543210
    | _ => 0x13579bdf2468ace0
  rip := 4096
  flags := 0xed7
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else data.read address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
    writable := data.writable }

def registers : List Register :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

structure AtomicView where
  label : LogicalEvent64
  accesses : List LockedLogical64.Access
  bytes : List (Option Byte)
  gprsPreserved : Bool
  rip : Word
  definedAndOtherFlags : Word
  af : Bool
  codeExecutable : Bool
  highWritable : Bool
  outsideWritable : Bool
  deriving DecidableEq, Repr

def observe (af : Bool) (initial : State) : Except Error AtomicView := do
  let observation ← LockedLogical64.step af initial
  match observation.result with
  | .atomic64 label final =>
    return ⟨label, observation.accesses,
      [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map final.memory.read,
      registers.all (fun register => final.registers register == initial.registers register),
      final.rip, final.flags &&& ~~~(0x10 : Word), final.flags.getLsbD 4,
      final.memory.executable 4099, final.memory.writable 65543, final.memory.writable 65544⟩
  | .returned _ => throw .unexpectedReturn

/-- Every byte changes, bit63 is set, low-byte parity is even and CF/OF clear.
Both guards and every GPR are observed after actual fetch + execution. -/
example (af : Bool) : observe af (entry) = .ok {
    label := ⟨.bor, 0x8020044080201010, ⟨65536, 0x01cdab8967452301, 0x81edafc9e7653311⟩⟩
    accesses := [.rmw8 65536]
    bytes := [some 0x5a, some 0x11, some 0x33, some 0x65, some 0xe7, some 0xc9,
      some 0xaf, some 0xed, some 0x81, some 0xa5]
    gprsPreserved := true
    rip := 4100
    definedAndOtherFlags := 0x686
    af := af
    codeExecutable := true
    highWritable := true
    outsideWritable := false } := by cases af <;> rfl

/-- Literal input byte vectors distinguish full64 ZF from low32 ZF, sign at
bit63, zero, and both parities. The flag oracle does not call flag helpers. -/
def statusView (af : Bool) (oldBytes : List Byte) (mask : Word) : Except Error (Word × Word × Bool) := do
  let initial := { entry mask with memory := { (entry mask).memory with
    read := fun address => if 65536 ≤ address.toNat ∧ address.toNat < 65544
      then oldBytes[address.toNat - 65536]? else (entry mask).memory.read address } }
  let observation ← LockedLogical64.step af initial
  match observation.result with
  | .atomic64 label final =>
    return (label.event.after, final.flags &&& ~~~(0x10 : Word), final.flags.getLsbD 4)
  | .returned _ => throw .unexpectedReturn

example (af : Bool) :
    (statusView af [0,0,0,0,1,0,0,0] 0,
      statusView af [0,0,0,0,0,0,0,0] 0x8000000000000000,
      statusView af [0,0,0,0,0,0,0,0] 0,
      statusView af [1,0,0,0,0,0,0,0] 2,
      statusView af [1,0,0,0,0,0,0,0] 0) =
    (.ok (0x100000000,0x606,af), .ok (0x8000000000000000,0x686,af),
      .ok (0,0x646,af), .ok (3,0x606,af), .ok (1,0x602,af)) := by cases af <;> rfl

-- The same primitive's AND/XOR operations also retain the upper 32 bits.
example : ((logicalRmwQWord .band data 65536 0xff000000000000ff).map (fun result =>
    (result.2, [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map result.1.read))) =
    .ok (⟨.band, 0xff000000000000ff, ⟨65536,0x01cdab8967452301,0x0100000000000001⟩⟩,
      [some 0x5a,some 1,some 0,some 0,some 0,some 0,some 0,some 0,some 1,some 0xa5]) := by rfl
example : (logicalRmwQWord .bxor data 65536 0x81cdab8967452301).map (fun result => result.2) =
    .ok ⟨.bxor,0x81cdab8967452301,⟨65536,0x01cdab8967452301,0x8000000000000000⟩⟩ := by rfl

/-- A second execution reads the first update and its own current RSI; no
entry-time snapshot, previous operand or low-half value is sufficient. -/
def consecutiveView (af : Bool) : Except Error (LogicalEvent64 × LogicalEvent64) := do
  let first ← LockedLogical64.step af (entry 0x8000000000000000)
  match first.result with
  | .atomic64 firstLabel middle =>
    let second ← LockedLogical64.step (!af) { middle with
      rip := 4096
      registers := fun register => if register = .rsi then 0x200000000 else middle.registers register }
    match second.result with
    | .atomic64 secondLabel _ => return (firstLabel, secondLabel)
    | .returned _ => throw .unexpectedReturn
  | .returned _ => throw .unexpectedReturn

example (af : Bool) : consecutiveView af = .ok
    (⟨.bor,0x8000000000000000,⟨65536,0x01cdab8967452301,0x81cdab8967452301⟩⟩,
      ⟨.bor,0x200000000,⟨65536,0x81cdab8967452301,0x81cdab8b67452301⟩⟩) := by cases af <;> rfl

/-- After the RMW, RET must fetch the preserved c3 and read the real stack.
A different current RSP points to different return bytes, preventing an
implementation from using a captured caller slot or the RMW destination. -/
def returnView (af : Bool) (moveStack : Bool) : Except Error
    (Word × Word × Word × Word × Bool × List LockedLogical64.Access × Except Error Word) := do
  let first ← LockedLogical64.step af (entry)
  let state := first.result.state
  let current := if moveStack then { state with
    registers := fun register => if register = .rsp then 32784 else state.registers register
    memory := { state.memory with
      read := fun address =>
        if address = 32784 then some 0x34 else if address = 32785 then some 0x12
        else if 32786 ≤ address.toNat ∧ address.toNat < 32792 then some 0
        else state.memory.read address } } else state
  let last ← LockedLogical64.step (!af) current
  match last.result with
  | .returned final => return (final.rip, final.registers .rsp, final.registers .rax,
      final.flags &&& ~~~(0x10 : Word), final.flags.getLsbD 4,
      last.accesses, loadQWord final.memory 65536)
  | .atomic64 _ _ => throw .unexpectedReturn

example (af : Bool) : returnView af false =
    .ok (8192,32776,0xdeadbeef76543210,0x686,af,[.stack8 32768],.ok 0x81edafc9e7653311) := by
  cases af <;> rfl
example (af : Bool) : returnView af true =
    .ok (0x1234,32792,0xdeadbeef76543210,0x686,af,[.stack8 32784],.ok 0x81edafc9e7653311) := by
  cases af <;> rfl

-- Read-only no-change operations remain rejected, including the eighth byte.
example : (observe false (entry 0)).map (fun view => (view.label,view.accesses,view.bytes)) =
    .ok (⟨.bor,0,⟨65536,0x01cdab8967452301,0x01cdab8967452301⟩⟩,[.rmw8 65536],
      [some 0x5a,some 1,some 0x23,some 0x45,some 0x67,some 0x89,
        some 0xab,some 0xcd,some 1,some 0xa5]) := by rfl

/-- Every operand byte is checked; upper-half failures are not DWORD successes. -/
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun denied => (LockedLogical64.step false { entry 0 with memory := { (entry 0).memory with
      writable := fun address => address != denied } }).map (fun _ => true)) =
    List.replicate 8 (.error (.writeDenied 65536)) := by rfl
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun missing => (LockedLogical64.step true { entry with memory := { (entry).memory with
      read := fun address => if address = missing then none else (entry).memory.read address } }).map
      (fun _ => true)) = List.replicate 8 (.error (.writeDenied 65536)) := by rfl
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun missing => loadQWord { data with read := fun address =>
      if address = missing then none else data.read address } 65536) =
    [.error (.inaccessibleData 65536),.error (.inaccessibleData 65537),
      .error (.inaccessibleData 65538),.error (.inaccessibleData 65539),
      .error (.inaccessibleData 65540),.error (.inaccessibleData 65541),
      .error (.inaccessibleData 65542),.error (.inaccessibleData 65543)] := by rfl

-- The fixed-code gate covers all eight bytes even when full R+W is available.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun executable => (LockedLogical64.step false { entry with memory := { (entry).memory with
      executable := fun address => (entry).memory.executable address || address == executable } }).map
      (fun _ => true)) = List.replicate 8 (.error (.writeDenied 65536)) := by rfl

def accessible : Memory where
  read := fun _ => some 0xa5
  executable := fun _ => false
  writable := fun _ => true

example : ([65537,65540,65543,0x800000000000,0x7fffffffffff,
    0xfffffffffffffffa,0xffffffffffffffff] : List Word).map
    (fun address => (logicalRmwQWord .bor accessible address 0).map (fun _ => true)) =
    [.error (.unsupportedAtomicAddress 65537),.error (.unsupportedAtomicAddress 65540),
      .error (.unsupportedAtomicAddress 65543),.error (.unsupportedAtomicAddress 0x800000000000),
      .error (.unsupportedAtomicAddress 0x7fffffffffff),
      .error (.unsupportedAtomicAddress 0xfffffffffffffffa),
      .error (.unsupportedAtomicAddress 0xffffffffffffffff)] := by rfl
example : (logicalRmwQWord .bor accessible 0xfffffffffffffff8 0).map (fun result => result.2) =
    .ok ⟨.bor,0,⟨0xfffffffffffffff8,0xa5a5a5a5a5a5a5a5,0xa5a5a5a5a5a5a5a5⟩⟩ := by rfl
example : atomicAddressable64 0x7ffffffffff8 = true ∧
    atomicAddressable64 0xffff800000000000 = true := by decide

-- Reject alternate widths/directions/register destinations and extra prefixes.
example : ([[0x48,0x09,0x37], [0xf0,0x09,0x37], [0xf0,0x40,0x09,0x37],
    [0xf0,0x48,0x09,0xf7], [0xf0,0x48,0x0b,0x37], [0xf0,0x48,0x09,0x36],
    [0x66,0xf0,0x48,0x09,0x37], [0x67,0xf0,0x48,0x09,0x37],
    [0x2e,0xf0,0x48,0x09,0x37], [0xf0,0x66,0x48,0x09,0x37],
    [0xf0,0x67,0x48,0x09,0x37], [0xf0,0xf0,0x48,0x09,0x37],
    [0x48,0xf0,0x48,0x09,0x37], [0xf0,0x48,0x48,0x09,0x37],
    [0xf0,0x48,0x81,0x0f,1,0,0,0], [0xf0,0x48,0x0f,0xb1,0x37],
    [0xf0,0x48,0x21,0x37], [0xf0,0x48,0x31,0x37]] : List (List Byte)).map
    (fun code => LockedLogical64.decodeAt (entry 0 code)) =
    List.replicate 18 (.error .unsupportedEncoding) := by rfl

example : ([[],[0xf0],[0xf0,0x48],[0xf0,0x48,0x09]] : List (List Byte)).map
    (fun code => LockedLogical64.decodeAt (entry 0 code)) =
    [.error (.inaccessibleInstruction 4096),.error (.inaccessibleInstruction 4097),
      .error (.inaccessibleInstruction 4098),.error (.inaccessibleInstruction 4099)] := by rfl

example : LockedLogical64.decodeAt { entry with memory := { (entry).memory with
    executable := fun address => address != 4099 } } =
    .error (.inaccessibleInstruction 4099) := by rfl

/-- The wrapped bytes are deliberately mapped; successful byte fetches alone
must not permit an instruction window to wrap the 64-bit address space. -/
def atAddress (pc : Word) (code : List Byte) : State :=
  { entry with rip := pc, memory := {
    read := fun query => code[(query - pc).toNat]?
    executable := fun _ => true
    writable := fun _ => false } }

example : LockedLogical64.decodeAt (atAddress 0xfffffffffffffffd [0xf0,0x48,0x09,0x37]) =
    .error (.inaccessibleInstruction 0xfffffffffffffffd) := by rfl
example : LockedLogical64.decodeAt (atAddress 0x7ffffffffffd [0xf0,0x48,0x09,0x37]) =
    .error (.inaccessibleInstruction 0x800000000000) := by rfl
example : LockedLogical64.decodeAt (atAddress 0xffffffffffffffff [0xc3]) = .ok .ret := by rfl
example : LockedLogical64.decodeAt (entry 0 [0xc3]) = .ok .ret := by rfl

-- RET's eighth-byte fault retains STACK provenance at the actual current RSP.
example : (LockedLogical64.step true { entry 0 [0xc3] with memory := { (entry 0 [0xc3]).memory with
    read := fun address => if address = 32775 then none else (entry 0 [0xc3]).memory.read address } }).map
    (fun _ => true) = .error (.inaccessibleStack 32775) := by rfl

end EDSL.Tests.AtomicMemory64

#audit_edsl
