/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.OS.TSO.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialMoves64
open X86

def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

/-- Distinct high halves and set bit31 distinguish full copies from either
zero/sign extension, wrong-bank selection, and reversed direction. -/
def registerInput : Register → Word
  | .rax => 0x1111111180000001 | .rcx => 0x2222222280000002
  | .rdx => 0x3333333380000003 | .rbx => 0x4444444480000004
  | .rsp => 0x5555555580000005 | .rbp => 0x6666666680000006
  | .rsi => 0x7777777780000007 | .rdi => 0x8888888880000008
  | .r8 => 0x9999999980000009 | .r9 => 0xaaaaaaaa8000000a
  | .r10 => 0xbbbbbbbb8000000b | .r11 => 0xcccccccc8000000c
  | .r12 => 0xdddddddd8000000d | .r13 => 0xeeeeeeee8000000e
  | .r14 => 0xfedcba988000000f | .r15 => 0xf123456780000010

def emptyMemory : Memory where
  read := fun _ => none
  executable := fun _ => false

/-- The instruction window is executable; all other memory queries come from
the supplied memory. Register operands require no readable data or stack. -/
def entry (code : List Byte) (registers : Register → Word := registerInput)
    (flags : Word := 0xfedcba9876543210) (data : Memory := emptyMemory) : State where
  registers := registers
  flags := flags
  rip := 4096
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else data.read address
    executable := fun address =>
      if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then true
      else data.executable address
    writable := data.writable }

def nextView (af : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

/-- These literal register encodings also occur in the native fixture. They
are independent operand vectors, with no second REX/ModRM decoder. -/
theorem bank_bits_and_directions :
    ([[0x48,0x89,0xd8], [0x49,0x89,0xd8], [0x4a,0x89,0xd8], [0x4b,0x89,0xd8],
      [0x4c,0x89,0xd8], [0x4d,0x89,0xd8], [0x4e,0x89,0xd8], [0x4f,0x89,0xd8],
      [0x48,0x8b,0xd8], [0x49,0x8b,0xd8], [0x4a,0x8b,0xd8], [0x4b,0x8b,0xd8],
      [0x4c,0x8b,0xd8], [0x4d,0x8b,0xd8], [0x4e,0x8b,0xd8], [0x4f,0x8b,0xd8]] :
      List (List Byte)).map (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.movReg64 .rax .rbx), .ok (.movReg64 .r8 .rbx),
      .ok (.movReg64 .rax .rbx), .ok (.movReg64 .r8 .rbx),
      .ok (.movReg64 .rax .r11), .ok (.movReg64 .r8 .r11),
      .ok (.movReg64 .rax .r11), .ok (.movReg64 .r8 .r11),
      .ok (.movReg64 .rbx .rax), .ok (.movReg64 .rbx .r8),
      .ok (.movReg64 .rbx .rax), .ok (.movReg64 .rbx .r8),
      .ok (.movReg64 .r11 .rax), .ok (.movReg64 .r11 .r8),
      .ok (.movReg64 .r11 .rax), .ok (.movReg64 .r11 .r8)] := by rfl

/-- Both independent bank bits affect actual execution; X has no register-mode
effect. Reusing the same ModRM byte exposes an accidental direction swap. -/
theorem bank_execution (af : Bool) :
    ([([0x48,0x89,0xd8], .rax), ([0x49,0x89,0xd8], .r8),
      ([0x4a,0x89,0xd8], .rax), ([0x4b,0x89,0xd8], .r8),
      ([0x4c,0x89,0xd8], .rax), ([0x4d,0x89,0xd8], .r8),
      ([0x4e,0x89,0xd8], .rax), ([0x4f,0x89,0xd8], .r8),
      ([0x48,0x8b,0xd8], .rbx), ([0x49,0x8b,0xd8], .rbx),
      ([0x4a,0x8b,0xd8], .rbx), ([0x4b,0x8b,0xd8], .rbx),
      ([0x4c,0x8b,0xd8], .r11), ([0x4d,0x8b,0xd8], .r11),
      ([0x4e,0x8b,0xd8], .r11), ([0x4f,0x8b,0xd8], .r11)] :
      List (List Byte × Register)).map (fun (bytes, destination) =>
        nextView af (entry bytes) (fun s _ => s.registers destination)) =
    [.ok 0x4444444480000004, .ok 0x4444444480000004,
      .ok 0x4444444480000004, .ok 0x4444444480000004,
      .ok 0xcccccccc8000000c, .ok 0xcccccccc8000000c,
      .ok 0xcccccccc8000000c, .ok 0xcccccccc8000000c,
      .ok 0x1111111180000001, .ok 0x9999999980000009,
      .ok 0x1111111180000001, .ok 0x9999999980000009,
      .ok 0x1111111180000001, .ok 0x9999999980000009,
      .ok 0x1111111180000001, .ok 0x9999999980000009] := by rfl

/-- The assembler89 operand contracts cover all16 destinations AND sources,
including RSP, with each low/high bank pairing represented. -/
theorem all_89_operands (af : Bool) :
    ([([0x48,0x89,0xc8], .rax), ([0x4c,0x89,0xd1], .rcx),
      ([0x48,0x89,0xda], .rdx), ([0x4c,0x89,0xe3], .rbx),
      ([0x48,0x89,0xec], .rsp), ([0x4c,0x89,0xf5], .rbp),
      ([0x48,0x89,0xfe], .rsi), ([0x4c,0x89,0xc7], .rdi),
      ([0x4d,0x89,0xc8], .r8), ([0x49,0x89,0xd1], .r9),
      ([0x4d,0x89,0xda], .r10), ([0x49,0x89,0xe3], .r11),
      ([0x4d,0x89,0xec], .r12), ([0x49,0x89,0xf5], .r13),
      ([0x4d,0x89,0xfe], .r14), ([0x49,0x89,0xc7], .r15)] :
      List (List Byte × Register)).map (fun (bytes, destination) =>
        nextView af (entry bytes) (fun s _ => s.registers destination)) =
    [.ok 0x2222222280000002, .ok 0xbbbbbbbb8000000b,
      .ok 0x4444444480000004, .ok 0xdddddddd8000000d,
      .ok 0x6666666680000006, .ok 0xfedcba988000000f,
      .ok 0x8888888880000008, .ok 0x9999999980000009,
      .ok 0xaaaaaaaa8000000a, .ok 0x3333333380000003,
      .ok 0xcccccccc8000000c, .ok 0x5555555580000005,
      .ok 0xeeeeeeee8000000e, .ok 0x7777777780000007,
      .ok 0xf123456780000010, .ok 0x1111111180000001] := by rfl

/-- The alternate8b direction independently covers all16 sources and
destinations. In particular, extending r/m selects the SOURCE here. -/
theorem all_8b_operands (af : Bool) :
    ([([0x49,0x8b,0xc7], .rax), ([0x48,0x8b,0xc8], .rcx),
      ([0x49,0x8b,0xd1], .rdx), ([0x48,0x8b,0xda], .rbx),
      ([0x49,0x8b,0xe3], .rsp), ([0x48,0x8b,0xec], .rbp),
      ([0x49,0x8b,0xf5], .rsi), ([0x48,0x8b,0xfe], .rdi),
      ([0x4c,0x8b,0xc7], .r8), ([0x4d,0x8b,0xc8], .r9),
      ([0x4c,0x8b,0xd1], .r10), ([0x4d,0x8b,0xda], .r11),
      ([0x4c,0x8b,0xe3], .r12), ([0x4d,0x8b,0xec], .r13),
      ([0x4c,0x8b,0xf5], .r14), ([0x4d,0x8b,0xfe], .r15)] :
      List (List Byte × Register)).map (fun (bytes, destination) =>
        nextView af (entry bytes) (fun s _ => s.registers destination)) =
    [.ok 0xf123456780000010, .ok 0x1111111180000001,
      .ok 0xaaaaaaaa8000000a, .ok 0x3333333380000003,
      .ok 0xcccccccc8000000c, .ok 0x5555555580000005,
      .ok 0xeeeeeeee8000000e, .ok 0x7777777780000007,
      .ok 0x8888888880000008, .ok 0x9999999980000009,
      .ok 0x2222222280000002, .ok 0xbbbbbbbb8000000b,
      .ok 0x4444444480000004, .ok 0xdddddddd8000000d,
      .ok 0x6666666680000006, .ok 0xfedcba988000000f] := by rfl

set_option maxRecDepth 4096 in
/-- An arbitrary PRE source survives, every other register survives, and the
entire memory (read function and BOTH permission functions) and flags survive.
The empty read list and .next result exclude reads and locked/atomic effects. -/
theorem complete_context (registers : Register → Word) (flags : Word) (data : Memory)
    (af : Bool) : nextView af (entry [0x4f,0x89,0xd8] registers flags data)
      (fun s reads => (allRegisters.map s.registers, s.memory, s.flags, s.rip, reads)) =
    .ok ([registers .rax, registers .rcx, registers .rdx, registers .rbx,
      registers .rsp, registers .rbp, registers .rsi, registers .rdi,
      registers .r11, registers .r9, registers .r10, registers .r11,
      registers .r12, registers .r13, registers .r14, registers .r15],
      (entry [0x4f,0x89,0xd8] registers flags data).memory, flags, 4099, []) := by
  have decoded : Sequential.decodeAt (entry [0x4f,0x89,0xd8] registers flags data) =
      .ok (.movReg64 .r8 .r11) := by
    simp [Sequential.decodeAt, X86.decodeAt, Sequential.decodeNewAt, Sequential.decodeREXWAt, entry,
      fetchByte, canonical, Sequential.rexWPrefix, Sequential.rexModRMReg,
      Sequential.rexModRMRM, Sequential.highRegister]
  unfold nextView
  rw [Sequential.step_eq_execute af decoded]
  rfl

/-- Full64 self-copy is identity for every GPR, using both opcode directions;
the nonzero high halves detect accidental MOV32 zero extension. -/
theorem all_self_copies (af : Bool) :
    ([[0x48,0x89,0xc0], [0x48,0x8b,0xc9], [0x48,0x89,0xd2], [0x48,0x8b,0xdb],
      [0x48,0x89,0xe4], [0x48,0x8b,0xed], [0x48,0x89,0xf6], [0x48,0x8b,0xff],
      [0x4d,0x89,0xc0], [0x4d,0x8b,0xc9], [0x4d,0x89,0xd2], [0x4d,0x8b,0xdb],
      [0x4d,0x89,0xe4], [0x4d,0x8b,0xed], [0x4d,0x89,0xf6], [0x4d,0x8b,0xff]] :
      List (List Byte)).map (fun bytes => nextView af (entry bytes)
        (fun s reads => (allRegisters.map s.registers, s.flags, s.rip, reads))) =
    List.replicate 16 (.ok (allRegisters.map registerInput, 0xfedcba9876543210, 4099, [])) := by rfl

theorem self64_vs_self32 (af : Bool) :
    (nextView af (entry [0x48,0x89,0xe4]) (fun s reads => (s.registers .rsp, s.rip, reads)),
      nextView af (entry [0x89,0xe4]) (fun s reads => (s.registers .rsp, s.rip, reads))) =
    (.ok (0x5555555580000005, 4099, []), .ok (0x80000005, 4098, [])) := by rfl

/-- W=0 REX is outside this profile even though unprefixed MOV32 exists. -/
theorem w0_rejected :
    ([[0x40,0x89,0xd8], [0x41,0x8b,0xd8], [0x42,0x89,0xd8], [0x43,0x8b,0xd8],
      [0x44,0x89,0xd8], [0x45,0x8b,0xd8], [0x46,0x89,0xd8], [0x47,0x8b,0xd8]] :
      List (List Byte)).map (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.unsupportedOpcode 0x40), .error (.unsupportedOpcode 0x41),
      .error (.unsupportedOpcode 0x42), .error (.unsupportedOpcode 0x43),
      .error (.unsupportedOpcode 0x44), .error (.unsupportedOpcode 0x45),
      .error (.unsupportedOpcode 0x46), .error (.unsupportedOpcode 0x47)] := by rfl

/-- Repeated REX, extra legacy prefixes and displacements reject. Supported
base and extended-SIB operands retain their full64 memory interpretation. -/
theorem prefixes_displacements_and_memory_decoding :
    ([[0x48,0x48,0x89,0xd8], [0x49,0x48,0x8b,0xd8], [0x4f,0x4f,0x89,0xd8],
      [0x48,0x66,0x89,0xd8], [0x48,0xf0,0x89,0xd8], [0xf0,0x48,0x89,0xd8],
      [0x48,0x89,0x18], [0x49,0x8b,0x0b], [0x4f,0x89,0x1c,0x24],
      [0x48,0x8b,0x5b,0], [0x48,0x89,0x9b,0,0,0,0],
      [0x48,0x8b,0x1d,0,0,0,0]] : List (List Byte)).map
        (fun bytes => Sequential.decodeAt (entry bytes)) =
    List.replicate 6 (.error .unsupportedEncoding) ++
      [.ok (.storeMem64 (.base .rax) .rbx), .ok (.loadMem64 .rcx (.base .r11)),
        .ok (.storeMem64 (.indexed .r12 .r12 ⟨0, by decide⟩) .r11)] ++
      List.replicate 3 (.error .unsupportedEncoding) := by rfl

theorem leading_legacy_prefixes_rejected :
    ([[0x66,0x48,0x89,0xd8], [0x67,0x48,0x8b,0xd8],
      [0xf2,0x48,0x89,0xd8], [0xf3,0x4f,0x8b,0xd8]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.unsupportedOpcode 0x66), .error (.unsupportedOpcode 0x67),
      .error (.unsupportedOpcode 0xf2), .error (.unsupportedOpcode 0xf3)] := by rfl

/-- The earlier full64 families retain exact48 rather than acquiring MOV's
new bank extensions or ignored X. Cross-product construction only supplies
test inputs; expected results contain no opcode/REX/ModRM calculations. -/
theorem other_families_still_exact48 :
    ([0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] : List Byte).flatMap
      (fun rexByte => ([[0x85,0xd8], [0x39,0xd8], [0x83,0xc0,1],
        [0xff,0xc0], [0xff,0xc8]] : List (List Byte)).map
          (fun suffix => Sequential.decodeAt (entry (rexByte :: suffix)))) =
    List.replicate 35 (.error .unsupportedEncoding) := by rfl

theorem exact48_families_retained :
    ([[0x48,0x85,0xd8], [0x48,0x39,0xd8], [0x48,0x83,0xc0,1],
      [0x48,0xff,0xc0], [0x48,0xff,0xc8]] : List (List Byte)).map
        (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.test64 .rax .rbx), .ok (.cmp64 .rax .rbx), .ok (.addImm64 .rax 1),
      .ok (.inc64 .rax), .ok (.dec64 .rax)] := by rfl

theorem truncated_fetch (af : Bool) :
    ([[0x48], [0x4f], [0x48,0x89], [0x4f,0x8b]] : List (List Byte)).map
      (fun bytes => (Sequential.step af (entry bytes)).map (fun _ => ())) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4097),
      .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4098)] := by rfl

/-- The actual third byte must be BOTH readable and executable. -/
theorem third_byte_execute_permission (af : Bool) :
    (Sequential.step af { entry [0x4f,0x8b,0xd8] with
      memory := { (entry [0x4f,0x8b,0xd8]).memory with
        executable := fun address => decide (address = 4096 ∨ address = 4097) } }).map
          (fun _ => ()) = .error (.inaccessibleInstruction 4098) := by rfl

theorem third_byte_read_permission (af : Bool) :
    (Sequential.step af { entry [0x49,0x89,0xd8] with
      memory := { (entry [0x49,0x89,0xd8]).memory with
        read := fun address => if address = 4098 then none
          else (entry [0x49,0x89,0xd8]).memory.read address } }).map
          (fun _ => ()) = .error (.inaccessibleInstruction 4098) := by rfl

/-- Real discovery and graph checking admit the new register operations,
partitioning the bytes at three-byte boundaries before the terminal RET. -/
theorem cfg_admission :
    (Sequential.CFG.analyze [0x4c,0x89,0xd8,0x49,0x8b,0xc7,0x4f,0x8b,0xd8,0xc3]).map
      (fun graph => graph.nodes.map (fun node =>
        (node.offset, node.instruction, node.instruction.length))) =
    .ok [(0, .movReg64 .rax .r11, 3), (3, .movReg64 .rax .r15, 3),
      (6, .movReg64 .r11 .r8, 3), (9, .legacy .ret, 1)] := by rfl

def tsoEntry (bytes : List Byte) : OS.TSO.State :=
  ⟨(entry bytes).memory, [⟨OS.Threads.Context.ofState (entry bytes), false, []⟩]⟩

/-- The real TSO issue path still rejects MOV64: sequential admission must
not change legacy decoding or concurrent FIFO/atomicity contracts. -/
theorem tso_issue_rejection :
    ([[0x48,0x89,0xd8], [0x49,0x89,0xd8], [0x4a,0x8b,0xd8], [0x4b,0x8b,0xd8],
      [0x4c,0x89,0xd8], [0x4d,0x89,0xd8], [0x4e,0x8b,0xd8], [0x4f,0x8b,0xd8]] :
      List (List Byte)).map (fun bytes =>
        (OS.TSO.step (tsoEntry bytes) (.issue 0)).map (fun _ => ())) =
    [.error (.machine (.unsupportedOpcode 0x48)), .error (.machine (.unsupportedOpcode 0x49)),
      .error (.machine (.unsupportedOpcode 0x4a)), .error (.machine (.unsupportedOpcode 0x4b)),
      .error (.machine (.unsupportedOpcode 0x4c)), .error (.machine (.unsupportedOpcode 0x4d)),
      .error (.machine (.unsupportedOpcode 0x4e)), .error (.machine (.unsupportedOpcode 0x4f))] := by rfl

end EDSL.Tests.SequentialMoves64

#audit_edsl
